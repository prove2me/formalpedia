-- Prove2me | solution 1 for NishtAbel2024.checked_solver_sound
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T03:16:06.005356+00:00
-- url     : https://prove2.me/submissions/9b6b4008-5f00-4312-a789-a5be2bd3d7de

import Definitions.Def_NishtAbel2024_CheckedConstraintSolver

namespace NishtAbel2024.RawSizeLtCheck

theorem usable_eq (p : Polarity) : usable p = Polarity.le p .pos := by
  cases p <;> rfl

theorem hasBound_sound {Ψ : SizeCtx} {i : SizeVar} (h : hasBound Ψ i = true) :
    ∃ a, SizeVarBound Ψ i a := by
  obtain ⟨d, hd, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, usable_eq] at h
  refine ⟨d.bound, d.pol, ?_, h.2⟩
  cases d with
  | mk v p a =>
    simp only at h
    rcases h with ⟨rfl, _⟩
    exact hd

theorem hasBoundEq_sound {Ψ : SizeCtx} {i : SizeVar} {a : SizeExp}
    (h : hasBoundEq Ψ i a = true) : SizeVarBound Ψ i a := by
  obtain ⟨d, hd, h⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, usable_eq] at h
  refine ⟨d.pol, ?_, h.1.2⟩
  cases d with
  | mk v p b =>
    simp only at h
    rcases h with ⟨⟨rfl, _⟩, rfl⟩
    exact hd

theorem checkWf_sound {Ψ : SizeCtx} {a : SizeExp} (h : checkWf Ψ a = true) :
    SizeWf Ψ a := by
  cases a with
  | inf n => trivial
  | meet a =>
    intro sv hm
    exact hasBound_sound ((List.all_eq_true.mp h) sv hm)

theorem direct_sound {Ψ : SizeCtx} {a b : SizeExp} (h : direct Ψ a b = true) :
    SizeLt Ψ a b := by
  cases a with
  | inf n =>
    cases b with
    | inf m => exact .inf_lt_inf (of_decide_eq_true h)
    | meet bm => simp [direct] at h
  | meet am =>
    cases am with
    | mk av ats =>
      cases av with
      | mk i n =>
        cases ats with
        | cons x xs => simp [direct] at h
        | nil =>
          cases b with
          | inf m =>
            exact SizeLt.var_lt_inf (hasBoundEq_sound h)
          | meet bm =>
            cases bm with
            | mk bv bts =>
              cases bv with
              | mk j m =>
                cases bts with
                | cons x xs => simp [direct] at h
                | nil =>
                  simp only [direct, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
                  rcases h with ⟨⟨rfl, hn⟩, hb⟩
                  obtain ⟨a, ha⟩ := hasBound_sound hb
                  exact SizeLt.var_lt_var hn ha

theorem checkSizeLt_sound {fuel : Nat} {Ψ : SizeCtx} {a b : SizeExp}
    (h : checkSizeLt fuel Ψ a b = true) : SizeLt Ψ a b := by
  induction fuel generalizing a b with
  | zero => simp [checkSizeLt] at h
  | succ fuel ih =>
    simp only [checkSizeLt, Bool.or_eq_true] at h
    rcases h with (((hd | hr) | hl) | hs)
    · exact direct_sound hd
    · cases b with
      | inf n => simp at hr
      | meet bm =>
        by_cases he : bm.tail.isEmpty
        · simp [he] at hr
        · simp [he] at hr
          apply SizeLt.lt_meet_right
          intro sv hm
          exact ih (hr sv hm)
    · cases a with
      | inf n => simp at hl
      | meet am =>
        by_cases he : am.tail.isEmpty
        · simp [he] at hl
        · simp [he] at hl
          obtain ⟨hwf, sv, hm, hc⟩ := hl
          exact SizeLt.meet_lt_left (checkWf_sound hwf) hm (ih hc)
    · cases a with
      | inf n => simp at hs
      | meet am =>
        cases am with
        | mk sv tail =>
          cases tail with
          | cons x xs => simp at hs
          | nil =>
            obtain ⟨d, hd, hc⟩ := List.any_eq_true.mp hs
            simp only [Bool.and_eq_true, beq_iff_eq, usable_eq] at hc
            apply SizeLt.var_bound_step (a := d.bound)
            · refine ⟨d.pol, ?_, hc.1.2⟩
              cases d with
              | mk v p bound =>
                simp only at hc
                rcases hc with ⟨⟨rfl, _⟩, _⟩
                exact hd
            · exact ih hc.2

end NishtAbel2024.RawSizeLtCheck

namespace NishtAbel2024.CheckedConstraintSolver

theorem solver_outside_support (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar)
    (k : SizeVar) (hk : k ∉ support Ψ C T) :
    solveConstraintGraph Ψ C T k = .infty := by
  have hΨ : k ∉ Ψ.dom := by
    intro h
    exact hk (by simp [support, h])
  have hT : k ∉ T := by
    intro h
    exact hk (by simp [support, h])
  have hC : ∀ c ∈ C, k ∉ c.rhs.vars := by
    intro c hc hv
    apply hk
    simp only [support, List.mem_append, List.mem_flatMap]
    exact Or.inl (Or.inr ⟨c, hc, Or.inr hv⟩)
  have hfilter : (C.filter (fun c => c.rhs == .var k 0 &&
      c.lhs.vars.all (fun v => Ψ.dom.contains v))) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro c hc htest
    simp only [Bool.and_eq_true, beq_iff_eq] at htest
    apply hC c hc
    rw [htest.1]
    simp [SizeExp.var, SizeExp.vars, SizeMin.vars, SizeMin.single, SizeMin.toList]
  have hself : C.any (fun c => c.rel == .lt && c.lhs.vars.contains k &&
      c.rhs.vars.contains k) = false := by
    cases he : C.any (fun c => c.rel == .lt && c.lhs.vars.contains k &&
        c.rhs.vars.contains k) with
    | false => rfl
    | true =>
      obtain ⟨c, hc, ht⟩ := List.any_eq_true.mp he
      simp only [Bool.and_eq_true] at ht
      exact False.elim (hC c hc (List.contains_iff_mem.mp ht.2))
  have hΨb : Ψ.dom.contains k = false := by simpa using hΨ
  have hTb : T.contains k = false := by simpa using hT
  unfold solveConstraintGraph
  split
  · simp only [hΨb, Bool.false_eq_true, ↓reduceIte, hself, hfilter, List.map_nil,
      hTb, Bool.false_and, lubSizes]
  · simp [hΨ]

theorem constraintCheck_sound {fuel : Nat} {Ψ : SizeCtx} {φ : FlexSubst}
    {c : SizeConstraint} (h : constraintCheck fuel Ψ φ c = true) :
    match c.rel with
    | .lt => SizeLt Ψ (c.lhs.applyFlex φ) (c.rhs.applyFlex φ).boundNorm
    | .le => SizeLe Ψ (c.lhs.applyFlex φ) (c.rhs.applyFlex φ).boundNorm := by
  cases hr : c.rel with
  | lt => exact RawSizeLtCheck.checkSizeLt_sound (by simpa [constraintCheck, hr] using h)
  | le => exact RawSizeLtCheck.checkSizeLt_sound (by simpa [constraintCheck, hr, SizeLe] using h)

theorem certificate_sound {fuel : Nat} {Ψ : SizeCtx} {C : List SizeConstraint}
    {T : List SizeVar} (h : certificate fuel Ψ C T = true) :
    CoherentSubst Ψ C (solveConstraintGraph Ψ C T) := by
  have h' := h
  simp only [certificate, Bool.and_eq_true] at h'
  obtain ⟨⟨hrigid, hwf⟩, hconstraints⟩ := h'
  constructor
  · constructor
    · intro i hi
      have hval := (List.all_eq_true.mp hrigid) i hi
      exact (beq_iff_eq.mp hval)
    · intro k
      by_cases hk : k ∈ support Ψ C T
      · exact RawSizeLtCheck.checkWf_sound ((List.all_eq_true.mp hwf) k hk)
      · rw [solver_outside_support Ψ C T k hk]
        trivial
  · intro c hc
    exact constraintCheck_sound ((List.all_eq_true.mp hconstraints) c hc)

theorem checkedSolve_sound {fuel : Nat} {Ψ : SizeCtx} {C : List SizeConstraint}
    {T : List SizeVar} {φ : FlexSubst} (h : checkedSolve fuel Ψ C T = some φ) :
    CoherentSubst Ψ C φ := by
  unfold checkedSolve at h
  split at h
  · rename_i hcert
    cases h
    exact certificate_sound hcert
  · contradiction

end NishtAbel2024.CheckedConstraintSolver

open NishtAbel2024

theorem solution :
    ∀ (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) (φ : FlexSubst),
      CheckedConstraintSolver.checkedSolve fuel Ψ C T = some φ → CoherentSubst Ψ C φ := by
  intro fuel Ψ C T φ h
  exact CheckedConstraintSolver.checkedSolve_sound h
