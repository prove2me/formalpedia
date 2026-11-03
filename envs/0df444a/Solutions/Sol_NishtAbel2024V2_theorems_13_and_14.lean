-- Prove2me | solution 1 for NishtAbel2024V2.theorems_13_and_14
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:20:48.192814+00:00
-- url     : https://prove2.me/submissions/65515d66-8e3b-44cf-988b-c4e3bc342467

import Definitions.Def_NishtAbel2024V2_Syntax
import Definitions.Def_NishtAbel2024V2_Inference

namespace NishtAbel2024V2

/-! ## Part 1: Spine Self-Substitution, Elaboration, and Postchecked Algorithm 2 Soundness -/

mutual

theorem spine_subst_self_1314 (X : TyVar) (F : TypeExpr) :
    TypeExpr.substTyVar X (.atom (.var X)) F = F := by
  cases F with
  | atom K =>
    cases K with
    | var Y =>
      simp only [TypeExpr.substTyVar]
      split <;> simp_all
    | size _ | unit | prod | arr | all _ | ex _ => rfl
  | lam Y ι F =>
    simp only [TypeExpr.substTyVar]
    split
    · rfl
    · rw [spine_subst_self_1314 X F]
  | app F G =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_self_1314 X F, spine_subst_self_1314 X G]
  | mu a S =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_branches_self_1314 X S]
  | nu a R =>
    simp only [TypeExpr.substTyVar]
    rw [spine_subst_branches_self_1314 X R]
termination_by sizeOf F

theorem spine_subst_branches_self_1314 (X : TyVar) (S : List (Nat × TypeExpr)) :
    TypeExpr.substTyVarBranches X (.atom (.var X)) S = S := by
  cases S with
  | nil => rfl
  | cons p rest =>
    rcases p with ⟨name, body⟩
    simp only [TypeExpr.substTyVarBranches]
    rw [spine_subst_self_1314 X body, spine_subst_branches_self_1314 X rest]
termination_by sizeOf S

end

theorem spine_normApp_self_1314 (X : TyVar) (ι : SKind) (B : TypeExpr) :
    (TypeExpr.lam X ι B).normApp (.atom (.var X)) = B :=
  spine_subst_self_1314 X B

theorem inferPat_elaborates_1314 {Δ₀ : KindingCtx} {p p' : Pat} {A : TypeExpr}
    {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx}
    (h : InferPat Δ₀ p A Γ Δ Ψ p') : PatTyping Δ₀ Δ Γ p' A := by
  induction h with
  | var Δ₀ x _ => exact PatTyping.var Δ₀ x _
  | unit Δ₀ => exact PatTyping.unit Δ₀
  | pair _ _ _ _ ih₁ ih₂ => exact PatTyping.pair ih₁ ih₂
  | cons j hlookup _ _ _ _ _ ih =>
    apply PatTyping.cons j hlookup
    apply PatTyping.tyPack
    simpa [TypeExpr.existsSizeLt, spine_normApp_self_1314] using ih
  | tyPack _ _ ih => exact PatTyping.tyPack ih

theorem inferSpine_elaborates_1314 {Δ₀ : KindingCtx} {qs qs' : PatSpine} {A C : TypeExpr}
    {Γ : TermCtx} {Δ : List TyDecl} {Ψ : SizeCtx}
    (h : InferSpine Δ₀ qs A C Γ Δ Ψ qs') : SpineTyping Δ₀ Δ Γ A qs' C := by
  induction h with
  | nil Δ₀ A => exact SpineTyping.nil Δ₀ A
  | pat hp _ _ _ ih => exact SpineTyping.pat (inferPat_elaborates_1314 hp) ih
  | proj j hlookup _ _ _ _ _ ih =>
    apply SpineTyping.proj j hlookup
    apply SpineTyping.tyVar
    simpa [TypeExpr.forallSizeLt, spine_normApp_self_1314] using ih
  | tyApp _ _ ih => exact SpineTyping.tyVar ih

theorem postcheckedClauseRun_clauseCheck_1314 {sig : GlobalSig} {Ξannot : MutualBlock}
    {𝒢 : InvGraphFamily} {caller : FunName} {Ψ₁ : SizeCtx}
    {A' : TypeExpr} {qs : PatSpine} {t : Term} {D' : Clause}
    (run : PostcheckedAlgorithm2ClauseRun sig Ξannot 𝒢 caller Ψ₁ A' qs t D') :
    ClauseCheck ⟨sig, Ξannot, 𝒢, caller, Ψ₁⟩
      (KindingCtx.empty.extSizes Ψ₁) [] D' A' := by
  have hD' : D' = .mk run.qs' (run.t'.applyFlex (solveConstraintGraph (Ψ₁ ++ run.Ψ₂) run.Cs run.T)) :=
    run.callsConform.1
  rw [hD']
  exact ClauseCheck.mk
    (inferSpine_elaborates_1314 run.inferSpine)
    run.consistentExt
    (by simpa using run.postcheckedBody)

private theorem forall₂_mem_right_1314 {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β}
    (h : List.Forall₂ R xs ys) {y : β} (hy : y ∈ ys) : ∃ x ∈ xs, R x y := by
  induction h with
  | nil => cases hy
  | cons hxy hrest ih =>
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨_, List.Mem.head _, hxy⟩
    · rcases ih hy with ⟨x, hx, hRx⟩
      exact ⟨x, List.Mem.tail _ hx, hRx⟩

theorem postchecked_algorithm2_implies_typing_1314 {sig : GlobalSig} {Ξ Ξannot : MutualBlock}
    (hacc : PostcheckedAlgorithm2Accepts sig Ξ Ξannot) :
    MutualBlockTyping sig Ξannot := by
  rcases hacc with ⟨𝒢, hsct, harity, hdecls⟩
  refine ⟨𝒢, hsct, harity, ?_⟩
  intro decl' hdecl'
  rcases forall₂_mem_right_1314 hdecls hdecl' with
    ⟨_, _, _, _, _, hwf, hkind, hclauses⟩
  refine ⟨hwf, hkind, ?_⟩
  intro D' hD'
  rcases forall₂_mem_right_1314 hclauses hD' with ⟨_, _, _, _, _, ⟨run⟩⟩
  exact postcheckedClauseRun_clauseCheck_1314 run

/-! ## Part 2: Checked Constraint Solver Soundness -/

namespace CheckedConstraintSolver

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
  | lt => exact checkSizeLt_sound (by simpa [constraintCheck, hr] using h)
  | le => exact checkSizeLt_sound (by simpa [constraintCheck, hr, SizeLe] using h)

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
      · exact checkWf_sound ((List.all_eq_true.mp hwf) k hk)
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

end CheckedConstraintSolver

/-- Repaired Theorem 13 (Postchecked clause run typing soundness, pp. 56–57),
Theorem 14 (Soundness of the checked constraint solver, p. 58), and
Corollary (Target mutual-block typing of postchecked Algorithm 2, p. 59) in `NishtAbel2024V2`. -/
theorem theorems_13_and_14 :
    (∀ (sig : GlobalSig) (Ξannot : MutualBlock) (𝒢 : InvGraphFamily) (caller : FunName)
       (Ψ₁ : SizeCtx) (A' : TypeExpr) (qs : PatSpine) (t : Term) (D' : Clause),
      Nonempty (PostcheckedAlgorithm2ClauseRun sig Ξannot 𝒢 caller Ψ₁ A' qs t D') →
      ClauseCheck ⟨sig, Ξannot, 𝒢, caller, Ψ₁⟩ (KindingCtx.empty.extSizes Ψ₁) [] D' A') ∧
    (∀ (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) (φ : FlexSubst),
      CheckedConstraintSolver.checkedSolve fuel Ψ C T = some φ →
      CoherentSubst Ψ C φ) ∧
    (∀ (sig : GlobalSig) (Ξ Ξannot : MutualBlock),
      PostcheckedAlgorithm2Accepts sig Ξ Ξannot →
      MutualBlockTyping sig Ξannot) := by
  refine ⟨?_, ?_, ?_⟩
  · intro sig Ξannot 𝒢 caller Ψ₁ A' qs t D' ⟨run⟩
    exact postcheckedClauseRun_clauseCheck_1314 run
  · intro fuel Ψ C T φ h
    exact CheckedConstraintSolver.checkedSolve_sound h
  · intro sig Ξ Ξannot hacc
    exact postchecked_algorithm2_implies_typing_1314 hacc

end NishtAbel2024V2

open NishtAbel2024V2

theorem solution :
    (∀ (sig : GlobalSig) (Ξannot : MutualBlock) (𝒢 : InvGraphFamily) (caller : FunName)
       (Ψ₁ : SizeCtx) (A' : TypeExpr) (qs : PatSpine) (t : Term) (D' : Clause),
      Nonempty (PostcheckedAlgorithm2ClauseRun sig Ξannot 𝒢 caller Ψ₁ A' qs t D') →
      ClauseCheck ⟨sig, Ξannot, 𝒢, caller, Ψ₁⟩ (KindingCtx.empty.extSizes Ψ₁) [] D' A') ∧
    (∀ (fuel : Nat) (Ψ : SizeCtx) (C : List SizeConstraint) (T : List SizeVar) (φ : FlexSubst),
      CheckedConstraintSolver.checkedSolve fuel Ψ C T = some φ →
      CoherentSubst Ψ C φ) ∧
    (∀ (sig : GlobalSig) (Ξ Ξannot : MutualBlock),
      PostcheckedAlgorithm2Accepts sig Ξ Ξannot →
      MutualBlockTyping sig Ξannot) := NishtAbel2024V2.theorems_13_and_14
