-- Prove2me | solution 1 for MNLStability.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:43:19.54847+00:00
-- url     : https://prove2.me/submissions/1e11785e-8f33-4992-a131-44030fe619e9

import Mathlib
import Definitions.Def_MNLStability_prob
import Definitions.Def_MNLStability_IsLaw

open scoped ENNReal
open MNLStability

private lemma stepMass_sum_eq_one {n : ℕ} (wts : Weights n) (hw : wts.Pos) (V : Fin n → ℕ) :
    ∑ a : Option (Fin n), stepMass wts V a = 1 := by
  have hD : 0 < wts.w0 + wts.wsum (inStock V) := by
    have hsum : 0 ≤ wts.wsum (inStock V) := Finset.sum_nonneg fun i _ => (hw.2 i).le
    linarith [hw.1]
  rw [Fintype.sum_option]
  simp only [stepMass]
  have hsub : (∑ i : Fin n, if 0 < V i then ENNReal.ofReal (wts.w i / (wts.w0 + wts.wsum (inStock V))) else 0) =
      ∑ i ∈ inStock V, ENNReal.ofReal (wts.w i / (wts.w0 + wts.wsum (inStock V))) := by
    rw [← Finset.sum_filter]
    rfl
  rw [hsub, ← ENNReal.ofReal_sum_of_nonneg (fun i _ => div_nonneg (hw.2 i).le hD.le),
      ← ENNReal.ofReal_add (div_nonneg hw.1.le hD.le)
        (Finset.sum_nonneg fun i _ => div_nonneg (hw.2 i).le hD.le)]
  have hval : wts.w0 / (wts.w0 + wts.wsum (inStock V)) +
      ∑ i ∈ inStock V, wts.w i / (wts.w0 + wts.wsum (inStock V)) = 1 := by
    rw [← Finset.sum_div, ← add_div]
    exact div_self hD.ne'
  rw [hval, ENNReal.ofReal_one]

private lemma step_apply_pos {n : ℕ} (wts : Weights n) (hw : wts.Pos) (V : Fin n → ℕ)
    (a : Option (Fin n)) : step wts V a = stepMass wts V a := by
  unfold step
  rw [dif_pos (stepMass_sum_eq_one wts hw V)]
  rfl

private lemma step_some_le {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) (j : Fin n) (hj : 0 < V' j) :
    step wts V (some j) ≤ step wts V' (some j) := by
  rw [step_apply_pos wts hw V, step_apply_pos wts hw V']
  have hjV : 0 < V j := lt_of_lt_of_le hj (hV j)
  simp only [stepMass, if_pos hj, if_pos hjV]
  apply ENNReal.ofReal_le_ofReal
  have hsub : inStock V' ⊆ inStock V := by
    intro k hk
    simp only [inStock, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact lt_of_lt_of_le hk (hV k)
  have hwsum : wts.wsum (inStock V') ≤ wts.wsum (inStock V) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => (hw.2 k).le
  have hD' : 0 < wts.w0 + wts.wsum (inStock V') := by
    have : 0 ≤ wts.wsum (inStock V') := Finset.sum_nonneg fun k _ => (hw.2 k).le
    linarith [hw.1]
  exact div_le_div_of_nonneg_left (hw.2 j).le hD' (add_le_add_right hwsum _)

private noncomputable def scDiag {n : ℕ} (wts : Weights n) (V V' : Fin n → ℕ)
    (a : Option (Fin n)) : ℝ≥0∞ :=
  match a with
  | none => 0
  | some j => if 0 < V' j then step wts V (some j) else 0

private noncomputable def scLeftV {n : ℕ} (wts : Weights n) (V V' : Fin n → ℕ) :
    Option (Fin n) → ℝ≥0∞
  | none => step wts V none
  | some j => if 0 < V' j then 0 else step wts V (some j)

private noncomputable def scLeftV' {n : ℕ} (wts : Weights n) (V V' : Fin n → ℕ) :
    Option (Fin n) → ℝ≥0∞
  | none => step wts V' none
  | some j => if 0 < V' j then step wts V' (some j) - step wts V (some j) else 0

private lemma scDiag_add_leftV {n : ℕ} (wts : Weights n) (V V' : Fin n → ℕ) (a : Option (Fin n)) :
    scDiag wts V V' a + scLeftV wts V V' a = step wts V a := by
  cases a with
  | none => simp [scDiag, scLeftV]
  | some j =>
    simp only [scDiag, scLeftV]
    split_ifs <;> simp

private lemma scDiag_add_leftV' {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) (a : Option (Fin n)) :
    scDiag wts V V' a + scLeftV' wts V V' a = step wts V' a := by
  cases a with
  | none => simp [scDiag, scLeftV']
  | some j =>
    simp only [scDiag, scLeftV']
    split_ifs with hj
    · exact add_tsub_cancel_of_le (step_some_le wts hw hV j hj)
    · rw [zero_add, step_apply_pos wts hw V']
      simp [stepMass, hj]

private lemma scLeft_sum_eq {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) :
    ∑ a : Option (Fin n), scLeftV wts V V' a = ∑ a : Option (Fin n), scLeftV' wts V V' a := by
  have h1 : ∑ a : Option (Fin n), (scDiag wts V V' a + scLeftV wts V V' a) = 1 := by
    simp_rw [scDiag_add_leftV]
    have hts := (step wts V).tsum_coe
    rwa [tsum_fintype] at hts
  have h2 : ∑ a : Option (Fin n), (scDiag wts V V' a + scLeftV' wts V V' a) = 1 := by
    simp_rw [scDiag_add_leftV' wts hw hV]
    have := (step wts V').tsum_coe
    rwa [tsum_fintype] at this
  rw [Finset.sum_add_distrib] at h1 h2
  have hDne : ∑ a : Option (Fin n), scDiag wts V V' a ≠ ⊤ := by
    intro htop
    rw [htop, top_add] at h1
    exact ENNReal.top_ne_one h1
  exact (ENNReal.add_right_inj hDne).mp (h1.trans h2.symm)

private noncomputable def stepCouplingFun {n : ℕ} (wts : Weights n) (V V' : Fin n → ℕ)
    (p : Option (Fin n) × Option (Fin n)) : ℝ≥0∞ :=
  let R := ∑ a : Option (Fin n), scLeftV wts V V' a
  (if p.1 = p.2 then scDiag wts V V' p.1 else 0) +
    if R = 0 then 0 else scLeftV wts V V' p.1 * scLeftV' wts V V' p.2 / R

private lemma stepCouplingFun_sum_snd {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) (a : Option (Fin n)) :
    ∑ a' : Option (Fin n), stepCouplingFun wts V V' (a, a') = step wts V a := by
  simp only [stepCouplingFun, Finset.sum_add_distrib]
  have hdiag : (∑ a' : Option (Fin n), if a = a' then scDiag wts V V' a else 0) =
      scDiag wts V V' a := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb.symm]
    · intro h; exact absurd (Finset.mem_univ a) h
  rw [hdiag]
  set R := ∑ b : Option (Fin n), scLeftV wts V V' b
  by_cases hR : R = 0
  · have hleft : scLeftV wts V V' a = 0 := by
      have hsum0 : ∑ b : Option (Fin n), scLeftV wts V V' b = 0 := hR
      rw [Finset.sum_eq_zero_iff] at hsum0
      exact hsum0 a (Finset.mem_univ a)
    simp [hR, hleft, ← scDiag_add_leftV wts V V' a]
  · have hRtop : R ≠ ⊤ := by
      have hle : R ≤ ∑ b : Option (Fin n), step wts V b :=
        Finset.sum_le_sum fun b _ => by rw [← scDiag_add_leftV wts V V' b]; exact le_add_self
      have h1 : ∑ b : Option (Fin n), step wts V b = 1 := by
        have := (step wts V).tsum_coe; rwa [tsum_fintype] at this
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (hle.trans_eq h1)
    simp only [if_neg hR]
    have hsum' : (∑ a' : Option (Fin n), scLeftV wts V V' a * scLeftV' wts V V' a' / R) =
        scLeftV wts V V' a := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← scLeft_sum_eq wts hw hV]
      change scLeftV wts V V' a * R * R⁻¹ = scLeftV wts V V' a
      rw [mul_assoc, ENNReal.mul_inv_cancel hR hRtop, mul_one]
    rw [hsum', scDiag_add_leftV]

private lemma stepCouplingFun_sum_fst {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) (a' : Option (Fin n)) :
    ∑ a : Option (Fin n), stepCouplingFun wts V V' (a, a') = step wts V' a' := by
  simp only [stepCouplingFun, Finset.sum_add_distrib]
  have hdiag : (∑ a : Option (Fin n), if a = a' then scDiag wts V V' a else 0) =
      scDiag wts V V' a' := by
    rw [Finset.sum_eq_single a']
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ a') h
  rw [hdiag]
  set R := ∑ b : Option (Fin n), scLeftV wts V V' b
  by_cases hR : R = 0
  · have hsum0 : ∑ b : Option (Fin n), scLeftV' wts V V' b = 0 :=
      (scLeft_sum_eq wts hw hV).symm.trans hR
    rw [Finset.sum_eq_zero_iff] at hsum0
    have hleft' : scLeftV' wts V V' a' = 0 := hsum0 a' (Finset.mem_univ a')
    simp [hR, hleft', ← scDiag_add_leftV' wts hw hV a']
  · have hRtop : R ≠ ⊤ := by
      have hle : R ≤ ∑ b : Option (Fin n), step wts V b :=
        Finset.sum_le_sum fun b _ => by rw [← scDiag_add_leftV wts V V' b]; exact le_add_self
      have h1 : ∑ b : Option (Fin n), step wts V b = 1 := by
        have := (step wts V).tsum_coe; rwa [tsum_fintype] at this
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (hle.trans_eq h1)
    simp only [if_neg hR]
    have hsum : (∑ a : Option (Fin n), scLeftV wts V V' a * scLeftV' wts V V' a' / R) =
        scLeftV' wts V V' a' := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul, ← Finset.sum_mul]
      change R * scLeftV' wts V V' a' * R⁻¹ = scLeftV' wts V V' a'
      rw [mul_comm R _, mul_assoc, ENNReal.mul_inv_cancel hR hRtop, mul_one]
    rw [hsum, scDiag_add_leftV' wts hw hV]

private lemma stepCouplingFun_sum_one {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) :
    ∑ p : Option (Fin n) × Option (Fin n), stepCouplingFun wts V V' p = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [stepCouplingFun_sum_snd wts hw hV]
  have := (step wts V).tsum_coe
  rwa [tsum_fintype] at this

private noncomputable def stepCoupling {n : ℕ} (wts : Weights n) (hw : wts.Pos)
    (V V' : Fin n → ℕ) : PMF (Option (Fin n) × Option (Fin n)) :=
  if hV : ∀ j, V' j ≤ V j then
    PMF.ofFintype (stepCouplingFun wts V V') (stepCouplingFun_sum_one wts hw hV)
  else PMF.pure (none, none)

private lemma stepCoupling_map_fst {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) : (stepCoupling wts hw V V').map Prod.fst = step wts V := by
  ext a
  have hV' : ∀ j, V' j ≤ V j := hV
  simp only [stepCoupling, dif_pos hV', PMF.map_apply, PMF.ofFintype_apply]
  rw [tsum_fintype, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a]
  · simp only [↓reduceIte]
    exact stepCouplingFun_sum_snd wts hw hV a
  · intro b _ hb
    refine Finset.sum_eq_zero fun a' _ => ?_
    simp [hb.symm]
  · intro h; exact absurd (Finset.mem_univ a) h

private lemma stepCoupling_map_snd {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) : (stepCoupling wts hw V V').map Prod.snd = step wts V' := by
  ext a'
  have hV' : ∀ j, V' j ≤ V j := hV
  simp only [stepCoupling, dif_pos hV', PMF.map_apply, PMF.ofFintype_apply]
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_comm]
  rw [Finset.sum_eq_single a']
  · simp only [↓reduceIte]
    exact stepCouplingFun_sum_fst wts hw hV a'
  · intro b _ hb
    refine Finset.sum_eq_zero fun a _ => ?_
    simp [hb.symm]
  · intro h; exact absurd (Finset.mem_univ a') h

private lemma stepCoupling_support {n : ℕ} (wts : Weights n) (hw : wts.Pos) {V V' : Fin n → ℕ}
    (hV : V' ≤ V) {a a' : Option (Fin n)} (hmem : (a, a') ∈ (stepCoupling wts hw V V').support) :
    (∀ j, a = some j → 0 < V' j → a' = some j) ∧
    (∀ j, a = some j → 0 < V j) ∧
    (∀ k, a' = some k → 0 < V' k) := by
  have hV' : ∀ j, V' j ≤ V j := hV
  rw [PMF.mem_support_iff, stepCoupling, dif_pos hV', PMF.ofFintype_apply] at hmem
  refine ⟨?_, ?_, ?_⟩
  · intro j ha hj
    subst ha
    by_contra hne
    have h0 : stepCouplingFun wts V V' (some j, a') = 0 := by
      simp [stepCouplingFun, scLeftV, hj, Ne.symm hne]
    exact hmem h0
  · intro j ha
    subst ha
    by_contra hle
    have h0 : stepCouplingFun wts V V' (some j, a') = 0 := by
      have hj' : ¬ (0 < V' j) := fun h => hle (lt_of_lt_of_le h (hV j))
      have hs0 : step wts V (some j) = 0 := by
        rw [step_apply_pos wts hw V]; simp [stepMass, hle]
      simp [stepCouplingFun, scDiag, scLeftV, hj', hs0]
    exact hmem h0
  · intro k ha'
    subst ha'
    by_contra hle
    have h0 : stepCouplingFun wts V V' (a, some k) = 0 := by
      have hdiag : (if a = some k then scDiag wts V V' a else 0) = 0 := by
        split_ifs with heq
        · subst heq; simp [scDiag, hle]
        · rfl
      simp [stepCouplingFun, hdiag, scLeftV', hle]
    exact hmem h0

private def nextConsumed {n : ℕ} (x : Fin n → ℕ) : Option (Fin n) → (Fin n → ℕ)
  | none => x
  | some i => x + Pi.single i 1

private noncomputable def demandCoupling {n : ℕ} (wts : Weights n) (hw : wts.Pos)
    (U U' : Fin n → ℕ) : ℕ → PMF ((Fin n → ℕ) × (Fin n → ℕ))
  | 0 => PMF.pure (0, 0)
  | m + 1 => (demandCoupling wts hw U U' m).bind fun p =>
      (stepCoupling wts hw (U - p.1) (U' - p.2)).map fun q =>
        (nextConsumed p.1 q.1, nextConsumed p.2 q.2)

private lemma demand_map_fst {n : ℕ} (wts : Weights n) (U : Fin n → ℕ) (m : ℕ) :
    (demand wts U m).map Prod.fst =
      match m with
      | 0 => PMF.pure 0
      | m + 1 => ((demand wts U m).map Prod.fst).bind fun x =>
          (step wts (U - x)).map (nextConsumed x) := by
  induction m with
  | zero =>
    ext x
    simp only [demand, PMF.map_apply, PMF.pure_apply]
    rw [tsum_eq_single (0, 0)]
    · simp
    · intro b hb; simp [hb]
  | succ m _ =>
    simp only [demand, PMF.map_bind, PMF.bind_map]
    congr 1
    funext x
    rw [PMF.map_comp]
    congr 1
    funext a
    cases a <;> rfl

private lemma demandCoupling_inv {n : ℕ} (wts : Weights n) (hw : wts.Pos)
    (U U' : Fin n → ℕ) (hU : U' ≤ U) (m : ℕ) :
    (demandCoupling wts hw U U' m).map Prod.fst = (demand wts U m).map Prod.fst ∧
    (demandCoupling wts hw U U' m).map Prod.snd = (demand wts U' m).map Prod.fst ∧
    ∀ p ∈ (demandCoupling wts hw U U' m).support,
      p.1 ≤ U ∧ p.2 ≤ U' ∧ ∀ j, p.2 j = U' j ∨ p.1 j ≤ p.2 j := by
  induction m with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · ext x
      simp only [demandCoupling, demand, PMF.map_apply, PMF.pure_apply]
      rw [tsum_eq_single (0, 0), tsum_eq_single (0, 0)]
      · simp
      · intro b hb; simp [hb]
      · intro b hb; simp [hb]
    · ext x
      simp only [demandCoupling, demand, PMF.map_apply, PMF.pure_apply]
      rw [tsum_eq_single (0, 0), tsum_eq_single (0, 0)]
      · simp
      · intro b hb; simp [hb]
      · intro b hb; simp [hb]
    · intro p hp
      simp only [demandCoupling, PMF.mem_support_iff, PMF.pure_apply] at hp
      have hp0 : p = (0, 0) := by by_contra h; exact hp (if_neg h)
      subst hp0
      exact ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _, fun _ => Or.inr le_rfl⟩
  | succ m ih =>
    rcases ih with ⟨ih1, ih2, ihsupp⟩
    have hVle : ∀ p ∈ (demandCoupling wts hw U U' m).support, U' - p.2 ≤ U - p.1 := by
      intro p hp j
      rcases ihsupp p hp with ⟨_, _, hj⟩
      dsimp only [Pi.sub_apply]
      rcases hj j with hsat | hle
      · simp [hsat]
      · exact tsub_le_tsub (hU j) hle
    have hfst : (demandCoupling wts hw U U' (m + 1)).map Prod.fst =
        (demand wts U (m + 1)).map Prod.fst := by
      rw [demand_map_fst]
      simp only [demandCoupling, PMF.map_bind]
      rw [← ih1, PMF.bind_map]
      ext z
      simp only [PMF.bind_apply]
      refine tsum_congr fun p => ?_
      by_cases hp : p ∈ (demandCoupling wts hw U U' m).support
      · congr 1
        rw [PMF.map_comp,
          show (Prod.fst ∘ fun q => (nextConsumed p.1 q.1, nextConsumed p.2 q.2)) =
            nextConsumed p.1 ∘ Prod.fst from rfl,
          ← PMF.map_comp, stepCoupling_map_fst wts hw (hVle p hp)]
        rfl
      · rw [PMF.mem_support_iff, not_not] at hp
        simp [hp]
    have hsnd : (demandCoupling wts hw U U' (m + 1)).map Prod.snd =
        (demand wts U' (m + 1)).map Prod.fst := by
      rw [demand_map_fst]
      simp only [demandCoupling, PMF.map_bind]
      rw [← ih2, PMF.bind_map]
      ext z
      simp only [PMF.bind_apply]
      refine tsum_congr fun p => ?_
      by_cases hp : p ∈ (demandCoupling wts hw U U' m).support
      · congr 1
        rw [PMF.map_comp,
          show (Prod.snd ∘ fun q => (nextConsumed p.1 q.1, nextConsumed p.2 q.2)) =
            nextConsumed p.2 ∘ Prod.snd from rfl,
          ← PMF.map_comp, stepCoupling_map_snd wts hw (hVle p hp)]
        rfl
      · rw [PMF.mem_support_iff, not_not] at hp
        simp [hp]
    refine ⟨hfst, hsnd, ?_⟩
    intro r hr
    rw [PMF.mem_support_iff, demandCoupling, PMF.bind_apply] at hr
    have hexp : ∃ p, (demandCoupling wts hw U U' m) p *
        ((stepCoupling wts hw (U - p.1) (U' - p.2)).map
          fun q => (nextConsumed p.1 q.1, nextConsumed p.2 q.2)) r ≠ 0 := by
      by_contra h0
      push Not at h0
      exact hr (ENNReal.tsum_eq_zero.mpr h0)
    obtain ⟨p, hp0⟩ := hexp
    have hp : p ∈ (demandCoupling wts hw U U' m).support := by
      rw [PMF.mem_support_iff]; exact left_ne_zero_of_mul hp0
    have hq0 : ((stepCoupling wts hw (U - p.1) (U' - p.2)).map
        fun q => (nextConsumed p.1 q.1, nextConsumed p.2 q.2)) r ≠ 0 :=
      right_ne_zero_of_mul hp0
    rw [PMF.map_apply] at hq0
    have hexq : ∃ q, (stepCoupling wts hw (U - p.1) (U' - p.2)) q ≠ 0 ∧
        r = (nextConsumed p.1 q.1, nextConsumed p.2 q.2) := by
      by_contra h0
      push Not at h0
      apply hq0
      rw [ENNReal.tsum_eq_zero]
      intro q
      by_cases hq : r = (nextConsumed p.1 q.1, nextConsumed p.2 q.2)
      · rw [if_pos hq]
        by_contra hne
        exact h0 q hne hq
      · simp [hq]
    obtain ⟨⟨a, a'⟩, haa'0, hr_eq⟩ := hexq
    have haa' : (a, a') ∈ (stepCoupling wts hw (U - p.1) (U' - p.2)).support := by
      rw [PMF.mem_support_iff]; exact haa'0
    rcases ihsupp p hp with ⟨hpU, hpU', hpj⟩
    rcases stepCoupling_support wts hw (hVle p hp) haa' with ⟨hdiag, hapos, ha'pos⟩
    subst hr_eq
    have hr1 : nextConsumed p.1 a ≤ U := by
      cases a with
      | none => exact hpU
      | some k =>
        intro j
        by_cases hjk : j = k
        · subst hjk
          have hkpos : 0 < U j - p.1 j := hapos j rfl
          simp only [nextConsumed, Pi.add_apply, Pi.single_eq_same]
          omega
        · simp [nextConsumed, hjk, hpU j]
    have hr2 : nextConsumed p.2 a' ≤ U' := by
      cases a' with
      | none => exact hpU'
      | some k =>
        intro j
        by_cases hjk : j = k
        · subst hjk
          have hkpos : 0 < U' j - p.2 j := ha'pos j rfl
          simp only [nextConsumed, Pi.add_apply, Pi.single_eq_same]
          omega
        · simp [nextConsumed, hjk, hpU' j]
    refine ⟨hr1, hr2, fun j => ?_⟩
    rcases hpj j with hsat | hle
    · left
      have hjnot : a' ≠ some j := by
        intro ha'
        have hkpos := ha'pos j ha'
        simp [hsat] at hkpos
      cases a' with
      | none => exact hsat
      | some k =>
        have hjk : j ≠ k := fun h => hjnot (congrArg some h.symm)
        simp [nextConsumed, hjk, hsat]
    · by_cases ha_j : a = some j
      · subst ha_j
        by_cases hjpos : 0 < U' j - p.2 j
        · right
          rw [hdiag j rfl hjpos]
          simp [nextConsumed, hle]
        · left
          have hsat : p.2 j = U' j :=
            Nat.le_antisymm (hpU' j) (Nat.le_of_not_lt fun h => hjpos (Nat.sub_pos_of_lt h))
          have hjnot : a' ≠ some j := fun ha' => hjpos (ha'pos j ha')
          cases a' with
          | none => exact hsat
          | some k =>
            have hjk : j ≠ k := fun h => hjnot (congrArg some h.symm)
            simp [nextConsumed, hjk, hsat]
      · right
        have h1eq : nextConsumed p.1 a j = p.1 j := by
          cases a with
          | none => rfl
          | some k =>
            have hjk : j ≠ k := fun h => ha_j (congrArg some h.symm)
            simp [nextConsumed, hjk]
        have h2ge : p.2 j ≤ nextConsumed p.2 a' j := by
          cases a' with
          | none => exact le_rfl
          | some k => simp [nextConsumed]
        calc nextConsumed p.1 a j = p.1 j := h1eq
          _ ≤ p.2 j := hle
          _ ≤ nextConsumed p.2 a' j := h2ge

private lemma unitProb_le_of_le {n : ℕ} (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ)
    (hM : IsLaw pM) {U U' : Fin n → ℕ} (hU : U' ≤ U) (i : Fin n) (u : ℕ) (hu : u ≤ U' i) :
    unitProb wts pM U i u ≤ unitProb wts pM U' i u := by
  have hprob : ∀ m : ℕ, prob wts U m {x | u ≤ x.1 i} ≤ prob wts U' m {x | u ≤ x.1 i} := by
    intro m
    rcases demandCoupling_inv wts hw U U' hU m with ⟨h1, h2, hsupp⟩
    let c := demandCoupling wts hw U U' m
    have hlhs : prob wts U m {x | u ≤ x.1 i} = (c.toOuterMeasure {p | u ≤ p.1 i}).toReal := by
      unfold prob
      change ((demand wts U m).toOuterMeasure (Prod.fst ⁻¹' {x | u ≤ x i})).toReal = _
      rw [← PMF.toOuterMeasure_map_apply Prod.fst (demand wts U m) {x | u ≤ x i}]
      rw [← h1, PMF.toOuterMeasure_map_apply]
      rfl
    have hrhs : prob wts U' m {x | u ≤ x.1 i} = (c.toOuterMeasure {p | u ≤ p.2 i}).toReal := by
      unfold prob
      change ((demand wts U' m).toOuterMeasure (Prod.fst ⁻¹' {x | u ≤ x i})).toReal = _
      rw [← PMF.toOuterMeasure_map_apply Prod.fst (demand wts U' m) {x | u ≤ x i}]
      rw [← h2, PMF.toOuterMeasure_map_apply]
      rfl
    rw [hlhs, hrhs]
    have hlt : c.toOuterMeasure {p | u ≤ p.2 i} ≠ ⊤ := by
      have h1 : c.toOuterMeasure {p | u ≤ p.2 i} ≤ c.toOuterMeasure Set.univ :=
        c.toOuterMeasure.mono (Set.subset_univ _)
      have huniv : c.toOuterMeasure Set.univ = 1 := by
        rw [PMF.toOuterMeasure_apply]
        simp [Set.indicator, c.tsum_coe]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (h1.trans_eq huniv)
    refine ENNReal.toReal_mono hlt ?_
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine ENNReal.tsum_le_tsum fun p => ?_
    by_cases hp : p ∈ c.support
    · rcases hsupp p hp with ⟨_, _, hj⟩
      by_cases hpi : u ≤ p.1 i
      · have hpi' : u ≤ p.2 i := by
          rcases hj i with hsat | hle
          · exact hsat ▸ hu
          · exact le_trans hpi hle
        simp [Set.indicator, hpi, hpi']
      · simp [Set.indicator, hpi]
    · rw [PMF.mem_support_iff, not_not] at hp
      simp only [Set.indicator]
      split_ifs <;> simp [hp]
  unfold unitProb probM
  refine Finset.sum_le_sum fun m _ => ?_
  exact mul_le_mul_of_nonneg_left (hprob m) (hM.1 m)

private lemma demand_trunc_eq {n : ℕ} (wts : Weights n) (hw : wts.Pos)
    (U : Fin n → ℕ) (i₁ : Fin n) (B : ℕ) (hB : B ≤ U i₁) (m : ℕ) :
    let U' : Fin n → ℕ := fun k => if k = i₁ then B else U k
    ∀ x : Fin n → ℕ, x i₁ < B →
      ((demand wts U m).map Prod.fst) x = ((demand wts U' m).map Prod.fst) x := by
  intro U'
  induction m with
  | zero =>
    intro x _
    rw [demand_map_fst, demand_map_fst]
  | succ m ih =>
    intro x hx
    rw [demand_map_fst, demand_map_fst]
    simp only [PMF.bind_apply]
    refine tsum_congr fun y => ?_
    by_cases hy : y i₁ < B
    · rw [ih y hy]
      have hstep : step wts (U - y) = step wts (U' - y) := by
        have hin : inStock (U - y) = inStock (U' - y) := by
          ext k
          simp only [inStock, Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, U']
          split_ifs with hk
          · subst hk; constructor <;> intro _ <;> omega
          · rfl
        ext a
        rw [step_apply_pos wts hw (U - y), step_apply_pos wts hw (U' - y)]
        cases a with
        | none => simp [stepMass, hin]
        | some k =>
          have hkpos : (0 < (U - y) k ↔ 0 < (U' - y) k) := by
            simp only [Pi.sub_apply, U']
            split_ifs with hki
            · subst hki; constructor <;> intro _ <;> omega
            · rfl
          simp only [stepMass, hkpos, hin]
      rw [hstep]
    · have h0 : ∀ a, x = nextConsumed y a → False := by
        intro a ha
        have hle : y i₁ ≤ nextConsumed y a i₁ := by
          cases a with
          | none => exact le_rfl
          | some k => simp [nextConsumed]
        rw [← ha] at hle
        omega
      have hz : ((step wts (U - y)).map (nextConsumed y)) x = 0 := by
        simp only [PMF.map_apply]
        rw [ENNReal.tsum_eq_zero]
        intro a
        split_ifs with h
        · exact absurd h (h0 a)
        · rfl
      have hz' : ((step wts (U' - y)).map (nextConsumed y)) x = 0 := by
        simp only [PMF.map_apply]
        rw [ENNReal.tsum_eq_zero]
        intro a
        split_ifs with h
        · exact absurd h (h0 a)
        · rfl
      rw [hz, hz', mul_zero, mul_zero]

private lemma unitProb_trunc_eq {n : ℕ} (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ)
    (U : Fin n → ℕ) (i₁ : Fin n) (B : ℕ) (hB : B ≤ U i₁) (u : ℕ) (hu : u ≤ B) :
    unitProb wts pM U i₁ u =
      unitProb wts pM (fun k => if k = i₁ then B else U k) i₁ u := by
  let U' : Fin n → ℕ := fun k => if k = i₁ then B else U k
  have hprob : ∀ m : ℕ, prob wts U m {x | u ≤ x.1 i₁} = prob wts U' m {x | u ≤ x.1 i₁} := by
    intro m
    let p1 := (demand wts U m).map Prod.fst
    let p2 := (demand wts U' m).map Prod.fst
    have hcomp : ∀ (p : PMF (Fin n → ℕ)),
        p.toOuterMeasure {x | u ≤ x i₁} + p.toOuterMeasure {x | x i₁ < u} = 1 := by
      intro p
      rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
      have hsum : (fun x : Fin n → ℕ =>
          Set.indicator {x | u ≤ x i₁} p x + Set.indicator {x | x i₁ < u} p x) = p := by
        ext x
        simp only [Set.indicator, Set.mem_setOf_eq]
        split_ifs with h1 h2
        · omega
        · simp
        · simp
        · omega
      rw [hsum]
      exact p.tsum_coe
    have hlt_eq : p1.toOuterMeasure {x | x i₁ < u} = p2.toOuterMeasure {x | x i₁ < u} := by
      rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
      refine tsum_congr fun x => ?_
      simp only [Set.indicator, Set.mem_setOf_eq]
      split_ifs with hx
      · exact demand_trunc_eq wts hw U i₁ B hB m x (lt_of_lt_of_le hx hu)
      · rfl
    have h1 := hcomp p1
    have h2 := hcomp p2
    rw [hlt_eq] at h1
    have hne : p2.toOuterMeasure {x | x i₁ < u} ≠ ⊤ := by
      have hle : p2.toOuterMeasure {x | x i₁ < u} ≤ p2.toOuterMeasure Set.univ :=
        p2.toOuterMeasure.mono (Set.subset_univ _)
      have huniv : p2.toOuterMeasure Set.univ = 1 := by
        rw [PMF.toOuterMeasure_apply]
        simp [Set.indicator, p2.tsum_coe]
      exact ne_top_of_le_ne_top ENNReal.one_ne_top (hle.trans_eq huniv)
    have hge_eq : p1.toOuterMeasure {x | u ≤ x i₁} = p2.toOuterMeasure {x | u ≤ x i₁} :=
      (ENNReal.add_left_inj hne).mp (h1.trans h2.symm)
    unfold prob
    have e1 : (demand wts U m).toOuterMeasure {x | u ≤ x.1 i₁} = p1.toOuterMeasure {x | u ≤ x i₁} := by
      change (demand wts U m).toOuterMeasure (Prod.fst ⁻¹' {x | u ≤ x i₁}) = _
      rw [← PMF.toOuterMeasure_map_apply Prod.fst (demand wts U m) {x | u ≤ x i₁}]
    have e2 : (demand wts U' m).toOuterMeasure {x | u ≤ x.1 i₁} = p2.toOuterMeasure {x | u ≤ x i₁} := by
      change (demand wts U' m).toOuterMeasure (Prod.fst ⁻¹' {x | u ≤ x i₁}) = _
      rw [← PMF.toOuterMeasure_map_apply Prod.fst (demand wts U' m) {x | u ≤ x i₁}]
    rw [e1, e2, hge_eq]
  unfold unitProb probM
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hprob m]

private lemma demand_swap {n : ℕ} (wts : Weights n) (hw : wts.Pos)
    (i₁ i₂ : Fin n) (hw₁₂ : wts.w i₁ = wts.w i₂) (U : Fin n → ℕ) (m : ℕ) :
    let σ := Equiv.swap i₁ i₂
    (demand wts (U ∘ σ) m).map Prod.fst = ((demand wts U m).map Prod.fst).map (fun x => x ∘ σ) := by
  intro σ
  induction m with
  | zero =>
    rw [demand_map_fst, demand_map_fst]
    ext x
    simp only [PMF.map_apply, PMF.pure_apply]
    rw [tsum_eq_single 0]
    · simp
    · intro b hb; simp [hb]
  | succ m ih =>
    rw [demand_map_fst, demand_map_fst]
    dsimp only
    rw [ih, PMF.bind_map, PMF.map_bind]
    ext z
    simp only [PMF.bind_apply]
    refine tsum_congr fun y => ?_
    congr 1
    have hstep : step wts (U ∘ σ - y ∘ σ) = (step wts (U - y)).map (Option.map σ) := by
      have hstock : inStock (U ∘ σ - y ∘ σ) = (inStock (U - y)).image σ := by
        ext k
        simp only [inStock, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
          Pi.sub_apply, Function.comp_apply]
        constructor
        · intro hk
          refine ⟨σ k, hk, by simp [σ]⟩
        · rintro ⟨j, hj, rfl⟩
          simpa [σ] using hj
      have hwsum : wts.wsum (inStock (U ∘ σ - y ∘ σ)) = wts.wsum (inStock (U - y)) := by
        rw [hstock, Weights.wsum, Weights.wsum, Finset.sum_image (fun a _ b _ h => σ.injective h)]
        refine Finset.sum_congr rfl fun k _ => ?_
        dsimp only [σ]
        by_cases h1 : k = i₁
        · subst h1; simp [hw₁₂]
        · by_cases h2 : k = i₂
          · subst h2; simp [hw₁₂]
          · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
      ext a
      rw [step_apply_pos wts hw (U ∘ σ - y ∘ σ)]
      cases a with
      | none =>
        rw [PMF.map_apply, tsum_eq_single none]
        · simp [step_apply_pos wts hw (U - y), stepMass, hwsum]
        · intro b hb; cases b <;> simp_all
      | some k =>
        rw [PMF.map_apply, tsum_eq_single (some (σ k))]
        · rw [step_apply_pos wts hw (U - y)]
          have hw_eq : wts.w (σ k) = wts.w k := by
            dsimp only [σ]
            by_cases h1 : k = i₁
            · subst h1; simp [hw₁₂]
            · by_cases h2 : k = i₂
              · subst h2; simp [hw₁₂]
              · simp [Equiv.swap_apply_of_ne_of_ne h1 h2]
          simp [stepMass, hwsum, hw_eq, σ]
        · intro b hb
          cases b with
          | none => simp
          | some j =>
            simp only [Option.map_some]
            split_ifs with h
            · exfalso; apply hb; congr 1
              simpa [σ] using (congrArg σ (Option.some.inj h)).symm
            · rfl
    dsimp only [Function.comp_apply]
    rw [hstep, PMF.map_comp, PMF.map_comp]
    have hfn : nextConsumed (y ∘ ⇑σ) ∘ Option.map ⇑σ = (fun x => x ∘ ⇑σ) ∘ nextConsumed y := by
      funext a
      cases a with
      | none => simp [nextConsumed]
      | some k =>
        ext j
        have heq_iff : j = σ k ↔ σ j = k := by
          dsimp only [σ]
          rw [← Equiv.eq_symm_apply (Equiv.swap i₁ i₂), Equiv.symm_swap]
        simp only [Function.comp_apply, Option.map_some, nextConsumed, Pi.add_apply,
          Pi.single_apply, heq_iff]
    rw [hfn]

theorem solution {n : ℕ} (wts : Weights n) (hw : wts.Pos) (pM : ℕ →₀ ℝ) (hM : IsLaw pM)
    (U : Fin n → ℕ) (i₁ i₂ : Fin n) (hne : i₁ ≠ i₂) (hw₁₂ : wts.w i₁ = wts.w i₂)
    (hU : U i₂ ≤ U i₁) (u : ℕ) (hu1 : 1 ≤ u) (hu : u ≤ U i₂) :
    unitProb wts pM U i₂ u ≤ unitProb wts pM U i₁ u := by
  let σ := Equiv.swap i₁ i₂
  let U_trunc : Fin n → ℕ := fun k => if k = i₁ then U i₂ else U k
  have h1 : unitProb wts pM U i₁ u = unitProb wts pM U_trunc i₁ u :=
    unitProb_trunc_eq wts hw pM U i₁ (U i₂) hU u hu
  have hle : U_trunc ≤ U ∘ σ := by
    intro k
    dsimp only [U_trunc, Function.comp_apply, σ]
    by_cases hk1 : k = i₁
    · subst hk1; simp
    · by_cases hk2 : k = i₂
      · subst hk2; simp [hne.symm, hU]
      · simp [hk1, Equiv.swap_apply_of_ne_of_ne hk1 hk2]
  have h2 : unitProb wts pM (U ∘ σ) i₁ u ≤ unitProb wts pM U_trunc i₁ u :=
    unitProb_le_of_le wts hw pM hM hle i₁ u (by simp [U_trunc, hu])
  have h3 : unitProb wts pM (U ∘ σ) i₁ u = unitProb wts pM U i₂ u := by
    unfold unitProb probM
    refine Finset.sum_congr rfl fun m _ => ?_
    congr 1
    unfold prob
    have e1 : (demand wts (U ∘ σ) m).toOuterMeasure {x | u ≤ x.1 i₁} =
        ((demand wts (U ∘ σ) m).map Prod.fst).toOuterMeasure {x | u ≤ x i₁} := by
      change (demand wts (U ∘ σ) m).toOuterMeasure (Prod.fst ⁻¹' {x | u ≤ x i₁}) = _
      rw [← PMF.toOuterMeasure_map_apply Prod.fst (demand wts (U ∘ σ) m) {x | u ≤ x i₁}]
    have e2 : (demand wts U m).toOuterMeasure {x | u ≤ x.1 i₂} =
        ((demand wts U m).map Prod.fst).toOuterMeasure {x | u ≤ x i₂} := by
      change (demand wts U m).toOuterMeasure (Prod.fst ⁻¹' {x | u ≤ x i₂}) = _
      rw [← PMF.toOuterMeasure_map_apply Prod.fst (demand wts U m) {x | u ≤ x i₂}]
    rw [e1, e2, demand_swap wts hw i₁ i₂ hw₁₂ U m, PMF.toOuterMeasure_map_apply]
    have hset : (fun x => x ∘ σ) ⁻¹' {x | u ≤ x i₁} = {x | u ≤ x i₂} := by
      ext x
      simp [σ]
    rw [hset]
  linarith
