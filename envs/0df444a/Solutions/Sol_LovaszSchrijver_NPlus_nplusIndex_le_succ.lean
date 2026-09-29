-- Prove2me | solution 1 for LovaszSchrijver.NPlus.nplusIndex_le_succ
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:47:30.026699+00:00
-- url     : https://prove2.me/submissions/06a1383d-6c12-48b6-a7b8-c01f4ddae16b

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_StableSet



namespace LovaszSchrijver.NPlus

open Matrix

theorem ls_Qnonneg {ι : Type} (q : Option ι → ℝ) (hq : q ∈ (Q : Set (Option ι → ℝ)))
    (j : Option ι) : 0 ≤ q j := by
  unfold Q cone at hq
  simp only [PointedCone.hull, SetLike.mem_coe] at hq
  induction hq using Submodule.span_induction with
  | mem x hx =>
    rcases hx.1 j with h | h <;> simp [h]
  | zero => simp
  | add x y _ _ hx hy => simp only [Pi.add_apply]; linarith
  | smul c x _ hx =>
    simp only [Pi.smul_apply, NNReal.smul_def, smul_eq_mul]
    exact mul_nonneg c.2 hx

theorem ls_Qd {ι : Type} [Fintype ι] [DecidableEq ι] (j : Option ι) :
    (Pi.single j (1:ℝ) : Option ι → ℝ) ∈ dualCone (Q : Set (Option ι → ℝ)) := by
  intro q hq
  simpa [single_dotProduct] using ls_Qnonneg q hq j

theorem ls_exp {ι : Type} [Fintype ι] [DecidableEq ι] (Y : Matrix ι ι ℝ) (a : ι → ℝ) :
    a ⬝ᵥ (Y *ᵥ a) = ∑ j, a j * (a ⬝ᵥ (Y *ᵥ Pi.single j 1)) := by
  simp only [mulVec_single_one]
  simp only [dotProduct, mulVec, Matrix.col, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro k _
  simp [transpose_apply]; ring

open Classical in
noncomputable def dS {ι : Type} (S : Set ι) : Option ι → ℝ :=
  fun o => Option.elim o 1 (fun i => if i ∈ S then 0 else 1)

noncomputable def Dop {ι : Type} (S : Set ι) (z : Option ι → ℝ) : Option ι → ℝ :=
  fun o => dS S o * z o

theorem dS_01 {ι : Type} (S : Set ι) (o : Option ι) : dS S o = 0 ∨ dS S o = 1 := by
  classical
  cases o with
  | none => right; rfl
  | some i => by_cases h : i ∈ S <;> simp [dS, h]

theorem dS_none {ι : Type} (S : Set ι) : dS S none = 1 := rfl

theorem Q_Dop {ι : Type} (S : Set ι) : ∀ q ∈ (Q : Set (Option ι → ℝ)), Dop S q ∈ Q := by
  intro q hq
  unfold Q cone at hq ⊢
  simp only [PointedCone.hull, SetLike.mem_coe] at hq ⊢
  induction hq using Submodule.span_induction with
  | mem x hx =>
    apply Submodule.subset_span
    refine ⟨?_, ?_⟩
    · intro j
      rcases dS_01 S j with h | h <;> rcases hx.1 j with h' | h' <;> simp [Dop, h, h']
    · simp [Dop, dS_none, hx.2]
  | zero =>
    have : Dop S (0 : Option ι → ℝ) = 0 := by funext o; simp [Dop]
    rw [this]; exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have : Dop S (x + y) = Dop S x + Dop S y := by funext o; simp [Dop]; ring
    rw [this]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    have : Dop S (c • x) = c • Dop S x := by
      funext o; simp only [Dop, Pi.smul_apply]; exact mul_smul_comm _ _ _
    rw [this]; exact Submodule.smul_mem _ c hx

theorem Dop_dot {ι : Type} [Fintype ι] (S : Set ι) (u z : Option ι → ℝ) :
    Dop S u ⬝ᵥ z = u ⬝ᵥ Dop S z := by
  simp only [dotProduct, Dop]; apply Finset.sum_congr rfl; intro j _; ring

theorem N1plus_Dop {ι : Type} [Fintype ι] [DecidableEq ι] (S : Set ι)
    (K : Set (Option ι → ℝ)) (hK : ∀ z ∈ K, Dop S z ∈ K) :
    ∀ z ∈ N1plus K, Dop S z ∈ N1plus K := by
  intro z hz
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, rfl⟩ := hz
  let d := dS S
  let Y' : Matrix (Option ι) (Option ι) ℝ := diagonal d * Y * diagonal d
  have hY' : ∀ p q, Y' p q = d p * Y p q * d q := by
    intro p q; simp [Y', mul_apply, diagonal]
  have hdd : ∀ p, d p * d p = d p := by
    intro p; rcases dS_01 S p with h | h <;> simp [d, h]
  refine ⟨Y', ⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · ext p q
    simp only [transpose_apply, hY']
    rw [hsym.apply]; ring
  · intro i
    rw [hY', hY', hdiag i]
    show d (some i) * Y none (some i) * d (some i) = d none * Y none (some i) * d (some i)
    rw [show d none = 1 from rfl]
    rcases dS_01 S (some i) with h | h <;> simp [d, h]
  · intro u hu v hv
    have : u ⬝ᵥ (Y' *ᵥ v) = Dop S u ⬝ᵥ (Y *ᵥ Dop S v) := by
      simp only [dotProduct, mulVec, hY', Dop, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _
      apply Finset.sum_congr rfl; intro k _
      simp only [d]; ring
    rw [this]
    apply hMc
    · intro x hx; rw [Dop_dot]; exact hu _ (hK x hx)
    · intro x hx; rw [Dop_dot]; exact hv _ (Q_Dop S x hx)
  · have := hpsd.mul_mul_conjTranspose_same (diagonal d)
    simpa [diagonal_conjTranspose, Y'] using this
  · ext p
    simp only [mulVec, dotProduct, hY', Dop, Pi.single_apply]
    simp [d, dS_none]

theorem N1plus_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (c : ℝ) (hc : 0 ≤ c) :
    ∀ z ∈ N1plus K, c • z ∈ N1plus K := by
  intro z hz
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, rfl⟩ := hz
  refine ⟨c • Y, ⟨⟨hsym.smul c, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro i; simp [hdiag i]
  · intro u hu v hv
    rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
    exact mul_nonneg hc (hMc u hu v hv)
  · exact hpsd.smul hc
  · rw [smul_mulVec]

theorem N1plus_FR {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (K : Set (Option V → ℝ)) (hK : K ⊆ FR G) : N1plus K ⊆ FR G := by
  intro z hz
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, rfl⟩ := hz
  refine ⟨?_, ?_⟩
  · intro i
    have := hMc (Pi.single (some i) 1) (by
      intro x hx; simpa [single_dotProduct] using (hK hx).1 i) _ (ls_Qd none)
    simpa [single_dotProduct] using this
  · intro i j hij
    have := hMc (Pi.single none 1 - Pi.single (some i) 1 - Pi.single (some j) 1) (by
      intro x hx
      simp only [sub_dotProduct, single_dotProduct, one_mul]
      linarith [(hK hx).2 i j hij]) _ (ls_Qd none)
    simp only [sub_dotProduct, single_dotProduct, one_mul] at this
    linarith

theorem iter_props {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (r : ℕ) :
    NplusIter r (FR G) ⊆ FR G ∧
    (∀ c : ℝ, 0 ≤ c → ∀ z ∈ NplusIter r (FR G), c • z ∈ NplusIter r (FR G)) ∧
    (∀ S : Set V, ∀ z ∈ NplusIter r (FR G), Dop S z ∈ NplusIter r (FR G)) := by
  induction r with
  | zero =>
    refine ⟨le_rfl, ?_, ?_⟩
    · intro c hc z hz
      refine ⟨fun i => ?_, fun i j h => ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc (hz.1 i)
      · simp only [Pi.smul_apply, smul_eq_mul]
        have := hz.2 i j h
        nlinarith
    · intro S z hz
      have hle : ∀ i, Dop S z (some i) ≤ z (some i) := by
        intro i; simp only [Dop]
        rcases dS_01 S (some i) with h | h <;> rw [h] <;> linarith [hz.1 i]
      refine ⟨fun i => ?_, fun i j h => ?_⟩
      · simp only [Dop]
        rcases dS_01 S (some i) with h | h <;> rw [h] <;> linarith [hz.1 i]
      · have := hz.2 i j h
        have h0 : Dop S z none = z none := by simp [Dop, dS_none]
        linarith [hle i, hle j]
  | succ r ih =>
    refine ⟨N1plus_FR G _ ih.1, fun c hc => N1plus_smul _ c hc, fun S => N1plus_Dop S _ (ih.2.2 S)⟩

theorem ls_core {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b) (r : ℕ)
    (hcontract : ∀ v, 0 < a v → Valid (NplusG r G) (contractCoeff G a v) (b - a v)) :
    Valid (NplusG (r + 1) G) a b := by
  classical
  obtain ⟨hKFR, hKsmul, hKD⟩ := iter_props G r
  set K := NplusIter r (FR G) with hKdef
  intro x hx
  have hxFR : hom x ∈ FR G := (iter_props G (r + 1)).1 hx
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, hYx⟩ := hx
  let ap : V → ℝ := fun w => max (a w) 0
  let c : Option V → ℝ := fun o => Option.elim o b (fun w => -ap w)
  have hb : 0 ≤ b := by
    have := hvalid (chi ∅) (subset_convexHull ℝ _ ⟨∅, by simp, rfl⟩)
    simpa [chi] using this
  -- validity of the contracted positive part on K
  have hwf : ∀ v, 0 < a v → ∀ z ∈ K,
      ∑ w, contractCoeff G ap v w * z (some w) ≤ (b - a v) * z none := by
    intro v hv z hz
    let S : Set V := {w | a w < 0}
    have hz' : Dop S z ∈ K := hKD S z hz
    have hzFR := hKFR hz'
    have hD0 : Dop S z none = z none := by simp [Dop, dS_none]
    have hsum : ∑ w, contractCoeff G ap v w * z (some w) =
        ∑ w, contractCoeff G a v w * Dop S z (some w) := by
      apply Finset.sum_congr rfl; intro w _
      simp only [contractCoeff, Dop, dS, Option.elim, ap, S, Set.mem_setOf_eq]
      by_cases hw : a w < 0
      · simp [hw, max_eq_right hw.le]
      · push_neg at hw
        simp [not_lt.mpr hw, max_eq_left hw]
    rw [hsum]
    obtain ⟨w0, hw0⟩ := hG v
    have hz0 : 0 ≤ z none := by
      have := hzFR.2 v w0 hw0; rw [hD0] at this; linarith [hzFR.1 v, hzFR.1 w0]
    rcases lt_or_eq_of_le hz0 with hpos | hzero
    · let x' : V → ℝ := fun w => Dop S z (some w) / z none
      have hx' : x' ∈ NplusG r G := by
        show hom x' ∈ K
        have : hom x' = (z none)⁻¹ • Dop S z := by
          funext o
          cases o with
          | none => simp [hom, hD0, hpos.ne']
          | some w => simp [hom, x', div_eq_inv_mul]
        rw [this]; exact hKsmul _ (inv_nonneg.mpr hz0) _ hz'
      have := hcontract v hv x' hx'
      simp only [x'] at this
      have heq : ∑ w, contractCoeff G a v w * Dop S z (some w) =
          z none * ∑ w, contractCoeff G a v w * (Dop S z (some w) / z none) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _
        field_simp
      rw [heq]
      nlinarith
    · have hall : ∀ w, Dop S z (some w) = 0 := by
        intro w
        obtain ⟨w1, hw1⟩ := hG w
        have := hzFR.2 w w1 hw1
        rw [hD0, ← hzero] at this
        linarith [hzFR.1 w, hzFR.1 w1]
      simp [hall, ← hzero]
  -- columns
  have hcol : ∀ v, 0 < a v → 0 ≤ c ⬝ᵥ (Y *ᵥ Pi.single (some v) 1) := by
    intro v hv
    set y := Y *ᵥ Pi.single (some v) 1 with hydef
    have hy : ∀ u ∈ dualCone K, 0 ≤ u ⬝ᵥ y := fun u hu => hMc u hu _ (ls_Qd _)
    have hyv : y (some v) = y none := by
      simp [hydef, mulVec_single_one, hdiag v]
    have hyw : ∀ w, 0 ≤ y (some w) := by
      intro w
      have := hy (Pi.single (some w) 1) (by
        intro z hz; simpa [single_dotProduct] using (hKFR hz).1 w)
      simpa [single_dotProduct] using this
    have hyadj : ∀ w, G.Adj v w → y (some w) = 0 := by
      intro w hvw
      have := hy (Pi.single none 1 - Pi.single (some v) 1 - Pi.single (some w) 1) (by
        intro z hz
        simp only [sub_dotProduct, single_dotProduct, one_mul]
        linarith [(hKFR hz).2 v w hvw])
      simp only [sub_dotProduct, single_dotProduct, one_mul] at this
      linarith [hyw w]
    let wf : Option V → ℝ := fun o => Option.elim o (b - a v) (fun w => -contractCoeff G ap v w)
    have hwfK : wf ∈ dualCone K := by
      intro z hz
      have := hwf v hv z hz
      simp only [dotProduct, Fintype.sum_option, wf, Option.elim]
      simp only [neg_mul, Finset.sum_neg_distrib]
      linarith
    have h1 := hy wf hwfK
    have hkey : ∑ w, (ap w - contractCoeff G ap v w) * y (some w) = a v * y (some v) := by
      rw [Finset.sum_eq_single v]
      · simp [contractCoeff, ap, max_eq_left hv.le]
      · intro w _ hwv
        by_cases hadj : G.Adj v w
        · simp [hyadj w hadj]
        · simp [contractCoeff, hwv, hadj]
      · simp
    have e1 : c ⬝ᵥ y = b * y none + ∑ w, -ap w * y (some w) := by
      simp [dotProduct, Fintype.sum_option, c]
    have e2 : wf ⬝ᵥ y = (b - a v) * y none + ∑ w, -contractCoeff G ap v w * y (some w) := by
      simp [dotProduct, Fintype.sum_option, wf]
    have e3 : ∑ w, -ap w * y (some w) = ∑ w, -contractCoeff G ap v w * y (some w)
        - ∑ w, (ap w - contractCoeff G ap v w) * y (some w) := by
      rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro w _; ring
    rw [e1, e3, hkey]
    rw [e2] at h1
    rw [hyv]; linarith
  -- PSD argument
  have hnn : 0 ≤ c ⬝ᵥ (Y *ᵥ c) := by simpa using hpsd.dotProduct_mulVec_nonneg c
  have hterm : ∀ v : V, c (some v) * (c ⬝ᵥ (Y *ᵥ Pi.single (some v) 1)) ≤ 0 := by
    intro v
    by_cases hv : 0 < a v
    · have : c (some v) = -a v := by simp [c, ap, max_eq_left hv.le]
      rw [this]; nlinarith [hcol v hv]
    · push_neg at hv
      have : c (some v) = 0 := by simp [c, ap, max_eq_right hv]
      rw [this, zero_mul]
  have hsumt : ∑ v : V, c (some v) * (c ⬝ᵥ (Y *ᵥ Pi.single (some v) 1)) ≤ 0 :=
    Finset.sum_nonpos (fun v _ => hterm v)
  have hc0 : c none = b := rfl
  rw [ls_exp, Fintype.sum_option, hc0] at hnn
  have hmain : 0 ≤ c ⬝ᵥ (Y *ᵥ Pi.single none 1) := by
    rcases lt_or_eq_of_le hb with hbpos | hbzero
    · by_contra hneg; push_neg at hneg
      have : b * (c ⬝ᵥ (Y *ᵥ Pi.single none 1)) < 0 := mul_neg_of_pos_of_neg hbpos hneg
      linarith
    · have hz : c ⬝ᵥ (Y *ᵥ c) = 0 := by
        rw [ls_exp, Fintype.sum_option, hc0, ← hbzero, zero_mul, zero_add]
        rw [← hbzero, zero_mul, zero_add] at hnn
        linarith
      have hYc : Y *ᵥ c = 0 := (hpsd.dotProduct_mulVec_zero_iff c).mp (by simpa using hz)
      rw [dotProduct_mulVec, ← mulVec_transpose, hsym.eq, hYc, zero_dotProduct]
  rw [hYx] at hmain
  have e : c ⬝ᵥ hom x = b - ∑ w, ap w * x w := by
    simp [dotProduct, Fintype.sum_option, c, hom]; ring
  rw [e] at hmain
  have : ∑ i, a i * x i ≤ ∑ w, ap w * x w := by
    apply Finset.sum_le_sum; intro i _
    have hxi : 0 ≤ x i := hxFR.1 i
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hxi
  linarith

end LovaszSchrijver.NPlus

open LovaszSchrijver.NPlus


theorem solution {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : ∀ v, ∃ w, G.Adj v w)
    (a : V → ℝ) (b : ℝ) (hvalid : Valid (STAB G) a b) (r : ℕ)
    (hcontract : ∀ v, 0 < a v → Valid (NplusG r G) (contractCoeff G a v) (b - a v)) :
    Valid (NplusG (r + 1) G) a b := by
  exact ls_core G hG a b hvalid r hcontract
