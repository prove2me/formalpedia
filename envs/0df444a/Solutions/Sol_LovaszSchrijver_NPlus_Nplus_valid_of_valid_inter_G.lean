-- Prove2me | solution 1 for LovaszSchrijver.NPlus.Nplus_valid_of_valid_inter_G
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:42:20.44599+00:00
-- url     : https://prove2.me/submissions/aaca0382-d0cb-45e7-979d-271a05d9f6af

import Mathlib
import Definitions.Def_LovaszSchrijver_NPlus_MatrixCone



namespace LovaszSchrijver.NPlus

open Matrix

theorem nv_bipolar {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (z : Option ι → ℝ) (hz : ∀ u ∈ dualCone K, 0 ≤ u ⬝ᵥ z) : z ∈ K := by
  by_contra hzK
  obtain ⟨⟨x0, hx0⟩, hadd, hsmul⟩ := hK
  have hconv : Convex ℝ K := by
    intro x hx y hy s t hs ht _
    exact hadd _ (hsmul s hs x hx) _ (hsmul t ht y hy)
  obtain ⟨f, u, hfK, hfz⟩ := geometric_hahn_banach_closed_point hconv hKc hzK
  have h0K : (0 : Option ι → ℝ) ∈ K := by simpa using hsmul 0 le_rfl x0 hx0
  have hu : 0 < u := by simpa using hfK 0 h0K
  have hfle : ∀ y ∈ K, f y ≤ 0 := by
    intro y hy
    by_contra hpos
    push_neg at hpos
    have := hfK _ (hsmul (u / f y) (div_nonneg hu.le hpos.le) y hy)
    rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hpos.ne'] at this
    exact lt_irrefl _ this
  let w : Option ι → ℝ := fun j => -f (Pi.single j 1)
  have hw : ∀ y, w ⬝ᵥ y = -f y := by
    intro y
    have hy : y = ∑ j, y j • (Pi.single j (1 : ℝ) : Option ι → ℝ) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_rhs => rw [hy]
    rw [map_sum, ← Finset.sum_neg_distrib]
    simp only [dotProduct, w, map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl; intro j _; ring
  have hwK : w ∈ dualCone K := by
    intro y hy; rw [hw]; linarith [hfle y hy]
  have := hz w hwK
  rw [hw] at this
  linarith

theorem nv_Qnonneg {ι : Type} (q : Option ι → ℝ) (hq : q ∈ (Q : Set (Option ι → ℝ))) (j : Option ι) :
    0 ≤ q j := by
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

theorem nv_core {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKc : IsClosed K)
    (a : Option ι → ℝ) (ha : ∀ i : ι, a (some i) ≤ 0) (ha₀ : 0 ≤ a none)
    (hvalid : ∀ i : ι, a (some i) < 0 → ∀ x ∈ K ∩ G i, 0 ≤ a ⬝ᵥ x) :
    ∀ x ∈ N1plus K, 0 ≤ a ⬝ᵥ x := by
  intro x hx
  obtain ⟨Y, ⟨⟨hsym, hdiag, hMc⟩, hpsd⟩, rfl⟩ := hx
  have hQd : ∀ j, (Pi.single j (1:ℝ) : Option ι → ℝ) ∈ dualCone (Q : Set (Option ι → ℝ)) := by
    intro j q hq
    simpa [single_dotProduct] using nv_Qnonneg q hq j
  have hcolK : ∀ j, Y *ᵥ Pi.single j 1 ∈ K := by
    intro j
    apply nv_bipolar K hK hKc
    intro u hu
    exact hMc u hu _ (hQd j)
  have hcolG : ∀ i : ι, Y *ᵥ Pi.single (some i) 1 ∈ G i := by
    intro i
    show (Y *ᵥ Pi.single (some i) 1) (some i) = (Y *ᵥ Pi.single (some i) 1) none
    simp [mulVec_single_one, hdiag i]
  have hexp : a ⬝ᵥ (Y *ᵥ a) = ∑ j, a j * (a ⬝ᵥ (Y *ᵥ Pi.single j 1)) := by
    simp only [mulVec_single_one]
    simp only [dotProduct, mulVec, Matrix.col, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro j _
    apply Finset.sum_congr rfl; intro k _
    simp [transpose_apply]; ring
  have hnn : 0 ≤ a ⬝ᵥ (Y *ᵥ a) := by simpa using hpsd.dotProduct_mulVec_nonneg a
  have hterm : ∀ i : ι, a (some i) * (a ⬝ᵥ (Y *ᵥ Pi.single (some i) 1)) ≤ 0 := by
    intro i
    rcases lt_or_eq_of_le (ha i) with h | h
    · exact mul_nonpos_of_nonpos_of_nonneg h.le (hvalid i h _ ⟨hcolK _, hcolG i⟩)
    · rw [h, zero_mul]
  rw [hexp, Fintype.sum_option] at hnn
  have hsum : ∑ i : ι, a (some i) * (a ⬝ᵥ (Y *ᵥ Pi.single (some i) 1)) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => hterm i)
  rcases lt_or_eq_of_le ha₀ with h0 | h0
  · by_contra hneg
    push_neg at hneg
    have : a none * (a ⬝ᵥ (Y *ᵥ Pi.single none 1)) < 0 := mul_neg_of_pos_of_neg h0 hneg
    linarith
  · have hz : a ⬝ᵥ (Y *ᵥ a) = 0 := by
      rw [hexp, Fintype.sum_option, ← h0, zero_mul, zero_add]
      rw [← h0, zero_mul, zero_add] at hnn
      linarith
    have hYa : Y *ᵥ a = 0 := (hpsd.dotProduct_mulVec_zero_iff a).mp (by simpa using hz)
    rw [dotProduct_mulVec, ← mulVec_transpose, hsym.eq, hYa, zero_dotProduct]

end LovaszSchrijver.NPlus

open LovaszSchrijver.NPlus


theorem solution {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : Set (Option ι → ℝ)) (hK : IsConvexCone K) (hKQ : K ⊆ Q) (hKc : IsClosed K)
    (a : Option ι → ℝ) (ha : ∀ i : ι, a (some i) ≤ 0) (ha₀ : 0 ≤ a none)
    (hvalid : ∀ i : ι, a (some i) < 0 → ∀ x ∈ K ∩ G i, 0 ≤ a ⬝ᵥ x) :
    ∀ x ∈ N1plus K, 0 ≤ a ⬝ᵥ x := by
  exact nv_core K hK hKc a ha ha₀ hvalid
