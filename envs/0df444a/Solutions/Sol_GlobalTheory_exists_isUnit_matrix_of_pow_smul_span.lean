-- Prove2me | solution 1 for GlobalTheory.exists_isUnit_matrix_of_pow_smul_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:33:21.764884+00:00
-- url     : https://prove2.me/submissions/f45794a6-8e48-45b8-8ef9-f7e0ec3cde7c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsUnitMatrixOfPowSmulSpanInvert
import Theorems.Thm_GlobalTheory_eq_zero_of_sum_smul_eq_zero_of_powDenom
import Theorems.Thm_GlobalTheory_exists_coeff_powDenom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (S EE W RW Y : Type) [CommRing S] [CommRing EE] [CommRing W] [CommRing RW] [AddCommGroup Y] [Module RW Y] (a : S →+* EE) (ι : EE →+* RW) (c : W →+* RW) (ψ : S →+* W) (Q : S), Function.Injective ι → (∀ s, ι (a s) = c (ψ s)) → IsUnit (a Q) → ∀ (q : ℕ) (x z : Fin q → Y), (∀ w : Fin q → W, ∑ i, c (w i) • x i = 0 → w = 0) → (∀ j, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • z j = ∑ i, c (ψ (s i)) • x i) → (∀ i, ∃ (k : ℕ) (s : Fin q → S), c (ψ Q) ^ k • x i = ∑ j, c (ψ (s j)) • z j) → ∃ A : Matrix (Fin q) (Fin q) EE, IsUnit A ∧ ∀ j, z j = ∑ i, ι (A i j) • x i := by
  intro S EE W RW Y _ _ _ _ _ _ a ι c ψ Q hι hc hQ q x z hx hz hx'
  choose A hAm hA using fun j => exists_coeff_powDenom a ι c ψ Q hc hQ x (z j) (hz j)
  choose B hBm hB using fun i => exists_coeff_powDenom a ι c ψ Q hc hQ z (x i) (hx' i)
  refine ⟨Matrix.of fun i j => A j i, ?_, fun j => by simpa using hA j⟩
  have hAB : (Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)
      = (1 : Matrix (Fin q) (Fin q) EE) := by
    ext m i
    rw [← sub_eq_zero]
    refine eq_zero_of_sum_smul_eq_zero_of_powDenom a ι c ψ Q hι hc hQ x hx
      (fun m => ((Matrix.of fun i j => A j i) * (Matrix.of fun j i => B i j)) m i
        - (1 : Matrix (Fin q) (Fin q) EE) m i) ?_ ?_ m
    · intro m
      refine sub_mem ?_ ?_
      · rw [Matrix.mul_apply]
        exact sum_mem fun j _ => mul_mem (hAm j m) (hBm i j)
      · rw [Matrix.one_apply]
        split_ifs
        · exact one_mem _
        · exact zero_mem _
    · simp only [map_sub, sub_smul, Finset.sum_sub_distrib]
      rw [sub_eq_zero]
      have h1 : ∑ m, ι ((1 : Matrix (Fin q) (Fin q) EE) m i) • x m = x i := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro m _ hm
          simp [Matrix.one_apply_ne hm]
        · simp
      rw [h1]
      conv_rhs => rw [hB i]
      simp only [Matrix.mul_apply, Matrix.of_apply, map_sum, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hA j, Finset.smul_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_mul, mul_comm, mul_smul]
  exact (Matrix.isUnit_iff_isUnit_det _).2 (Matrix.isUnit_det_of_right_inverse hAB)
end GlobalTheory
