-- Prove2me | solution 1 for GlobalTheory.JR.DualLattice.box_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:12:43.386226+00:00
-- url     : https://prove2.me/submissions/5c328f83-3881-4c7c-810e-269fcd5fe577

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Theorems.Thm_GlobalTheory_JR_DualLattice_stdChar_key

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.DualLattice
variable {F : Type} [NontriviallyNormedField F]
variable {V : Type} [AddCommGroup V] [Module F V]
namespace GlobalTheory.JR.DualLattice
theorem _root_.solution [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) {ι : Type} [Fintype ι]
    (e e' : Module.Basis ι F V) (B : V → V → F)
    (hB : ∀ x y, B x y = ∑ i, e.repr x i * e'.repr y i) (t : F) (ht : t ≠ 0) (y : V) :
    y ∈ box e' ‖t⁻¹‖ (norm_nonneg _) ↔ ∀ x ∈ box e ‖t‖ (norm_nonneg _), ψ (B x y) = 1 := by
  classical
  have htp : 0 < ‖t‖ := norm_pos_iff.2 ht
  constructor
  · intro hy x hx
    apply hψ.1
    rw [hB]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [norm_mul]
    calc _ ≤ ‖t‖ * ‖t⁻¹‖ := mul_le_mul (hx i) (hy i) (norm_nonneg _) (norm_nonneg _)
      _ = 1 := by rw [← norm_mul, mul_inv_cancel₀ ht, norm_one]
  · intro h i
    have h1 : ‖t * e'.repr y i‖ ≤ 1 := by
      refine stdChar_key hψ _ fun c hc => ?_
      have hx : (c * t) • e i ∈ box e ‖t‖ (norm_nonneg _) := by
        intro j
        rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
        split_ifs
        · rw [smul_eq_mul, mul_one, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _) hc
        · simp
      have := h _ hx
      rw [hB, Finset.sum_eq_single i] at this
      · simpa [mul_assoc] using this
      · intro j _ hj
        simp [Finsupp.single_apply, hj.symm]
      · simp
    rw [norm_mul] at h1
    rw [norm_inv, ← one_div, le_div_iff₀ htp, mul_comm]
    exact h1
end GlobalTheory.JR.DualLattice
