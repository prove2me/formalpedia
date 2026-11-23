-- Prove2me | solution 1 for GlobalTheory.HopfQuot.tr_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:05.683829+00:00
-- url     : https://prove2.me/submissions/3619bde3-4952-4176-8b89-8bd2327a9e38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteFaithfullyFlatKer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HopfQuot
open TensorProduct
variable {A M ι : Type*} [CommRing A] [AddCommGroup M] [Module A M] [Fintype ι]
namespace GlobalTheory.HopfQuot
theorem _root_.solution (e : ι → M) (c : ι → M →ₗ[A] A) (h : ∀ m, ∑ i, c i m • e i = m)
    (φ ψ : M →ₗ[A] M) : tr e c (φ ∘ₗ ψ) = tr e c (ψ ∘ₗ φ) := by
  have key : ∀ φ ψ : M →ₗ[A] M, tr e c (φ ∘ₗ ψ) =
      ∑ i, ∑ j, c j (ψ (e i)) * c i (φ (e j)) := by
    intro φ ψ
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.comp_apply]
    conv_lhs => rw [← h (ψ (e i))]
    simp [map_sum]
  rw [key, key, Finset.sum_comm]
  simp [mul_comm]
end GlobalTheory.HopfQuot
