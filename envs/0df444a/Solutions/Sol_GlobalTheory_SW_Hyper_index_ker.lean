-- Prove2me | solution 1 for GlobalTheory.SW.Hyper.index_ker
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:52:09.234614+00:00
-- url     : https://prove2.me/submissions/c8a9616f-5cbb-4634-9aa3-87dabadf9e39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Theorems.Thm_GlobalTheory_SW_Hyper_surj_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Hyper
variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]
namespace GlobalTheory.SW.Hyper
theorem _root_.solution (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    (LinearMap.ker f).toAddSubgroup.index = Nat.card (O ⧸ P) := by
  obtain ⟨v, hv⟩ := surj_of_ne P f hf
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨r • v, ?_⟩
    rw [map_smul, hv, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have h := AddSubgroup.index_ker f.toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top] at h
  exact h
end GlobalTheory.SW.Hyper
