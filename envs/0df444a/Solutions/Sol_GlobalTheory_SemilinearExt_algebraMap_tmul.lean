-- Prove2me | solution 1 for GlobalTheory.SemilinearExt.algebraMap_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:04:13.803889+00:00
-- url     : https://prove2.me/submissions/74fa88d4-2a2d-4d94-9aa7-4531833c5737

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SemilinearExtensionBases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisTensor

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Module
open GlobalTheory GlobalTheory.SemilinearExt
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases
variable {O K K'' : Type} [CommRing O] [Field K] [Algebra O K] [IsFractionRing O K]
  [Field K''] [Algebra O K''] [Algebra K K''] [IsScalarTower O K K'']
  {Fm : Type} [AddCommGroup Fm] [Module K Fm] [Module O Fm] [IsScalarTower O K Fm]
namespace GlobalTheory.SemilinearExt
theorem _root_.solution (c : K) (m : Fm) :
    algebraMap K K'' c ⊗ₜ[O] m = (1 : K'') ⊗ₜ[O] (c • m) := by
  obtain ⟨⟨a, b⟩, hc⟩ := IsLocalization.mk'_surjective (nonZeroDivisors O) c
  dsimp only at hc
  subst hc
  have hb : algebraMap O K (b : O) ≠ 0 := (IsLocalization.map_units K b).ne_zero
  set m₀ : Fm := (algebraMap O K (b : O))⁻¹ • m with hm₀
  have h1 : (b : O) • m₀ = m := by
    rw [← algebraMap_smul K (b : O) m₀, hm₀, smul_smul, mul_inv_cancel₀ hb, one_smul]
  have h2 : IsLocalization.mk' K a b • m = (a : O) • m₀ := by
    rw [← algebraMap_smul K a m₀, hm₀, smul_smul, ← div_eq_mul_inv, IsFractionRing.mk'_eq_div]
  have h3 : (b : O) • algebraMap K K'' (IsLocalization.mk' K a b) = (a : O) • (1 : K'') := by
    rw [Algebra.smul_def, Algebra.smul_def, mul_one, IsScalarTower.algebraMap_apply O K K'' (b : O),
      IsScalarTower.algebraMap_apply O K K'' a, ← map_mul, IsLocalization.mk'_spec']
  calc algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] m
      = algebraMap K K'' (IsLocalization.mk' K a b) ⊗ₜ[O] ((b : O) • m₀) := by rw [h1]
    _ = ((b : O) • algebraMap K K'' (IsLocalization.mk' K a b)) ⊗ₜ[O] m₀ :=
        (TensorProduct.smul_tmul _ _ _).symm
    _ = ((a : O) • (1 : K'')) ⊗ₜ[O] m₀ := by rw [h3]
    _ = (1 : K'') ⊗ₜ[O] ((a : O) • m₀) := TensorProduct.smul_tmul _ _ _
    _ = (1 : K'') ⊗ₜ[O] (IsLocalization.mk' K a b • m) := by rw [h2]
end GlobalTheory.SemilinearExt
