-- Prove2me | solution 1 for GlobalTheory.PerfectPairing.isReduced_rep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:24:33.939099+00:00
-- url     : https://prove2.me/submissions/1ccd5f26-6538-4c30-a235-da1f5e78fee3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubWeilOneLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsReducedTorsionGeometricFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_FinRepExistsIsPullbackSpec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAlgHomLocalizationAugmentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CardAlgHomReducedTraceSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsUnitDetPairingOfBicharacterOfDvdTraceStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubWeilPerfectOfGeneric
import Theorems.Thm_GlobalTheory_TangentPow_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_TorsionReduced_eq_const_of_pow_eq_one
import Theorems.Thm_GlobalTheory_TorsionReduced_isReduced_of_forall_dualNumber
import Theorems.Thm_GlobalTheory_TorsionTheta_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_CubWeil_unique
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_TorusCompat_unique
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]
namespace GlobalTheory.PerfectPairing
theorem _root_.solution {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {n : ℕ} {H : Type} [CommRing H] [Algebra O H]
    [Module.Finite O H] {y : specO O H ⟶ A} (hy : y ^ n = 1)
    (hu : ∀ (S : Type) [CommRing S] [Algebra O S] (z : specO O S ⟶ A), z ^ n = 1 →
      ∃! φ : H →ₐ[O] S, ptMap φ ≫ y = z)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra O F] (hn : (n : F) ≠ 0) : _root_.IsReduced (F ⊗[O] H) := by
  refine TorsionReduced.isReduced_of_forall_dualNumber F _ fun φ b => ?_
  let χ : H →ₐ[O] DualNumber F := (φ.restrictScalars O).comp Algebra.TensorProduct.includeRight
  have hz : (ptMap χ ≫ y) ^ n = 1 := by rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  have h2 := TorsionReduced.eq_const_of_pow_eq_one hn.isUnit _ hz
  simp only [← Category.assoc] at h2
  rw [TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap] at h2
  have h4 := (hu _ _ hz).unique rfl h2.symm
  have h5 : ∀ a, (χ a).snd = 0 := fun a => by
    have := congrArg TrivSqZeroExt.snd (congrArg (fun f => f a) h4)
    simpa using this
  induction b with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | tmul f a =>
    have : f ⊗ₜ[O] a = f • ((1 : F) ⊗ₜ[O] a) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [this, map_smul, TrivSqZeroExt.snd_smul]
    exact smul_eq_zero_of_right f (h5 a)
end GlobalTheory.PerfectPairing
