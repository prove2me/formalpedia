-- Prove2me | solution 1 for GlobalTheory.PerfectPairing.exists_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:52:41.240212+00:00
-- url     : https://prove2.me/submissions/74566cdc-bbcb-41fd-be4a-6211a3e33772

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
import Theorems.Thm_GlobalTheory_PerfectPairing_Val_exists
import Theorems.Thm_GlobalTheory_PerfectPairing_Val_comp
import Theorems.Thm_GlobalTheory_TangentPow_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_TorsionTheta_ptMap_comp_ptMap
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.PerfectPairing
variable {O : Type} [CommRing O]
variable {A : Over (Sp O)} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L) (n : ℕ)
  {S S' : Type} [CommRing S] [Algebra O S] [CommRing S'] [Algebra O S']
variable {c n} {x x' y y' : specO O S ⟶ A} {s s' : S}
namespace GlobalTheory.PerfectPairing
theorem _root_.solution (c : CubicalStr A L) {H : Type} [CommRing H] [Algebra O H] {r : ℕ} (b : Module.Basis (Fin r) O H)
    {y : specO O H ⟶ A} (hy : y ^ n = 1) :
    ∃ D : Matrix (Fin r) (Fin r) O, ∀ (S : Type) [CommRing S] [Algebra O S] (φ ψ : H →ₐ[O] S),
      Val c n (ptMap φ ≫ y) (ptMap ψ ≫ y) (∑ i, ∑ j, algebraMap O S (D i j) * φ (b i) * ψ (b j)) := by
  have hz : ∀ χ : H →ₐ[O] H ⊗[O] H, (ptMap χ ≫ y) ^ n = 1 := fun χ => by
    rw [← MonObj.comp_pow, hy, MonObj.comp_one]
  obtain ⟨e, he⟩ := Val.exists (c := c) (hz Algebra.TensorProduct.includeLeft) (hz Algebra.TensorProduct.includeRight)
  refine ⟨fun i j => (b.tensorProduct b).repr e (i, j), fun S _ _ φ ψ => ?_⟩
  have h := he.comp (Algebra.TensorProduct.productMap φ ψ)
  rw [← Category.assoc, ← Category.assoc, TangentPow.ptMap_comp_ptMap, TangentPow.ptMap_comp_ptMap,
    Algebra.TensorProduct.productMap_left, Algebra.TensorProduct.productMap_right] at h
  convert h using 1
  conv_rhs => rw [← (b.tensorProduct b).sum_repr e]
  rw [map_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Module.Basis.tensorProduct_apply, Algebra.TensorProduct.productMap_apply_tmul, Algebra.smul_def,
    _root_.mul_assoc]
end GlobalTheory.PerfectPairing
