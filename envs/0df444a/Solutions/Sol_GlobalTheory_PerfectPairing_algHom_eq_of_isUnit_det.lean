-- Prove2me | solution 1 for GlobalTheory.PerfectPairing.algHom_eq_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:34:20.291825+00:00
-- url     : https://prove2.me/submissions/94391ec4-728c-43fa-bab5-d4139ee8d537

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
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_GlobalTheory_restrictPoints_val
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
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
theorem _root_.solution {H S : Type} [CommRing H] [Algebra O H] [CommRing S] [Algebra O S] {r : ℕ}
    (b : Module.Basis (Fin r) O H) (D : Matrix (Fin r) (Fin r) O) (hD : IsUnit D.det) (φ φ' : H →ₐ[O] S)
    (h : ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (φ' (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j)) : φ = φ' := by
  have key : ∀ ψ : H →ₐ[O] S,
      ∑ i, ∑ j, algebraMap O (S ⊗[O] H) (D i j) * (ψ (b i) ⊗ₜ[O] (1 : H)) * ((1 : S) ⊗ₜ[O] b j) =
        ∑ j, (Matrix.vecMul (fun i => ψ (b i)) (D.map (algebraMap O S)) j) • Algebra.TensorProduct.basis S b j := by
    intro ψ
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.vecMul, dotProduct, Finset.sum_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Algebra.TensorProduct.algebraMap_apply, TensorProduct.smul_tmul', mul_comm]
  rw [key, key] at h
  have h1 := (Algebra.TensorProduct.basis S b).equivFun.symm.injective
    (((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).trans
      (h.trans ((Algebra.TensorProduct.basis S b).equivFun_symm_apply _).symm))
  have hD' : IsUnit (D.map (algebraMap O S)) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    have := hD.map (algebraMap O S)
    rwa [RingHom.map_det] at this
  have h2 := (Matrix.vecMul_injective_of_isUnit hD') h1
  exact AlgHom.toLinearMap_injective (b.ext fun i => congrFun h2 i)
end GlobalTheory.PerfectPairing
