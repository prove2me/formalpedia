-- Prove2me | solution 1 for GlobalTheory.QuasiFiniteFibreFlat.flat_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:41:20.661919+00:00
-- url     : https://prove2.me/submissions/99ac4099-68f7-4d3c-90b2-b1b659694426

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatOfQuasiFiniteOfFlatFibres
import Theorems.Thm_GlobalTheory_QuasiFiniteFibreFlat_flat_baseChange_trans
import Theorems.Thm_GlobalTheory_FiniteFibreFlat_flat_of_flat_fibres
import Theorems.Thm_GlobalTheory_FinitePresFibreFlat_flat_of_flat_fibres
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
open GlobalTheory.QuasiFiniteFibreFlat
namespace GlobalTheory.QuasiFiniteFibreFlat
theorem _root_.solution {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B]
    [hRB : Module.Flat R B]
    (H : ∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C),
      (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B))
    (A' : Type) [CommRing A'] [Algebra A A'] [Module.Flat A A'] (e : A' ⊗[A] B)
    [Module.Finite A' (Localization.Away e)] : Module.Flat A' (Localization.Away e) := by
  let D := Localization.Away e
  letI : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Flat (A' ⊗[A] B) D := IsLocalization.flat _ (Submonoid.powers e)
  haveI : Algebra.FinitePresentation (A' ⊗[A] B) D := IsLocalization.Away.finitePresentation e
  haveI : Algebra.FinitePresentation A' D := .trans A' (A' ⊗[A] B) D
  haveI : Module.FinitePresentation A' D :=
    Module.FinitePresentation.of_finite_of_finitePresentation A' D
  haveI : Module.Flat R D := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    have h2 := h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
    have h3 := ((RingHom.flat_algebraMap_iff.mpr hRB).comp h2).comp
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A' ⊗[A] B) D))
    rw [← RingHom.flat_algebraMap_iff]
    convert h3 using 1
    ext r
    rw [IsScalarTower.algebraMap_apply R A' D]
    change algebraMap A' D (algebraMap A A' (algebraMap R A r)) =
      algebraMap (A' ⊗[A] B) D (1 ⊗ₜ algebraMap R B r)
    rw [IsScalarTower.algebraMap_apply A' (A' ⊗[A] B) D, IsScalarTower.algebraMap_apply R A B,
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul _
  refine FinitePresFibreFlat.flat_of_flat_fibres (R := R) (A := A') (B := D)
    fun k C _ _ _ t h w => ?_
  letI : Algebra A C := ((algebraMap A' C).comp (algebraMap A A')).toAlgebra
  haveI : IsScalarTower A A' C := IsScalarTower.of_algebraMap_eq' rfl
  haveI := H k C t h w
  haveI : Module.Flat C (C ⊗[A'] (A' ⊗[A] B)) :=
    Module.Flat.of_linearEquiv (AlgebraTensorModule.cancelBaseChange A A' C C B)
  exact flat_baseChange_trans A' C (A' ⊗[A] B) D
end GlobalTheory.QuasiFiniteFibreFlat
