-- Prove2me | solution 1 for GlobalTheory.AffineComplement.exists_nonzeroLocus_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:32:52.036801+00:00
-- url     : https://prove2.me/submissions/6b65bf35-f6c3-41f9-8578-d1c468ebd68d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowMulMemRangeOfLocalDenominators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNonzeroLocusEqAffineOpenLocallyFactorial
import Theorems.Thm_GlobalTheory_AffineComplement_effCartier_of_stalkId_of_isLocallyNoetherian
import Theorems.Thm_GlobalTheory_AffineComplement_exists_radical_span_singleton_eq
import Theorems.Thm_GlobalTheory_AffineComplement_stalkId_vanishingIdeal_compl
import Theorems.Thm_GlobalTheory_Descent_freeIso_hom
import Theorems.Thm_GlobalTheory_EffCartierData_exists_idealSheaf_eq
import Theorems.Thm_GlobalTheory_GrSum_map_of
import Theorems.Thm_GlobalTheory_Wick_dividedContraction_one
import Theorems.Thm_GlobalTheory_exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization
import Theorems.Thm_GlobalTheory_locCubeMap_app_toLocCube
import Theorems.Thm_GlobalTheory_locCubeMap_id
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Descent.freeIso_hom
attribute [local simp] GlobalTheory.GrSum.map_of
attribute [local simp] GlobalTheory.Wick.dividedContraction_one
attribute [local simp] GlobalTheory.locCubeMap_app_toLocCube
attribute [local simp] GlobalTheory.locCubeMap_id



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AffineComplement
open ReciprocityTheory.AnForm.R
namespace GlobalTheory.AffineComplement
theorem _root_.solution : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [X.IsSeparated] (U : X.Opens), IsAffineOpen U → (U : Set X).Nonempty → (∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) → ∃ (L : LB X) (σ : LB.Sec L), L.IsLB ∧ nonzeroLocus σ = U := by
  intro X _ _ _ U hU hne hufd
  have hι : IsAffineHom U.ι :=
    haveI : IsAffine U := hU
    haveI : IsAffineHom (U.ι ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  have hE : FinalTheorems.EffCartier (Scheme.IdealSheafData.vanishingIdeal U.compl) := by
    refine effCartier_of_stalkId_of_isLocallyNoetherian _ fun x => ?_
    haveI := hufd x
    have hd : IsDomain (X.presheaf.stalk x) := inferInstance
    have hn : IsNoetherianRing (X.presheaf.stalk x) := inferInstance
    have hA : IsAffineOpen (X.fromSpecStalk x ⁻¹ᵁ U) := by
      have : IsAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι :=
        MorphismProperty.of_isPullback (P := @IsAffineHom)
          (isPullback_morphismRestrict (X.fromSpecStalk x) U) hι
      exact isAffine_of_isAffineHom (X.fromSpecStalk x ⁻¹ᵁ U).ι
    have hg : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact (genericPoint_spec X).specializes trivial
    obtain ⟨q, hq⟩ := hg
    have hqU : q ∈ X.fromSpecStalk x ⁻¹ᵁ U := by
      change X.fromSpecStalk x q ∈ U
      rw [hq]
      exact ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
    obtain ⟨a, ha⟩ := @GlobalTheory.exists_eq_basicOpen_of_isAffineOpen_of_uniqueFactorization (X.presheaf.stalk x) (X.presheaf.stalk x).commRing hd hn (hufd x)
      (X.fromSpecStalk x ⁻¹ᵁ U) hA ⟨q, hqU⟩
    have h : ∀ q : PrimeSpectrum (X.presheaf.stalk x),
        X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal := fun q =>
      iff_of_eq (congrArg (fun V => q ∈ V) ha)
    have ha0 : a ≠ 0 := fun h0 => (h q).1 hqU (h0 ▸ zero_mem _)
    rw [stalkId_vanishingIdeal_compl U x a h]
    exact exists_radical_span_singleton_eq ha0
  obtain ⟨D, hD⟩ := EffCartierData.exists_idealSheaf_eq hE
  refine ⟨D.lb, D.canonical, D.isLB_lb, TopologicalSpace.Opens.ext ?_⟩
  refine D.coe_nonzeroLocus_canonical.trans ?_
  rw [hD]
  exact compl_compl _
end GlobalTheory.AffineComplement
