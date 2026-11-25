-- Prove2me | solution 1 for GlobalTheory.AffineComplement.stalkId_vanishingIdeal_compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:04.376765+00:00
-- url     : https://prove2.me/submissions/05e93ce2-f7de-4753-a1ba-6b4f3ff1c744

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Landherr__DimEqZero_40b4adf5f58b53e3
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsPowMulMemRangeOfLocalDenominators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsNonzeroLocusEqAffineOpenLocallyFactorial
import Theorems.Thm_ReciprocityTheory_AnForm_R_ds_stalkId_eq_map


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
open GlobalTheory GlobalTheory.AffineComplement
open ReciprocityTheory.AnForm.R
namespace GlobalTheory.AffineComplement
theorem _root_.solution {X : Scheme.{0}} (U : X.Opens) (x : X)
    (a : X.presheaf.stalk x)
    (h : ∀ q : PrimeSpectrum (X.presheaf.stalk x), X.fromSpecStalk x q ∈ U ↔ a ∉ q.asIdeal) :
    FinalTheorems.stalkId (Scheme.IdealSheafData.vanishingIdeal U.compl) x = (Ideal.span {a}).radical := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  have hcl : IsClosed (X := PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) :=
    U.compl.isClosed.preimage hW.fromSpec.continuous
  generalize hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (U.compl : Set X)) = J
  have hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (U.compl : Set X) := by
    rw [← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]
    rfl
  have hr : J.radical = J := hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  change J.map (algebraMap Γ(X, W) (X.presheaf.stalk x)) = _
  rw [← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
    ← PrimeSpectrum.zeroLocus_eq_iff]
  ext q
  have e : X.fromSpecStalk x q =
      hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q) := by
    rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rw [PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe,
    SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem,
    ← not_iff_not, ← h, e]
  have := Set.ext_iff.1 hz (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q)
  exact (not_congr this).trans not_not
end GlobalTheory.AffineComplement
