-- Prove2me | solution 1 for GlobalTheory.ProjSpace.isPullback_baseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:17:05.431817+00:00
-- url     : https://prove2.me/submissions/db2a3b46-9b1d-43a7-89e9-da6e8e9afca9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ProjDehomA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_AwayToSectionFromZero
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_TwistingSheafOneChartEqPreimageStandardChart
import Theorems.Thm_P2M_GlobalTheory_ProjSpace_chart__str_475cb27b7b18
import Theorems.Thm_P2M_GlobalTheory_ProjSpace_chart__baseChange_4f839b0b071b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi (LB res pullU)
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace resG lbPow LBIso)
open GlobalTheory.ProjFrac GlobalTheory.QCoh.Qcqs
attribute [local instance] MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.ProjSpace
variable (R : Type) [CommRing R] (N : ℕ)
variable {R N}
variable (R N)
variable {R N}
variable (R N)
variable {R} {R' : Type} [CommRing R'] (φ : R →+* R')
namespace GlobalTheory.ProjSpace
theorem _root_.solution :
    IsPullback (baseChange N φ) (PSpace.str R' N) (PSpace.str R N) (spMap φ) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (chartCover R N) fun (i : Fin (N + 1)) => ?_
  have h1 : IsPullback (chartι R' N i) (spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _))
      (baseChange N φ) (chartι R N i) :=
    (IsOpenImmersion.isPullback _ _ _ _ (chartι_baseChange N φ i)
      (by rw [opensRange_chartι, opensRange_chartι, baseChange_preimage_chart])).flip
  have h2 : IsPullback (spMap (MvPolynomial.map φ : MvPolynomial {j // j ≠ i} R →+* _))
      (chartι R' N i ≫ PSpace.str R' N) (chartι R N i ≫ PSpace.str R N) (spMap φ) := by
    rw [chartι_str, chartι_str]
    letI := φ.toAlgebra
    letI := MvPolynomial.algebraMvPolynomial (σ := {j // j ≠ i}) (R := R) (S := R')
    exact isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout R (MvPolynomial {j // j ≠ i} R) R' (MvPolynomial {j // j ≠ i} R'))
  exact h2.of_iso h1.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.comp_id _).trans (h1.isoPullback_hom_snd).symm)
    ((Category.comp_id _).trans (h1.isoPullback_hom_fst_assoc _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
end GlobalTheory.ProjSpace
