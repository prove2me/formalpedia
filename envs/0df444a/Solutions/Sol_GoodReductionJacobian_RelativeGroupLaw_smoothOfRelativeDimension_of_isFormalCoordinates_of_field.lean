-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.smoothOfRelativeDimension_of_isFormalCoordinates_of_field
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ea962f4d-ebf7-523f-8e35-42aa5431ac23

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth
import Theorems.Thm_CerednikDrinfeld_QM_exists_injective_range_isTangentVector_of_isFormalCoordinates
import Theorems.Thm_CerednikDrinfeld_QM_finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isFormalCoordinates_of_field
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM

theorem solution
    {K : Type} [Field K] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of K)} [Smooth f]
    (L : RelativeGroupLaw K f) {d : ℕ} (F : MvFormalGroup d K)
    (θ : RelativeGroupLaw.FormalCoordinates f d) (hθ : L.IsFormalCoordinates F θ) :
    SmoothOfRelativeDimension d f := by

  obtain ⟨n, hn⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth L

  obtain ⟨τ, -, hinj, hrange, hadd, hsmul⟩ :=
    CerednikDrinfeld.QM.exists_injective_range_isTangentVector_of_isFormalCoordinates L F θ hθ K
  have hfin :=
    CerednikDrinfeld.QM.finrank_eq_of_range_iff_isTangentVector_of_smoothOfRelativeDimension
      L n K (algebraMap K K) (Fin d → K) τ hinj hrange hadd hsmul
  rw [Module.finrank_fin_fun] at hfin
  subst hfin
  exact hn

end S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isFormalCoordinates_of_field
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_smoothOfRelativeDimension_of_isFormalCoordinates_of_field (solution)
