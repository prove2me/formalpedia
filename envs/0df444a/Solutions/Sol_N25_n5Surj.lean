-- Prove2me | solution 1 for N25.n5Surj
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:46:02.314012+00:00
-- url     : https://prove2.me/submissions/fb0b9f3f-140b-40be-a9e6-77ef736ec3e1

import Mathlib
import Definitions.Def_N25_LocalFiveCondition
import Theorems.Thm_N25_exists_ratPointModel
import Definitions.Def_N25_RatPointModel
import Theorems.Thm_N25_RatPointModel_exists_localRealization
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_N25_RatPointModel_localRealization_saturated
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
import Theorems.Thm_N25_LocalFive_exists_finite_quotient_surjective_71_nsmul
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_N25_LocalFive_finite_quotient_and_surjective_nsmul_comap

set_option autoImplicit false

noncomputable section

namespace N25

local instance instL_N25_n5Surj_bfd51b_s2ee859 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The literal local fixed subgroup inherits finite-index division by seventy-one
from the retained model through its saturated realization. -/
theorem _root_.solution : N5Surj := by
  obtain ⟨D⟩ := exists_ratPointModel
  obtain ⟨e, he, _, himage⟩ := D.exists_localRealization
  obtain ⟨U, hfin, hsurj⟩ :=
    LocalFive.exists_finite_quotient_surjective_71_nsmul D.G D.abelian D.comm
  exact ⟨U.comap e, LocalFive.finite_quotient_and_surjective_nsmul_comap e he 71
    (D.localRealization_saturated e himage) U hfin hsurj⟩

end N25
