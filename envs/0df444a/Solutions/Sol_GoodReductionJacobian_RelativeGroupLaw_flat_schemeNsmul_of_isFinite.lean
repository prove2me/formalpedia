-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/fe929ee8-11ff-5e2d-b8e0-871f7978243c

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_SchemeFibreEndo
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_fibrewiseFlat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeFibreEndo_schemeNsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe RegularLocalRingQuotientAscent.dualNumberFst_apply"

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

set_option maxHeartbeats 3200000 in
theorem solution
    {R : Type} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : 0 < n) (hfin : IsFinite (L.schemeNsmul n)) :
    Flat (L.schemeNsmul n) := by
  exact L.flat_schemeNsmul_of_fibrewiseFlat hJ n hn
    (fun s => L.flat_schemeFibreEndo_schemeNsmul hJ n hn hfin s)

end S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite (solution)
