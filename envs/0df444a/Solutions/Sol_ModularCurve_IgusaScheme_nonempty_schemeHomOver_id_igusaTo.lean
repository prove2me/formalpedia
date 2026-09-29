-- Prove2me | solution 1 for ModularCurve.IgusaScheme.nonempty_schemeHomOver_id_igusaTo
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/fd3ec5ae-d6b6-52f3-b747-d6361098fa20

import Theorems.Thm_ModularCurve_IgusaScheme_nonempty_algHom_chartAlgInf
import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_IgusaScheme_nonempty_schemeHomOver_id_igusaTo
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))))
      (igusaTo N ℓ)) := by
  obtain ⟨cuspHom⟩ := ModularCurve.IgusaScheme.nonempty_algHom_chartAlgInf N ℓ
  have hcomp : cuspHom.toRingHom.comp
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ↥(chartAlgInf N ℓ)) =
      RingHom.id ↥(GaloisRep.ratLocalizedAt ℓ) := by
    ext x
    simpa using cuspHom.commutes x
  refine ⟨⟨Spec.map (CommRingCat.ofHom cuspHom.toRingHom) ≫ ιInf N ℓ, ?_⟩⟩
  rw [Category.assoc, ιInf_igusaTo, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
  simp

end S_ModularCurve_IgusaScheme_nonempty_schemeHomOver_id_igusaTo
end P2MW
export P2MW.S_ModularCurve_IgusaScheme_nonempty_schemeHomOver_id_igusaTo (solution)
