-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/82562a96-e9da-54c1-a7bf-da13e24fb336

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardChartSections
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel"

p2m_open_scoped "MatrixGroups Polynomial AlgebraicGeometry.Polynomial"

set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (theta : ↥(chartAlgFin p (ΓM M H) hj) ≃ₐ[R p] ↥(chartAlgFin p (ΓM M H) hj))
    (hwchart : ιFin p (ΓM M H) hj ≫ 𝔛.w.hom = Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom) ≫ ιFin p (ΓM M H) hj)
    (a b : ↥(chartAlgFin p (ΓM M H) hj))
    (hab : Ideal.span {b} ⊔ Ideal.span {theta a} = ⊤)
    (𝔮 𝔮' : PrimeSpectrum ↥(chartAlgFin p (ΓM M H) hj)) (ha : a ∈ 𝔮.asIdeal) (hb : b ∈ 𝔮'.asIdeal) :
    (ιFin p (ΓM M H) hj).base 𝔮 ≠ 𝔛.w.hom.base ((ιFin p (ΓM M H) hj).base 𝔮') := by
  intro heq
  rw [← Scheme.Hom.comp_apply, hwchart, Scheme.Hom.comp_apply] at heq
  have h𝔮 := (ιFin p (ΓM M H) hj).isOpenEmbedding.injective heq

  have hθa : theta a ∈ 𝔮'.asIdeal := by
    have : a ∈ ((Spec.map (CommRingCat.ofHom theta.toRingEquiv.toRingHom)).base 𝔮').asIdeal := h𝔮 ▸ ha
    exact this
  exact 𝔮'.isPrime.ne_top (top_le_iff.1 (hab ▸ sup_le ((Ideal.span_singleton_le_iff_mem _).2 hb)
    ((Ideal.span_singleton_le_iff_mem _).2 hθa)))

end S_ModularCurve_XHDRModelAtP_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_iotaFin_ne_w_iotaFin_of_span_singleton_sup_span_singleton_theta_eq_top (solution)
