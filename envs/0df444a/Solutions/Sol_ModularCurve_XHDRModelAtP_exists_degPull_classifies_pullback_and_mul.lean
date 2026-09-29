-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_degPull_classifies_pullback_and_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/6d49a738-3b52-5101-a11d-aa682cae9021

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_JacJ1Iface
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_rigidify_pullback_curveChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_degPull_classifies_pullback_and_mul

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard

open scoped MatrixGroups

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀) :
    ∃ degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase,

      (∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L))) ∧

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver s D₀.toBase),
        NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul s x y) (degPull i) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x (degPull i)) (NeronModelInfra.schemeHomOverComp y (degPull i))) ∧

      (∀ i : Fin 2, D₀.zeroSection ≫ (degPull i).1 = D.zeroSection) := by
  obtain ⟨N0, hpin0, hhom0, hzero0⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_curveChange
      (ε := NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) (ε' := 𝔛.εinf) 𝔛.π.1 𝔛.π.2 hD₀ hD
  obtain ⟨N1, hpin1, hhom1, hzero1⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_rigidify_pullback_curveChange
      (ε := NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π) (ε' := 𝔛.εinf) 𝔛.πw.1 𝔛.πw.2 hD₀ hD
  refine ⟨fun i => if i = 0 then N0 else N1, ?_, ?_, ?_⟩
  · intro i T t b
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact hpin0 t b
    · simp only [hi, if_false]
      exact hpin1 t b
  · intro i T s x y
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact hhom0 s x y
    · simp only [hi, if_false]
      exact hhom1 s x y
  · intro i
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact hzero0
    · simp only [hi, if_false]
      exact hzero1

end S_ModularCurve_XHDRModelAtP_exists_degPull_classifies_pullback_and_mul
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_degPull_classifies_pullback_and_mul (solution)
