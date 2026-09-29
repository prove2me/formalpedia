-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.degPull_mul_and_zeroSection_comp_of_classifies_pullback
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/714fc20a-e2ea-54ba-b299-fb3866c1b618

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

import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_degPull_classifies_pullback_and_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_degPull_mul_and_zeroSection_comp_of_classifies_pullback
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard

open scoped MatrixGroups

set_option maxHeartbeats 1600000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (D₀ : RelativePic0Designation (R p) (toBase p (ΓN p M H hpM) hj))
    (hD₀ : RepresentsRelSubPic (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)
      (algEquivZeroCut (toBase p (ΓN p M H hpM) hj) (NeronModelInfra.schemeHomOverComp 𝔛.εinf 𝔛.π)) D₀)
    (degPull : Fin 2 → SchemeHomOver D₀.toBase D.toBase)
    (hdegPull : ∀ (i : Fin 2) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t D₀.toBase),
        Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b (degPull i))).L ≅
          Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) t 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) t)
            ((Scheme.Modules.pullback (curveChange (if i = 0 then 𝔛.π else 𝔛.πw).1 (if i = 0 then 𝔛.π else 𝔛.πw).2 t)).obj
              (hD₀.poincare.pullbackAlong b).L))) :

    (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver s D₀.toBase),
      NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).mul s x y) (degPull i) =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
          (NeronModelInfra.schemeHomOverComp x (degPull i)) (NeronModelInfra.schemeHomOverComp y (degPull i))) ∧

    (∀ i : Fin 2, D₀.zeroSection ≫ (degPull i).1 = D.zeroSection) := by

  obtain ⟨dp, hdp, hmul, hzero⟩ :=
    ModularCurve.XHDRModelAtP.exists_degPull_classifies_pullback_and_mul p M H hpM hj 𝔛 D hD D₀ hD₀

  have huniq : ∀ i, degPull i = dp i := by
    intro i
    let b : SchemeHomOver D₀.toBase D₀.toBase := ⟨𝟙 _, Category.id_comp _⟩
    have hb : ∀ f : SchemeHomOver D₀.toBase D.toBase, NeronModelInfra.schemeHomOverComp b f = f := by
      intro f; apply Subtype.ext; exact Category.id_comp _
    obtain ⟨e₁⟩ := hdegPull i D₀.toBase b
    obtain ⟨e₂⟩ := hdp i D₀.toBase b
    have := hD.ext_of_iso D₀.toBase (NeronModelInfra.schemeHomOverComp b (degPull i)) (NeronModelInfra.schemeHomOverComp b (dp i)) ⟨e₁ ≪≫ e₂.symm⟩
    rwa [hb, hb] at this
  refine ⟨fun i T s x y => ?_, fun i => ?_⟩
  · rw [huniq i]; exact hmul i s x y
  · rw [huniq i]; exact hzero i

#print axioms solution

end S_ModularCurve_XHDRModelAtP_degPull_mul_and_zeroSection_comp_of_classifies_pullback
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_degPull_mul_and_zeroSection_comp_of_classifies_pullback (solution)
