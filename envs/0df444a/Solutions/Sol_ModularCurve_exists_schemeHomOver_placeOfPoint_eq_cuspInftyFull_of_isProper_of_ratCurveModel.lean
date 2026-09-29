-- Prove2me | solution 1 for ModularCurve.exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/15aaa195-bf3c-58c9-8265-49311c439db5

import Mathlib
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_QAdicPlace
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_cuspInftyFull
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra ModularCurve

theorem solution
    (p : ℕ) [NeZero p] (q : ℕ) [Fact q.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q))) [IsProper c]
    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ))))
    [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase) :
    ∃ (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt q)))) c)
      (x₀ : closedPoints M₀.C)
      (y : Spec (CommRingCat.of ℚ) ⟶
        pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)))),
      M₀.placeOfPoint x₀ = cuspInftyFull p ∧
      y ≫ pullback.snd c _ = 𝟙 _ ∧
      y ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)) ≫ ε.1 ∧
      (y ≫ inv e₀).base (IsLocalRing.closedPoint ℚ) = x₀.1 := by
  haveI hdvr : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt q) :=
    GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out
  haveI : IsFractionRing ↥(GaloisRep.ratLocalizedAt q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q
  haveI : ValuationRing ↥(GaloisRep.ratLocalizedAt q) := inferInstance

  let x₀ : closedPoints M₀.C := M₀.placeEquiv.symm (cuspInftyFull p)
  have hx₀ : M₀.placeOfPoint x₀ = cuspInftyFull p := by
    rw [← CurveModel.placeEquiv_apply]; exact M₀.placeEquiv.apply_symm_apply _

  obtain ⟨pt, hpt, hptx⟩ :=
    AlgebraicCurve.CurveModel.exists_comp_toBase_eq_id_and_base_closedPoint_eq_of_deg_eq_one M₀ x₀
      (by rw [hx₀]; exact ModularCurve.deg_cuspInftyFull p)
  have hy_snd : (pt ≫ e₀) ≫ pullback.snd c _ = 𝟙 _ := by rw [Category.assoc, he₀, hpt]
  have hxQ : ((pt ≫ e₀) ≫ pullback.fst c _) ≫ c =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt q) ℚ)) := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hy_snd, Category.id_comp]

  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ :=
    AlgebraicGeometry.existsUnique_section_comp_eq_of_universallyClosed_of_isSeparated
      c ((pt ≫ e₀) ≫ pullback.fst c _) hxQ
  refine ⟨⟨σ, hσ₁⟩, x₀, pt ≫ e₀, hx₀, hy_snd, hσ₂.symm, ?_⟩
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact hptx

end S_ModularCurve_exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel
end P2MW
export P2MW.S_ModularCurve_exists_schemeHomOver_placeOfPoint_eq_cuspInftyFull_of_isProper_of_ratCurveModel (solution)
