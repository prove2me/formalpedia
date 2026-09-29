-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/76a0871b-ca5c-59ac-9d61-d410828e7081

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_CharPReduction
import Theorems.Thm_ModularCurve_isAffineGeomPlace_or_ord_jGeomGen_lt_zero
import Theorems.Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable
import Theorems.Thm_ModularCurve_PlaceSpecialization_ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
import Theorems.Thm_ModularCurve_DRModelPackageLevel_ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin
import Theorems.Thm_ModularCurve_DRModelPackageLevel_red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst ModularCurve.DRLevel.sectionFibre_snd_assoc AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel ModularCurve.IgusaScheme ModularCurve.PlaceSpecialization

noncomputable section

namespace CoordSS

variable {N₀ p : ℕ} [NeZero N₀] [Fact p.Prime] [NeZero p] {hpN₀ : ¬ p ∣ N₀}

theorem reduceFst_mem_ssPlaces_of_ord_jFun_sub_pos
    {A : ValuationSubring (AlgebraicClosure ℚ)}
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] {red : ↥A →+* κ}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p}
    (P : PlaceSpecialization A p N₀ data hKr κ red hα hβ) (hN : (N₀ : κ) ≠ 0)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) (a : ↥A)
    (hV : 0 < V.ord (ProlongationTuple.jFun N₀ p -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) ((a : ↥A) : AlgebraicClosure ℚ)))
    (ha : red a ∈ ssJSet p κ) :
    P.reduceFst V ∈ ssPlaces p N₀ κ := by
  have hord := P.ord_jGeomGen_sub_pos_of_ord_jFun_sub_pos V a hV
  have hj : jGeomGen κ N₀ ∈ (P.reduceFst V).toValuationSubring := by
    have hmem := (P.reduceFst V).mem_of_ord_nonneg (jGeomGen_sub_algebraMap_ne_zero κ N₀ (red a)) hord.le
    have := add_mem hmem ((P.reduceFst V).algebraMap_mem' (red a))
    rwa [sub_add_cancel] at this
  have haff : IsAffineGeomPlace κ N₀ (P.reduceFst V) := by
    rcases isAffineGeomPlace_or_ord_jGeomGen_lt_zero κ N₀ (P.reduceFst V) with h | h
    · exact h
    · exact absurd h (not_lt.mpr ((P.reduceFst V).ord_nonneg_of_mem hj))
  have hrat : (P.reduceFst V).IsRational := by
    obtain ⟨_, _, _, _, _⟩ := exists_algebra_ratFunc_modularFunctionFieldC_finite_isSeparable κ N₀ hN
    exact Place.isRational_of_isAlgClosed (P.reduceFst V)
  have hcen : IsCentreOf κ N₀ (red a, (P.reduceFst V).evalAt (jNGeomGen κ N₀)) (P.reduceFst V) :=
    ⟨hord, ord_sub_evalAt_pos_of_isRational hrat haff.2 (jNGeomGen_sub_algebraMap_ne_zero κ N₀ _)⟩
  refine (mem_ssPlaces_iff p N₀ κ).mpr ⟨hrat, haff, ?_⟩
  rw [hcen.evalAt_jGeomGen]
  exact ha

end CoordSS

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ] (red : ↥A →+* κ) :
    letI : Algebra (R p) κ := (red.comp ρ).toAlgebra
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr κ red hα hβ)
      (_ : ∀ c : ↥A, red c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
      (uκ : Spec (CommRingCat.of κ) ⟶ fibre (N₀ := N₀) (algebraMap (R p) κ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom red) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (n : ↥(pullback (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1)))
      (_ : (pullback.fst (𝔓.comp κ (algebraMap (R p) κ) 0) (𝔓.comp κ (algebraMap (R p) κ) 1) ≫ 𝔓.comp κ (algebraMap (R p) κ) 0).base n =
        uκ.base (IsLocalRing.closedPoint κ)),
      P.reduceFst (𝔓.Meta.pointEquivPlace y) ∈ ssPlaces p N₀ κ := by
  letI : Algebra (R p) κ := (red.comp ρ).toAlgebra
  intro data hKr hα hβ P hker y u hu uκ huκ₁ huκ₂ n hn
  obtain ⟨φ, hφ⟩ := ModularCurve.DRModelPackageLevel.exists_eq_spec_map_comp_iotaFin_of_comp_base_eq
    N₀ p hpN₀ 𝔓 κ (algebraMap (R p) κ) red
    (fun c hc => (hker c).mpr hc) u.1 uκ huκ₁ n hn
  have hord := ModularCurve.DRModelPackageLevel.ord_jFun_sub_pos_of_eq_spec_map_comp_iotaFin
    N₀ p hpN₀ 𝔓 A y u.1 hu φ hφ
  have hval := ModularCurve.DRModelPackageLevel.red_jChartFin_eq_evalAt_jGeomGen_nodeEquiv
    N₀ p hpN₀ 𝔓 κ (algebraMap (R p) κ) red u.1 φ hφ uκ huκ₁ huκ₂ n hn
  have hss : red (φ (jChartFin (N₀ * p) p)) ∈ ssJSet p κ := by
    rw [hval]
    exact ((isSupersingularPlace_iff p N₀ κ _).mp
      ((mem_ssPlaces_iff p N₀ κ).mp (𝔓.nodeEquiv κ (algebraMap (R p) κ) n).2)).2.2
  have hN : (N₀ : κ) ≠ 0 := fun h => hpN₀ ((CharP.cast_eq_zero_iff κ p N₀).mp h)
  exact CoordSS.reduceFst_mem_ssPlaces_of_ord_jFun_sub_pos P hN _ _ hord hss

#print axioms solution

end
end S_ModularCurve_DRModelPackageLevel_reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_reduceFst_mem_ssPlaces_of_specialPoint_eq_crossing (solution)
