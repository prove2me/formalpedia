-- Prove2me | solution 1 for ModularCurve.ord_jBar_sub_1728_dvd_two_of_odd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/47ca24e4-02ba-5eb1-b64b-c83deeb6d257

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_ModularCurve_JLinePlacesBar
import Definitions.Def_HahnSeries_RamificationBound
import Definitions.Def_ModularCurve_QAdicPlace
import Theorems.Thm_AlgebraicCurve_Place_ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
import Theorems.Thm_ModularCurve_ModularPolynomialData_hasRamBound_two_of_isRoot_at_1728_of_odd
import Theorems.Thm_ModularCurve_ModularPolynomialData_hasRamBound_three_of_isRoot_at_zero_of_odd
import Theorems.Thm_ModularCurve_adjoin_jBar_jNBar_eq_top
import Theorems.Thm_HahnSeries_mem_puiseuxRamSubfield_iff
import Theorems.Thm_ModularCurve_nonempty_modularPolynomialData
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two_of_odd
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.vcY_vcYInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000

noncomputable section

open ModularCurve AlgebraicCurve IntermediateField Polynomial

namespace S12U

variable (N : ℕ) [NeZero N]

abbrev jb : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩

abbrev jNb : ↥(modularFunctionFieldBar N) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ N jq),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (dvd_refl N))⟩

@[reducible] def algRF : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) :=
  ((algebraMap ↥(jLineBar N) ↥(modularFunctionFieldBar N)).comp (jLineBarRingEquiv N).toRingHom).toAlgebra

theorem isScalarTower_RF :
    letI := algRF N
    IsScalarTower (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) := by
  letI := algRF N
  refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
  show algebraMap _ _ a = algebraMap ↥(jLineBar N) ↥(modularFunctionFieldBar N)
    (jLineBarRingEquiv N (algebraMap _ _ a))
  rw [jLineBarRingEquiv_algebraMap]
  rfl

theorem finite_RF :
    letI := algRF N
    FiniteDimensional (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N) := by
  letI := algRF N
  letI algRE : Algebra (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) := (jLineBarRingEquiv N).toRingHom.toAlgebra
  haveI : IsScalarTower (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) ↥(modularFunctionFieldBar N) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Module.Finite (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N) :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc (AlgebraicClosure ℚ)) ↥(jLineBar N))
      (jLineBarRingEquiv N).surjective
  haveI : FiniteDimensional ↥(jLineBar N) ↥(modularFunctionFieldBar N) :=
    finiteDimensional_adjoin_coeffEmb_jq_of_neZero N
  exact Module.Finite.trans ↥(jLineBar N) ↥(modularFunctionFieldBar N)

theorem algebraMap_RF_X :
    letI := algRF N
    algebraMap (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) Polynomial.X) = jb N := by
  letI := algRF N
  show ((jLineBarRingEquiv N (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) X)
    : ↥(jLineBar N)) : ↥(modularFunctionFieldBar N)) = jb N
  rw [RatFunc.algebraMap_X, jLineBarRingEquiv_X]

theorem algebraMap_RF_C (c : AlgebraicClosure ℚ) :
    letI := algRF N
    algebraMap (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (Polynomial.C c))
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c := by
  letI := algRF N
  haveI := isScalarTower_RF N
  rw [RatFunc.algebraMap_C, ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply]

theorem algebraMap_RF_X_sub_C (c : AlgebraicClosure ℚ) :
    letI := algRF N
    algebraMap (RatFunc (AlgebraicClosure ℚ)) ↥(modularFunctionFieldBar N)
      (algebraMap (Polynomial (AlgebraicClosure ℚ)) (RatFunc (AlgebraicClosure ℚ)) (X - C c))
        = jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c := by
  letI := algRF N
  rw [map_sub, map_sub, algebraMap_RF_X, algebraMap_RF_C]

theorem eval₂_Phi_jb_jNb (data : ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) (jNb N)
      = 0 := by

  apply Subtype.ext
  have hval : ((modularFunctionFieldBar N).toSubfield.subtype).comp
      (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N))
      = (coeffEmb (AlgebraicClosure ℚ)).comp evalAtJ := by
    refine Polynomial.ringHom_ext (fun z => by simp) ?_
    show ((Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N) X :
        ↥(modularFunctionFieldBar N)) : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (evalAtJ X)
    rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, evalAtJ_X]
  have h0 := congrArg (coeffEmb (AlgebraicClosure ℚ)) data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, ← hval] at h0
  rw [ZeroMemClass.coe_zero, ← h0]
  show ((modularFunctionFieldBar N).toSubfield.subtype) _ = _
  rw [Polynomial.hom_eval₂]
  rfl

theorem hasRamBound_C (a : AlgebraicClosure ℚ) :
    HahnSeries.HasRamBound 1 (HahnSeries.C a : HahnSeries ℚ (AlgebraicClosure ℚ)) := by
  intro g hg
  have : g ∈ ({0} : Set ℚ) := HahnSeries.support_single_subset (a := (0 : ℚ)) (r := a) hg
  rw [Set.mem_singleton_iff] at this
  exact ⟨0, by simp [this]⟩

theorem hasRamBound_C_add_single (a : AlgebraicClosure ℚ) :
    HahnSeries.HasRamBound 1
      (HahnSeries.C a + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)) := by
  intro g hg
  rcases (HahnSeries.support_add_subset (x := HahnSeries.C a)
      (y := HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ))) hg with h | h
  · exact hasRamBound_C a h
  · have : g ∈ ({1} : Set ℚ) :=
      HahnSeries.support_single_subset (a := (1 : ℚ)) (r := (1 : AlgebraicClosure ℚ)) h
    rw [Set.mem_singleton_iff] at this
    exact ⟨1, by simp [this]⟩

end S12U

namespace S12U

variable (N : ℕ) [NeZero N]

theorem hasRamBound_of_one' {e : ℕ} (he : 0 < e) {y : HahnSeries ℚ (AlgebraicClosure ℚ)}
    (hy : HahnSeries.HasRamBound 1 y) : HahnSeries.HasRamBound e y := by
  intro g hg
  obtain ⟨k, hk⟩ := hy hg
  refine ⟨k * e, ?_⟩
  simp only [Nat.cast_one, div_one] at hk
  have he' : (e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  rw [← hk]; push_cast; field_simp

theorem forall_hasRamBound_of_roots (data : ModularPolynomialData N) (c : AlgebraicClosure ℚ) {d : ℕ} (hd : 0 < d)
    (hroots : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.C c + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r → HahnSeries.HasRamBound d r)
    (ψ : ↥(modularFunctionFieldBar N) →ₐ[AlgebraicClosure ℚ] HahnSeries ℚ (AlgebraicClosure ℚ))
    (hψ : ψ (jb N) = HahnSeries.C c + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)) :
    ∀ z, HahnSeries.HasRamBound d (ψ z) := by
  let S := HahnSeries.puiseuxRamSubfield (AlgebraicClosure ℚ) (e := d) hd
  have hS : ∀ y, y ∈ S ↔ HahnSeries.HasRamBound d y := fun y => HahnSeries.mem_puiseuxRamSubfield_iff hd
  let T : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    (S.comap ψ.toRingHom).toIntermediateField (fun a => by
      show ψ (algebraMap (AlgebraicClosure ℚ) _ a) ∈ S
      have hC : algebraMap (AlgebraicClosure ℚ) (HahnSeries ℚ (AlgebraicClosure ℚ)) a = HahnSeries.C a := by
        rw [HahnSeries.algebraMap_apply']; simp
      rw [ψ.commutes, hS, hC]
      exact hasRamBound_of_one' hd (hasRamBound_C a))
  have hjb : jb N ∈ T := by
    show ψ (jb N) ∈ S
    rw [hψ, hS]
    exact hasRamBound_of_one' hd (hasRamBound_C_add_single c)
  have hjNb : jNb N ∈ T := by
    show ψ (jNb N) ∈ S
    rw [hS]
    refine hroots _ ?_
    rw [Polynomial.IsRoot, Polynomial.eval_map, ← hψ]
    have hcomp : Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) (ψ (jb N))
        = (ψ.toRingHom).comp (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) := by
      refine Polynomial.ringHom_ext (fun z => by simp) ?_
      simp
    rw [hcomp]
    have h := (Polynomial.hom_eval₂ data.Φ
      (Polynomial.eval₂RingHom (Int.castRingHom ↥(modularFunctionFieldBar N)) (jb N)) ψ.toRingHom (jNb N)).symm
    rw [eval₂_Phi_jb_jNb N data, map_zero] at h
    simpa using h
  have htop := ModularCurve.adjoin_jBar_jNBar_eq_top (AlgebraicClosure ℚ) N
  have hle : (⊤ : IntermediateField (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N)) ≤ T := by
    rw [← htop, IntermediateField.adjoin_le_iff]
    intro z hz
    rcases hz with rfl | rfl
    · exact hjb
    · exact hjNb
  intro z
  exact (hS _).mp (hle IntermediateField.mem_top)

theorem ord_jb_sub_dvd (data : ModularPolynomialData N) (c : AlgebraicClosure ℚ) {d : ℕ} (hd : 0 < d)
    (hroots : ∀ r : HahnSeries ℚ (AlgebraicClosure ℚ),
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
        (HahnSeries.C c + HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r → HahnSeries.HasRamBound d r)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hpos : 0 < v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c)) :
    v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) c) ∣ (d : ℤ) := by
  letI := algRF N
  haveI := isScalarTower_RF N
  haveI := finite_RF N
  have key := AlgebraicCurve.Place.ord_dvd_of_forall_hahnSeries_embedding_hasRamBound
    (K := AlgebraicClosure ℚ) (L := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))
    (X - C c) (Polynomial.irreducible_X_sub_C c) c (by simp) (by simp) hd
    (fun ψ hψ => forall_hasRamBound_of_roots N data c hd hroots ψ (by rwa [algebraMap_RF_X] at hψ)) v
    (by rwa [algebraMap_RF_X_sub_C])
  rwa [algebraMap_RF_X_sub_C] at key

theorem ord_jb_sub_1728_dvd_two (hN : Odd N)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hpos : 0 < v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728)) :
    v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 1728) ∣ 2 := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  have h := ord_jb_sub_dvd N data 1728 (d := 2) two_pos (fun r hr => by
    refine ModularCurve.ModularPolynomialData.hasRamBound_two_of_isRoot_at_1728_of_odd hN data r ?_
    have : (HahnSeries.C (1728 : AlgebraicClosure ℚ) : HahnSeries ℚ (AlgebraicClosure ℚ)) = 1728 := map_ofNat _ 1728
    rwa [this] at hr) v hpos
  exact_mod_cast h

theorem ord_jb_dvd_three (hN : Odd N)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hpos : 0 < v.ord (jb N)) :
    v.ord (jb N) ∣ 3 := by
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  have hpos' : 0 < v.ord (jb N - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) 0) := by
    rwa [map_zero, sub_zero]
  have h := ord_jb_sub_dvd N data 0 (d := 3) three_pos (fun r hr => by
    refine ModularCurve.ModularPolynomialData.hasRamBound_three_of_isRoot_at_zero_of_odd hN data r ?_
    rwa [map_zero, zero_add] at hr) v hpos'
  rw [map_zero, sub_zero] at h
  exact_mod_cast h

end S12U

end

theorem solution (N : ℕ) [NeZero N] (hN : Odd N)
    (v : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N))
    (hpos : 0 < v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728)) :
    v.ord (ModularCurve.jBar N - algebraMap (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) 1728) ∣ 2 := by
  exact S12U.ord_jb_sub_1728_dvd_two N hN v hpos

end S_ModularCurve_ord_jBar_sub_1728_dvd_two_of_odd
end P2MW
export P2MW.S_ModularCurve_ord_jBar_sub_1728_dvd_two_of_odd (solution)
