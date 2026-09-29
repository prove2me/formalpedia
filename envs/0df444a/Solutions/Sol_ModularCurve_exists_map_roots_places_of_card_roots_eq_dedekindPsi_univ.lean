-- Prove2me | solution 1 for ModularCurve.exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/a808d981-dca3-5d1d-a200-311a93e52df2

import Theorems.Thm_ModularCurve_sum_ord_jGeomGen_sub_eq_dedekindPsi
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_modularPolynomialData
import Mathlib.Algebra.CharP.Defs
import Definitions.Def_WeierstrassCurve_ReduceHom
import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_ModularPolynomialData_eval_jqNModC_mul_eq_zero
import Theorems.Thm_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries
import Mathlib.FieldTheory.Relrank
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Algebra.Polynomial.Div
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet
import Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j
import Theorems.Thm_WeierstrassCurve_exists_isElliptic_map_veluQuotient_j
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Card
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Theorems.Thm_ModularCurve_modularFunctionFieldC_algHom_ext
import Theorems.Thm_ModularCurve_isSeparable_jqNModC_of_good
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none HahnSeries.ramScale_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluY_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"

set_option autoImplicit false

section Brick_ELL1_B

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
p2m_open "ModularCurve"

private theorem isSeparable_jqNModC_of_prime_of_not_dvd (q N : ℕ) [Fact N.Prime] (hqN : ¬ q ∣ N)
    (K : Type*) [Field K] [Fact q.Prime] [CharP K q] :
    IsSeparable (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (jqNModC K N) := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm N
  refine isSeparable_jqNModC_of_modularPolynomialData K data hsymm ?_
  intro h
  exact hqN ((CharP.cast_eq_zero_iff K q N).mp h)

end ModularCurve

end Brick_ELL1_B

section Brick_ELL4A_LAU

set_option autoImplicit false

open IsLocalRing Polynomial

namespace SsfrobEll4a

section Transport

variable {R S : Type*} [CommRing R] [CommRing S]

private lemma mem_maximalIdeal_map {e : R ≃+* S} [IsLocalRing R] [IsLocalRing S] {r : R}
    (hr : r ∈ maximalIdeal R) : e r ∈ maximalIdeal S := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
  intro hu
  apply hr
  have h := hu.map e.symm.toRingHom
  simpa using h

private theorem henselianLocalRing_of_ringEquiv [HenselianLocalRing R] [IsLocalRing S]
    (e : R ≃+* S) : HenselianLocalRing S := by
  constructor
  intro f hf a₀ h₁ h₂
  have hcomp : (f.map (e.symm : S →+* R)).map (e : R →+* S) = f := by
    rw [Polynomial.map_map, show ((e : R →+* S).comp (e.symm : S →+* R)) = RingHom.id S from
      RingHom.ext fun s => e.apply_symm_apply s, Polynomial.map_id]
  have h₁' : (f.map (e.symm : S →+* R)).eval ((e.symm : S →+* R) a₀) ∈ maximalIdeal R := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact mem_maximalIdeal_map (e := e.symm) h₁
  have h₂' : IsUnit ((derivative (f.map (e.symm : S →+* R))).eval
      ((e.symm : S →+* R) a₀)) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, Polynomial.eval₂_at_apply]
    exact h₂.map e.symm.toRingHom
  obtain ⟨b, hroot, hb⟩ := HenselianLocalRing.is_henselian
    (f.map (e.symm : S →+* R)) (hf.map _) ((e.symm : S →+* R) a₀) h₁' h₂'
  refine ⟨(e : R →+* S) b, ?_, ?_⟩
  · rw [← hcomp, Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_at_apply,
      hroot.eq_zero, map_zero]
  · have h := mem_maximalIdeal_map (e := e) hb
    simpa [map_sub, RingEquiv.coe_toRingHom] using h

private theorem henselianLocalRing_of_henselianRing' {T : Type*} [CommRing T] [IsLocalRing T]
    (h : HenselianRing T (maximalIdeal T)) : HenselianLocalRing T := by
  constructor
  intro f hf a₀ h₁ h₂
  exact h.is_henselian f hf a₀ h₁ ((Ideal.Quotient.mk _).isUnit_map h₂)

end Transport

private scoped instance instHenselianLocalRingPowerSeries (k : Type*) [Field k] :
    HenselianLocalRing (PowerSeries k) := by
  refine henselianLocalRing_of_henselianRing' ?_
  rw [PowerSeries.maximalIdeal_eq_span_X]
  infer_instance

section Laurent

variable (K : Type*) [Field K]

private noncomputable def laurentIntegers : ValuationSubring (LaurentSeries K) :=
  (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))).valuationSubring

private theorem mem_laurentIntegers_iff {f : LaurentSeries K} :
    f ∈ laurentIntegers K ↔ ∃ p : PowerSeries K, (p : LaurentSeries K) = f := by
  rw [show (f ∈ laurentIntegers K) ↔
      Valued.v f ≤ (1 : WithZero (Multiplicative ℤ)) from Iff.rfl,
    LaurentSeries.val_le_one_iff_eq_coe]

private noncomputable def powerSeriesEquivLaurentIntegers :
    PowerSeries K ≃+* (laurentIntegers K) := by
  refine RingEquiv.ofBijective
    (((HahnSeries.ofPowerSeries ℤ K : PowerSeries K →+* LaurentSeries K)).codRestrict
      (laurentIntegers K).toSubring
      (fun p => (mem_laurentIntegers_iff K).mpr ⟨p, rfl⟩)) ⟨?_, ?_⟩
  · intro p q h
    exact HahnSeries.ofPowerSeries_injective (congrArg Subtype.val h)
  · rintro ⟨f, hf⟩
    obtain ⟨p, hp⟩ := (mem_laurentIntegers_iff K).mp hf
    exact ⟨p, Subtype.ext hp⟩

private scoped instance : HenselianLocalRing (laurentIntegers K) :=
  henselianLocalRing_of_ringEquiv (powerSeriesEquivLaurentIntegers K)

end Laurent

section Residue

variable (K : Type*) [Field K]

private noncomputable def powerSeriesResidueEquiv :
    ResidueField (PowerSeries K) ≃+* K :=
  (Ideal.quotEquivOfEq (PowerSeries.ker_coeff_eq_max_ideal).symm).trans
    (RingHom.quotientKerEquivOfSurjective
      (fun c => ⟨PowerSeries.C c, PowerSeries.constantCoeff_C c⟩))

private noncomputable def laurentIntegersResidueEquiv :
    ResidueField (laurentIntegers K) ≃+* K :=
  (ResidueField.mapEquiv (powerSeriesEquivLaurentIntegers K).symm).trans
    (powerSeriesResidueEquiv K)

private scoped instance [IsAlgClosed K] :
    IsAlgClosed (ResidueField (laurentIntegers K)) :=
  IsAlgClosed.of_ringEquiv _ _ (laurentIntegersResidueEquiv K).symm

end Residue

end SsfrobEll4a
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a"

end Brick_ELL4A_LAU
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a"

section Brick_ELL4B_A

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve"

namespace SsfrobWlocSkin

private abbrev wlocJAdj (K : Type*) [Field K] : IntermediateField K (LaurentSeries K) :=
  IntermediateField.adjoin K ({ModularCurve.jqModC K} : Set (LaurentSeries K))

private abbrev wlocJGen (K : Type*) [Field K] : ↥(wlocJAdj K) :=
  IntermediateField.AdjoinSimple.gen K (ModularCurve.jqModC K)

private abbrev wlocPhi (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) : Polynomial ↥(wlocJAdj K) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ↥(wlocJAdj K)) (wlocJGen K))

private theorem wlocPhi_monic (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) : (wlocPhi K N data).Monic :=
  data.monic.map _

private theorem eval₂_phi_jqModC_jqNModC (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (ModularCurve.jqModC K)) (ModularCurve.jqNModC K N) = 0 := by
  have h := ModularCurve.ModularPolynomialData.eval_jqNModC_mul_eq_zero data K 1
  simp only [ModularCurve.jqNModC_one, one_mul] at h
  have hbr : (Polynomial.aeval (R := ℤ) (ModularCurve.jqModC K)).toRingHom
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
          (ModularCurve.jqModC K) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  rw [hbr] at h
  exact h

private theorem aeval_wlocPhi (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) :
    Polynomial.aeval (ModularCurve.jqNModC K N) (wlocPhi K N data) = 0 := by
  have hcomp : (algebraMap ↥(wlocJAdj K) (LaurentSeries K)).comp
        (Polynomial.eval₂RingHom (Int.castRingHom ↥(wlocJAdj K)) (wlocJGen K)) =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (ModularCurve.jqModC K) := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X]
    rfl
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hcomp]
  exact eval₂_phi_jqModC_jqNModC K N data

private theorem isIntegral_jqNModC_wloc (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) :
    IsIntegral ↥(wlocJAdj K) (ModularCurve.jqNModC K N) :=
  ⟨wlocPhi K N data, wlocPhi_monic K N data, by
    rw [← Polynomial.aeval_def]; exact aeval_wlocPhi K N data⟩

private theorem wlocJAdj_le (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    wlocJAdj K ≤ ModularCurve.modularFunctionFieldC K N :=
  IntermediateField.adjoin_le_iff.mpr
    (Set.singleton_subset_iff.mpr (ModularCurve.jqModC_mem K N))

private theorem adjoin_jqNModC_eq_extendScalars (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K)) =
      IntermediateField.extendScalars (wlocJAdj_le K N) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_simple_le_iff, IntermediateField.mem_extendScalars]
    exact ModularCurve.jqNModC_mem K N
  · intro x hx
    rw [IntermediateField.mem_extendScalars] at hx
    have ha : ModularCurve.jqModC K ∈ IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K)) := by
      have h := (IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))).algebraMap_mem (wlocJGen K)
      rwa [IntermediateField.algebraMap_apply] at h
    have hb : ModularCurve.jqNModC K N ∈ IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K)) :=
      IntermediateField.mem_adjoin_simple_self ↥(wlocJAdj K) (ModularCurve.jqNModC K N)
    have hle2 : ModularCurve.modularFunctionFieldC K N ≤
        (IntermediateField.adjoin ↥(wlocJAdj K)
          ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))).restrictScalars K := by
      show IntermediateField.adjoin K
          ({ModularCurve.jqModC K, ModularCurve.jqNModC K N} : Set (LaurentSeries K)) ≤ _
      exact IntermediateField.adjoin_le_iff.mpr
        (Set.insert_subset_iff.mpr ⟨ha, Set.singleton_subset_iff.mpr hb⟩)
    exact (IntermediateField.mem_restrictScalars K).mp (hle2 hx)

private theorem finrank_adjoin_jqNModC_wloc (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [Fact q.Prime] [CharP K q] (hqN : ¬ q ∣ N) :
    Module.finrank ↥(wlocJAdj K)
      ↥(IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))) =
      ModularCurve.dedekindPsi N := by
  rw [adjoin_jqNModC_eq_extendScalars K N,
    ← IntermediateField.relfinrank_eq_finrank_of_le (wlocJAdj_le K N)]
  exact ModularCurve.relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi K N q hqN

private theorem natDegree_minpoly_wloc (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [Fact q.Prime] [CharP K q] (hqN : ¬ q ∣ N)
    (data : ModularCurve.ModularPolynomialData N) :
    (minpoly ↥(wlocJAdj K) (ModularCurve.jqNModC K N)).natDegree =
      ModularCurve.dedekindPsi N := by
  rw [← IntermediateField.adjoin.finrank (isIntegral_jqNModC_wloc K N data),
    finrank_adjoin_jqNModC_wloc q N K hqN]

private theorem minpoly_wloc_eq (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [Fact q.Prime] [CharP K q] (hqN : ¬ q ∣ N)
    (data : ModularCurve.ModularPolynomialData N) :
    minpoly ↥(wlocJAdj K) (ModularCurve.jqNModC K N) = wlocPhi K N data := by
  symm
  refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic (isIntegral_jqNModC_wloc K N data)) (wlocPhi_monic K N data)
    (minpoly.dvd _ _ (aeval_wlocPhi K N data)) (le_of_eq ?_)
  rw [natDegree_minpoly_wloc q N K hqN data, data.monic.natDegree_map, data.natDegree_eq]

private def baseHom (K : Type*) [Field K] {A : Type*} [Field A] [Algebra K A] {x₀ : A}
    (hx : Transcendental K x₀) : ↥(wlocJAdj K) →ₐ[K] A :=
  (((IntermediateField.adjoin K ({x₀} : Set A)).val).comp
      (RatFunc.algEquivOfTranscendental x₀ hx).toAlgHom).comp
    (RatFunc.algEquivOfTranscendental (ModularCurve.jqModC K)
      (ModularCurve.transcendental_jqModC K)).symm.toAlgHom

private theorem baseHom_gen (K : Type*) [Field K] {A : Type*} [Field A] [Algebra K A] {x₀ : A}
    (hx : Transcendental K x₀) : baseHom K hx (wlocJGen K) = x₀ := by
  have h1 : (RatFunc.algEquivOfTranscendental (ModularCurve.jqModC K)
        (ModularCurve.transcendental_jqModC K)).symm (wlocJGen K) = RatFunc.X :=
    RatFunc.algEquivOfTranscendental_symm_gen (ModularCurve.jqModC K)
      (ModularCurve.transcendental_jqModC K)
  show (IntermediateField.adjoin K ({x₀} : Set A)).val
      ((RatFunc.algEquivOfTranscendental x₀ hx)
        ((RatFunc.algEquivOfTranscendental (ModularCurve.jqModC K)
          (ModularCurve.transcendental_jqModC K)).symm (wlocJGen K))) = x₀
  rw [h1]
  exact RatFunc.algEquivOfTranscendental_X x₀ hx

set_option maxHeartbeats 1600000 in
set_option maxSynthPendingDepth 3 in

private theorem exists_algHom_of_root_pair_aux (q N : ℕ) [NeZero N] (K : Type*) [Field K]
    [Fact q.Prime] [CharP K q] (hqN : ¬ q ∣ N)
    (data : ModularCurve.ModularPolynomialData N) (A : Type*) [Field A] [Algebra K A]
    (x₀ y : A) (hx : Transcendental K x₀)
    (hy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) x₀)).IsRoot y) :
    ∃ ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] A,
      ι ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩ = x₀ ∧
      ι ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩ = y := by
  have hB10 := minpoly_wloc_eq q N K hqN data
  let φ₀ : ↥(wlocJAdj K) →ₐ[K] A := baseHom K hx
  have hφ₀c : φ₀ (wlocJGen K) = x₀ := baseHom_gen K hx
  letI : Algebra ↥(wlocJAdj K) A := φ₀.toRingHom.toAlgebra
  have hamap : ∀ x, algebraMap ↥(wlocJAdj K) A x = φ₀ x := fun _ => rfl
  haveI : IsScalarTower K ↥(wlocJAdj K) A :=
    IsScalarTower.of_algebraMap_eq' (by ext x; exact (φ₀.commutes x).symm)
  have hint : IsIntegral ↥(wlocJAdj K) (ModularCurve.jqNModC K N) :=
    isIntegral_jqNModC_wloc K N data
  have hminmap : (minpoly ↥(wlocJAdj K) (ModularCurve.jqNModC K N)).map
        (algebraMap ↥(wlocJAdj K) A)
      = data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom A) x₀) := by
    rw [hB10, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, hamap]
    exact hφ₀c
  have hyroots : y ∈ (minpoly ↥(wlocJAdj K) (ModularCurve.jqNModC K N)).aroots A := by
    rw [Polynomial.mem_aroots', Polynomial.aeval_def, ← Polynomial.eval_map, hminmap]
    exact ⟨(data.monic.map _).ne_zero, hy⟩
  let ψ₁ : ↥(IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))) →ₐ[↥(wlocJAdj K)] A :=
    (IntermediateField.algHomAdjoinIntegralEquiv ↥(wlocJAdj K) hint).symm ⟨y, hyroots⟩
  have hψ₁gen : ψ₁ (IntermediateField.AdjoinSimple.gen ↥(wlocJAdj K)
        (ModularCurve.jqNModC K N)) = y :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ↥(wlocJAdj K) hint ⟨y, hyroots⟩
  have hadj : (IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))).restrictScalars K
      = ModularCurve.modularFunctionFieldC K N :=
    IntermediateField.adjoin_simple_adjoin_simple (F := K) (α := ModularCurve.jqModC K)
      (β := ModularCurve.jqNModC K N)
  let ψ' : ↥(IntermediateField.adjoin ↥(wlocJAdj K)
        ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))) →ₐ[K] A :=
    ψ₁.restrictScalars K
  let ψ : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] A :=
    ψ'.comp (IntermediateField.equivOfEq hadj).symm.toAlgHom
  refine ⟨ψ, ?_, ?_⟩
  · have hamb : ((IntermediateField.equivOfEq hadj).symm
          ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩ :
          ↥(IntermediateField.adjoin ↥(wlocJAdj K)
            ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))))
        = algebraMap ↥(wlocJAdj K)
            ↥(IntermediateField.adjoin ↥(wlocJAdj K)
              ({ModularCurve.jqNModC K N} : Set (LaurentSeries K)))
            (wlocJGen K) := Subtype.ext rfl
    show ψ₁ ((IntermediateField.equivOfEq hadj).symm
      ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem K N⟩) = x₀
    rw [hamb, ψ₁.commutes, hamap, hφ₀c]
  · have hamb' : ((IntermediateField.equivOfEq hadj).symm
          ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩ :
          ↥(IntermediateField.adjoin ↥(wlocJAdj K)
            ({ModularCurve.jqNModC K N} : Set (LaurentSeries K))))
        = IntermediateField.AdjoinSimple.gen ↥(wlocJAdj K) (ModularCurve.jqNModC K N) :=
      Subtype.ext rfl
    show ψ₁ ((IntermediateField.equivOfEq hadj).symm
      ⟨ModularCurve.jqNModC K N, ModularCurve.jqNModC_mem K N⟩) = y
    rw [hamb', hψ₁gen]

end SsfrobWlocSkin
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a"

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
namespace EllFam
p2m_open "ModularCurve"

open WeierstrassCurve

private theorem transcendental_of_notMem_range_of_isAlgClosed {K L : Type*} [Field K] [Field L]
    [Algebra K L] [IsAlgClosed K] {x : L} (hx : x ∉ Set.range (algebraMap K L)) :
    Transcendental K x := by
  intro halg
  have hint : IsIntegral K x := halg.isIntegral
  have hdeg : (minpoly K x).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint)
  have heq := minpoly.aeval K x
  rw [Polynomial.eq_X_add_C_of_degree_eq_one hdeg, (minpoly.monic hint).leadingCoeff,
    Polynomial.C_1, one_mul, Polynomial.aeval_add, Polynomial.aeval_X, Polynomial.aeval_C,
    add_eq_zero_iff_eq_neg] at heq
  exact hx ⟨-(minpoly K x).coeff 0, by rw [map_neg]; exact heq.symm⟩

private def genFibre {K : Type*} [CommRing K] (W : WeierstrassCurve (PowerSeries K)) :
    WeierstrassCurve (LaurentSeries K) :=
  W.map (algebraMap (PowerSeries K) (LaurentSeries K))

private scoped instance genFibre.instIsElliptic {K : Type*} [Field K]
    (W : WeierstrassCurve (PowerSeries K)) [W.IsElliptic] : (genFibre W).IsElliptic :=
  inferInstanceAs (W.map (algebraMap (PowerSeries K) (LaurentSeries K))).IsElliptic

p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre"
private theorem j_genFibre {K : Type*} [Field K] (W : WeierstrassCurve (PowerSeries K))
    [W.IsElliptic] :
    (genFibre W).j = algebraMap (PowerSeries K) (LaurentSeries K) W.j :=
  W.map_j (algebraMap (PowerSeries K) (LaurentSeries K))

private theorem algebraMap_laurentSeries_factor {K : Type*} [Field K] (c : K) :
    algebraMap K (LaurentSeries K) c
      = algebraMap (PowerSeries K) (LaurentSeries K) (PowerSeries.C (R := K) c) := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, LaurentSeries.coe_algebraMap,
    HahnSeries.ofPowerSeries_C]
  rfl

private theorem transcendental_j_genFibre {K : Type*} [Field K] [IsAlgClosed K]
    (W : WeierstrassCurve (PowerSeries K)) [W.IsElliptic]
    (hj : W.j ∉ Set.range (PowerSeries.C (R := K))) :
    Transcendental K (genFibre W).j := by
  apply transcendental_of_notMem_range_of_isAlgClosed
  rintro ⟨c, hc⟩
  refine hj ⟨c, ?_⟩
  have hinj : Function.Injective (algebraMap (PowerSeries K) (LaurentSeries K)) := by
    rw [LaurentSeries.coe_algebraMap]; exact HahnSeries.ofPowerSeries_injective
  apply hinj
  rw [← algebraMap_laurentSeries_factor, hc, j_genFibre]

private theorem order_ofPowerSeries_pos {K : Type*} [Field K] {f : PowerSeries K}
    (hf : f ≠ 0) (h0 : PowerSeries.constantCoeff (R := K) f = 0) :
    0 < (algebraMap (PowerSeries K) (LaurentSeries K) f).order := by
  rw [LaurentSeries.coe_algebraMap]
  have hne : HahnSeries.ofPowerSeries ℤ K f ≠ 0 :=
    fun h => hf (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))
  rw [show (0 : ℤ) < (HahnSeries.ofPowerSeries ℤ K f).order ↔
        (1 : ℤ) ≤ (HahnSeries.ofPowerSeries ℤ K f).order from
      Int.lt_iff_add_one_le.trans (by rw [zero_add]),
    HahnSeries.le_order_iff_forall hne]
  intro j hj
  have hc : (HahnSeries.ofPowerSeries ℤ K f).coeff j
      = if j < 0 then 0 else PowerSeries.coeff j.natAbs f := PowerSeries.coeff_coe (f := f) j
  rw [hc]
  split_ifs with hj0
  · rfl
  · have hj0' : j = 0 := by omega
    rw [hj0', Int.natAbs_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, h0]

private theorem order_j_genFibre_sub_pos {K : Type*} [Field K]
    (W : WeierstrassCurve (PowerSeries K)) [W.IsElliptic] {a : K}
    (hja : (W.map (PowerSeries.constantCoeff (R := K))).j = a)
    (hj : W.j ∉ Set.range (PowerSeries.C (R := K))) :
    0 < ((genFibre W).j - algebraMap K (LaurentSeries K) a).order := by
  rw [j_genFibre, algebraMap_laurentSeries_factor, ← map_sub]
  refine order_ofPowerSeries_pos (fun h => hj ?_) ?_
  · exact ⟨a, (sub_eq_zero.mp h).symm⟩
  · rw [map_sub, PowerSeries.constantCoeff_C, ← W.map_j (PowerSeries.constantCoeff (R := K)),
      hja, sub_self]

section PlaceOfAlgHom

variable {K : Type*} [Field K] {N : ℕ} [NeZero N]

private def wOfAlgHom (ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (h : ∃ x, (ι x).order ≠ 0) :
    AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N) :=
  (AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K ι h).choose

private def gammaOfAlgHom (ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (h : ∃ x, (ι x).order ≠ 0) : ℕ :=
  (AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K ι h).choose_spec.choose

private theorem gammaOfAlgHom_pos (ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (h : ∃ x, (ι x).order ≠ 0) : 0 < gammaOfAlgHom ι h :=
  (AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K
    ι h).choose_spec.choose_spec.1

private theorem ord_wOfAlgHom_mul_gamma
    (ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (h : ∃ x, (ι x).order ≠ 0) (x : ↥(ModularCurve.modularFunctionFieldC K N)) :
    (wOfAlgHom ι h).ord x * (gammaOfAlgHom ι h : ℤ) = (ι x).order :=
  (AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries K
    ι h).choose_spec.choose_spec.2 x

private theorem mem_wOfAlgHom_iff
    (ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K)
    (h : ∃ x, (ι x).order ≠ 0) (x : ↥(ModularCurve.modularFunctionFieldC K N)) :
    x ∈ (wOfAlgHom ι h).toValuationSubring ↔ 0 ≤ (ι x).order := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [ValuationSubring.zero_mem, map_zero, HahnSeries.order_zero, le_refl]
  have hιx : ι x ≠ 0 := fun hh =>
    hx0 ((injective_iff_map_eq_zero ι).mp (RingHom.injective ι.toRingHom) x hh)
  rw [← ord_wOfAlgHom_mul_gamma ι h]
  have hγ : (0 : ℤ) < (gammaOfAlgHom ι h : ℤ) :=
    Int.natCast_pos.mpr (gammaOfAlgHom_pos ι h)
  constructor
  · intro hmem
    exact mul_nonneg ((wOfAlgHom ι h).ord_nonneg_of_mem hmem) hγ.le
  · intro hnn
    refine (wOfAlgHom ι h).mem_of_ord_nonneg hx0 ?_
    by_contra hneg
    push Not at hneg
    have : (wOfAlgHom ι h).ord x * (gammaOfAlgHom ι h : ℤ) < 0 :=
      mul_neg_of_neg_of_pos hneg hγ
    omega

end PlaceOfAlgHom
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre"

section RootPair

variable (q N : ℕ) [NeZero N] (K : Type*) [Field K] [Fact q.Prime] [CharP K q]
  (hqN : ¬ q ∣ N) (data : ModularCurve.ModularPolynomialData N)
  {x₀ y : LaurentSeries K} (hx : Transcendental K x₀)
  (hy : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot y)

private def ιOfRoot : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K :=
  (SsfrobWlocSkin.exists_algHom_of_root_pair_aux q N K hqN data (LaurentSeries K)
    x₀ y hx hy).choose

private theorem ιOfRoot_jGeomGen :
    ιOfRoot q N K hqN data hx hy (ModularCurve.jGeomGen K N) = x₀ :=
  (SsfrobWlocSkin.exists_algHom_of_root_pair_aux q N K hqN data (LaurentSeries K)
    x₀ y hx hy).choose_spec.1

private theorem ιOfRoot_jNGeomGen :
    ιOfRoot q N K hqN data hx hy (ModularCurve.jNGeomGen K N) = y :=
  (SsfrobWlocSkin.exists_algHom_of_root_pair_aux q N K hqN data (LaurentSeries K)
    x₀ y hx hy).choose_spec.2

private theorem exists_order_ne_zero_of_order_sub_pos {a : K}
    (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) :
    ∃ z, ((ιOfRoot q N K hqN data hx hy) z).order ≠ 0 := by
  refine ⟨ModularCurve.jGeomGen K N - algebraMap K _ a, ?_⟩
  rw [map_sub, ιOfRoot_jGeomGen, AlgHom.commutes]
  exact hord.ne'

private def wOfRoot {a : K} (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) :
    AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N) :=
  wOfAlgHom (ιOfRoot q N K hqN data hx hy)
    (exists_order_ne_zero_of_order_sub_pos q N K hqN data hx hy hord)

private def gammaOfRoot {a : K} (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) : ℕ :=
  gammaOfAlgHom (ιOfRoot q N K hqN data hx hy)
    (exists_order_ne_zero_of_order_sub_pos q N K hqN data hx hy hord)

private theorem wOfRoot_ord_j_sub_pos {a : K}
    (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) :
    0 < (wOfRoot q N K hqN data hx hy hord).ord
        (ModularCurve.jGeomGen K N - algebraMap K _ a) := by
  have hγ : (0 : ℤ) < (gammaOfRoot q N K hqN data hx hy hord : ℤ) :=
    Int.natCast_pos.mpr (gammaOfAlgHom_pos _ _)
  have hmul := ord_wOfAlgHom_mul_gamma (ιOfRoot q N K hqN data hx hy)
    (exists_order_ne_zero_of_order_sub_pos q N K hqN data hx hy hord)
    (ModularCurve.jGeomGen K N - algebraMap K _ a)
  rw [map_sub, ιOfRoot_jGeomGen, AlgHom.commutes] at hmul
  by_contra hn
  push Not at hn
  have hprod : (wOfRoot q N K hqN data hx hy hord).ord
      (ModularCurve.jGeomGen K N - algebraMap K _ a)
        * (gammaOfRoot q N K hqN data hx hy hord : ℤ) ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inr ⟨hn, hγ.le⟩)
  rw [show (wOfRoot q N K hqN data hx hy hord : Place K _) = wOfAlgHom _ _ from rfl,
    show (gammaOfRoot q N K hqN data hx hy hord : ℤ)
      = ((gammaOfAlgHom _ _ : ℕ) : ℤ) from rfl, hmul] at hprod
  exact absurd hprod (not_le.mpr hord)

end RootPair
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre"

end ModularCurve.EllFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end Brick_ELL4B_A
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

section Brick_ELL4B_B

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine Polynomial

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
namespace EllFam
p2m_open "ModularCurve"

section Generic

variable {L : Type*} [CommRing L]

private theorem j_congr {W₁ W₂ : WeierstrassCurve L} (h : W₁ = W₂)
    {inst₁ : W₁.IsElliptic} {inst₂ : W₂.IsElliptic} :
    @WeierstrassCurve.j L _ W₁ inst₁ = @WeierstrassCurve.j L _ W₂ inst₂ := by
  subst h; congr 1

end Generic
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

section Plumbing

variable {R L M : Type*} [CommRing R] [Field L] [Field M] [DecidableEq L] [DecidableEq M]
  [Algebra R L] [Algebra R M] [Algebra L M] [IsScalarTower R L M]
  (W' : WeierstrassCurve R)

omit [DecidableEq L] [DecidableEq M] in

private theorem baseChange_map_eq :
    (W'⁄L).map (algebraMap L M) = W'⁄M :=
  (WeierstrassCurve.map_map W' (algebraMap R L) (algebraMap L M)).trans
    (congrArg W'.map (IsScalarTower.algebraMap_eq R L M).symm)

private theorem addOrderOf_pointMap (Q : (W'⁄L).toAffine.Point) :
    addOrderOf (Point.map (W' := W') (IsScalarTower.toAlgHom R L M) Q) = addOrderOf Q :=
  addOrderOf_injective
    (Point.map (W' := W') (IsScalarTower.toAlgHom R L M))
    (Point.map_injective (IsScalarTower.toAlgHom R L M)) Q

private theorem coordsOrZero_pointMap (Q : (W'⁄L).toAffine.Point) :
    (Point.map (W' := W') (IsScalarTower.toAlgHom R L M) Q).coordsOrZero
      = Prod.map (algebraMap L M) (algebraMap L M) Q.coordsOrZero := by
  cases Q with
  | zero => exact Prod.ext (map_zero (algebraMap L M)).symm (map_zero (algebraMap L M)).symm
  | some x y h => rfl

private theorem oddOrderSummingSet_pointMap (Q : (W'⁄L).toAffine.Point) (n : ℕ) :
    (W'⁄M).oddOrderSummingSet (Point.map (W' := W') (IsScalarTower.toAlgHom R L M) Q) n
      = ((W'⁄L).oddOrderSummingSet Q n).image
          (Prod.map (algebraMap L M) (algebraMap L M)) := by
  unfold WeierstrassCurve.oddOrderSummingSet
  rw [Finset.image_image]
  congr 1
  funext k
  rw [Function.comp_apply,
    show k • Point.map (W' := W') (IsScalarTower.toAlgHom R L M) Q
      = Point.map (W' := W') (IsScalarTower.toAlgHom R L M) (k • Q) from
      (map_nsmul (Point.map (W' := W') (IsScalarTower.toAlgHom R L M)) k Q).symm,
    coordsOrZero_pointMap]

omit [DecidableEq L] [DecidableEq M] in

private theorem fibrePoly_map (Φ : Polynomial (Polynomial ℤ)) (a : L) :
    ModularCurve.fibrePoly Φ (algebraMap L M a)
      = (ModularCurve.fibrePoly Φ a).map (algebraMap L M) := by
  unfold ModularCurve.fibrePoly
  rw [Polynomial.map_map]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_X]

private theorem j_veluQuotient_pointMap (Q : (W'⁄L).toAffine.Point) (n : ℕ)
    (hI : ((W'⁄L).veluQuotient ((W'⁄L).oddOrderSummingSet Q n)).IsElliptic)
    (hI' : ((W'⁄M).veluQuotient ((W'⁄M).oddOrderSummingSet
        (Point.map (W' := W') (IsScalarTower.toAlgHom R L M) Q) n)).IsElliptic) :
    @WeierstrassCurve.j M _ _ hI'
      = algebraMap L M (@WeierstrassCurve.j L _ _ hI) := by
  obtain ⟨hI'', hjeq⟩ := WeierstrassCurve.exists_isElliptic_map_veluQuotient_j
    (W := W'⁄L) (f := algebraMap L M) (S := (W'⁄L).oddOrderSummingSet Q n) hI
  rw [← hjeq]
  refine j_congr ?_
  rw [oddOrderSummingSet_pointMap W' Q n]
  exact congrArg (fun V : WeierstrassCurve M =>
    V.veluQuotient (((W'⁄L).oddOrderSummingSet Q n).image
      (Prod.map (algebraMap L M) (algebraMap L M)))) (baseChange_map_eq W').symm

end Plumbing
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

section Main

variable {R L M : Type*} [CommRing R] [Field L] [Field M] [DecidableEq L] [DecidableEq M]
  [Algebra R L] [Algebra R M] [Algebra L M] [IsScalarTower R L M] [IsAlgClosed M]
  (W' : WeierstrassCurve R) [(W'⁄L).IsElliptic]
  {ℓ : ℕ} [Fact ℓ.Prime] (data : ModularCurve.ModularPolynomialData ℓ)

private theorem isRoot_fibrePoly_j_veluQuotient (hℓ2 : ℓ ≠ 2) (hℓM : (ℓ : M) ≠ 0)
    (Q : (W'⁄L).toAffine.Point) (_hQ : addOrderOf Q = ℓ)
    (hΔQ : ((W'⁄L).veluQuotient ((W'⁄L).oddOrderSummingSet Q (ℓ / 2))).Δ ≠ 0)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Qb : ι → (W'⁄M).toAffine.Point) (hQb : ∀ i, addOrderOf (Qb i) = ℓ)
    (hinj : Function.Injective fun i => AddSubgroup.zmultiples (Qb i))
    (hΔb : ∀ i, ((W'⁄M).veluQuotient ((W'⁄M).oddOrderSummingSet (Qb i) (ℓ / 2))).Δ ≠ 0)
    (i₀ : ι) (hi₀ : Qb i₀ = Point.map (W' := W') (IsScalarTower.toAlgHom R L M) Q) :
    haveI hI : ((W'⁄L).veluQuotient ((W'⁄L).oddOrderSummingSet Q (ℓ / 2))).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr hΔQ⟩
    (ModularCurve.fibrePoly data.Φ (W'⁄L).j).IsRoot
      (@WeierstrassCurve.j L _ _ hI) := by
  haveI hEM : (W'⁄M).IsElliptic :=
    baseChange_map_eq (L := L) (M := M) W' ▸
      inferInstanceAs ((W'⁄L).map (algebraMap L M)).IsElliptic
  haveI hI : ((W'⁄L).veluQuotient ((W'⁄L).oddOrderSummingSet Q (ℓ / 2))).IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr hΔQ⟩

  have hprod := ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j
    (K := M) hℓ2 hℓM data (W'⁄M) hι Qb hQb hinj hΔb

  have hrootM : (ModularCurve.fibrePoly data.Φ (W'⁄M).j).IsRoot
      (@WeierstrassCurve.j M _ _ ⟨isUnit_iff_ne_zero.mpr (hΔb i₀)⟩) := by
    rw [hprod, Polynomial.isRoot_prod]
    exact ⟨i₀, Finset.mem_univ i₀, by
      rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]⟩

  have hjM : @WeierstrassCurve.j M _ _ ⟨isUnit_iff_ne_zero.mpr (hΔb i₀)⟩
      = algebraMap L M (@WeierstrassCurve.j L _ _ hI) := by
    refine (j_congr ?_).trans
      (j_veluQuotient_pointMap W' Q (ℓ / 2) hI ⟨isUnit_iff_ne_zero.mpr ?_⟩)
    · exact congrArg ((W'⁄M).veluQuotient <| (W'⁄M).oddOrderSummingSet · (ℓ / 2)) hi₀
    · rw [← hi₀]; exact hΔb i₀

  have hjW : (W'⁄M).j = algebraMap L M (W'⁄L).j :=
    (j_congr (inst₂ := inferInstance)
      (baseChange_map_eq (L := L) (M := M) W').symm).trans ((W'⁄L).map_j (algebraMap L M))
  rw [hjM, hjW, fibrePoly_map] at hrootM
  exact hrootM.of_map (algebraMap L M).injective

end Main
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end ModularCurve.EllFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end Brick_ELL4B_B
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

section Brick_ELL4B_C2

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
namespace EllFam
p2m_open "ModularCurve"

open AddSubgroup

variable {G : Type*} [AddCommGroup G] {ℓ : ℕ} [Fact ℓ.Prime]

private theorem finite_zmultiples_of_addOrderOf_eq {v : G} (hv : addOrderOf v = ℓ) :
    Finite (zmultiples v) :=
  Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hv]; exact (Fact.out : ℓ.Prime).pos.ne')

omit [Fact ℓ.Prime] in
private theorem zmultiples_le_torsionBy {v : G} (hv : addOrderOf v = ℓ) :
    (zmultiples v : Set G) ⊆ (Submodule.torsionBy ℤ G (ℓ : ℤ) : Set G) := by
  intro x hx
  obtain ⟨k, rfl⟩ := hx
  have h0 : (ℓ : ℤ) • v = 0 := by
    rw [natCast_zsmul v ℓ, ← hv, addOrderOf_nsmul_eq_zero]
  simp only [SetLike.mem_coe, Submodule.mem_torsionBy_iff, smul_comm (ℓ : ℤ) k, h0, smul_zero]

private theorem eq_zero_of_mem_inf_zmultiples {v w : G}
    (hw : addOrderOf w = ℓ) (hnm : w ∉ zmultiples v)
    {x : G} (hxv : x ∈ zmultiples v) (hxw : x ∈ zmultiples w) : x = 0 := by
  by_contra hx0
  have hxord : addOrderOf x = ℓ := by
    obtain ⟨k, rfl⟩ := hxw
    refine addOrderOf_eq_prime ?_ hx0
    rw [smul_comm, show ((ℓ : ℕ) • w = 0) from hw ▸ addOrderOf_nsmul_eq_zero w, smul_zero]
  have heqx : zmultiples x = zmultiples w := by
    haveI := finite_zmultiples_of_addOrderOf_eq hw
    exact AddSubgroup.eq_of_le_of_card_ge (zmultiples_le_of_mem hxw)
      (by rw [Nat.card_zmultiples, Nat.card_zmultiples, hxord, hw])
  exact hnm (zmultiples_le_of_mem hxv (heqx.symm ▸ mem_zmultiples w))

private theorem dvd_of_zsmul_eq_zsmul {v w : G} (hv : addOrderOf v = ℓ)
    (hw : addOrderOf w = ℓ) (hnm : w ∉ zmultiples v)
    {a b : ℤ} (h : a • v = b • w) : (ℓ : ℤ) ∣ a := by
  have h0 : a • v = 0 :=
    eq_zero_of_mem_inf_zmultiples hw hnm (zsmul_mem_zmultiples v a)
      (h ▸ zsmul_mem_zmultiples w b)
  have hdvd := addOrderOf_dvd_iff_zsmul_eq_zero.mpr h0
  rwa [hv] at hdvd

private def zmFamily (v w : G) : Fin (ℓ + 1) → G :=
  Fin.cases v (fun k => w + (k : ℕ) • v)

omit [Fact ℓ.Prime] in
@[scoped simp] private theorem zmFamily_zero (v w : G) : zmFamily (ℓ := ℓ) v w 0 = v := rfl

omit [Fact ℓ.Prime] in
@[scoped simp] private theorem zmFamily_succ (v w : G) (k : Fin ℓ) :
    zmFamily (ℓ := ℓ) v w k.succ = w + (k : ℕ) • v := rfl

private theorem addOrderOf_zmFamily {v w : G} (hv : addOrderOf v = ℓ)
    (hw : addOrderOf w = ℓ) (hnm : w ∉ zmultiples v)
    (i : Fin (ℓ + 1)) : addOrderOf (zmFamily (ℓ := ℓ) v w i) = ℓ := by
  refine Fin.cases (by rwa [zmFamily_zero]) (fun k => ?_) i
  rw [zmFamily_succ]
  refine addOrderOf_eq_prime ?_ ?_
  · rw [smul_add, show ((ℓ : ℕ) • w = 0) from hw ▸ addOrderOf_nsmul_eq_zero w, zero_add,
      smul_comm, show ((ℓ : ℕ) • v = 0) from hv ▸ addOrderOf_nsmul_eq_zero v, smul_zero]
  · intro h
    refine hnm ?_
    rw [show w = -((k : ℕ) • v) from eq_neg_of_add_eq_zero_left h]
    exact neg_mem (nsmul_mem_zmultiples v _)

private theorem notMem_zmultiples_symm {v w : G} (hv : addOrderOf v = ℓ)
    (hw : addOrderOf w = ℓ) (hnm : w ∉ zmultiples v) :
    v ∉ zmultiples w := fun hv' => by
  haveI := finite_zmultiples_of_addOrderOf_eq hw
  exact hnm ((AddSubgroup.eq_of_le_of_card_ge (zmultiples_le_of_mem hv')
    (by rw [Nat.card_zmultiples, Nat.card_zmultiples, hv, hw])).symm ▸ mem_zmultiples w)

private theorem zmultiples_zmFamily_injective {v w : G} (hv : addOrderOf v = ℓ)
    (hw : addOrderOf w = ℓ) (hnm : w ∉ zmultiples v) :
    Function.Injective fun i : Fin (ℓ + 1) => zmultiples (zmFamily (ℓ := ℓ) v w i) := by

  have hne0 : ∀ k : Fin ℓ, zmultiples v ≠ zmultiples (w + (k : ℕ) • v) := fun k heq => by
    have hmem : w + (k : ℕ) • v ∈ zmultiples v := heq ▸ mem_zmultiples _
    exact hnm (by simpa using sub_mem hmem (nsmul_mem_zmultiples v (k : ℕ)))
  intro i j hij
  induction i using Fin.cases with
  | zero =>
    induction j using Fin.cases with
    | zero => rfl
    | succ k => exact absurd hij (by simpa using hne0 k)
  | succ j' =>
    induction j using Fin.cases with
    | zero => exact absurd hij.symm (by simpa using hne0 j')
    | succ k =>
      congr 1
      simp only [zmFamily_succ] at hij
      have hmem : w + (j' : ℕ) • v ∈ zmultiples (w + (k : ℕ) • v) := hij ▸ mem_zmultiples _
      obtain ⟨m, hm⟩ := hmem
      beta_reduce at hm
      rw [← natCast_zsmul v (k : ℕ), ← natCast_zsmul v (j' : ℕ), smul_add, smul_smul] at hm

      have key : (((j' : ℕ) : ℤ) - m * ((k : ℕ) : ℤ)) • v = (m - 1) • w := by
        rw [sub_smul, sub_smul, one_smul, sub_eq_sub_iff_add_eq_add]
        exact (add_comm _ _).trans hm.symm
      have h1 : (ℓ : ℤ) ∣ ((j' : ℕ) : ℤ) - m * ((k : ℕ) : ℤ) := dvd_of_zsmul_eq_zsmul hv hw hnm key
      have h2 : (ℓ : ℤ) ∣ m - 1 :=
        dvd_of_zsmul_eq_zsmul hw hv (notMem_zmultiples_symm hv hw hnm) key.symm
      have h3 : (ℓ : ℤ) ∣ ((j' : ℕ) : ℤ) - ((k : ℕ) : ℤ) := by
        have hsplit : ((j' : ℕ) : ℤ) - ((k : ℕ) : ℤ)
            = (((j' : ℕ) : ℤ) - m * ((k : ℕ) : ℤ)) + (m - 1) * ((k : ℕ) : ℤ) := by ring
        rw [hsplit]
        exact dvd_add h1 (dvd_mul_of_dvd_left h2 _)
      have hj := j'.isLt
      have hk := k.isLt
      rcases le_total ((j' : ℕ) : ℤ) ((k : ℕ) : ℤ) with hle | hle
      · have h0 : ((k : ℕ) : ℤ) - ((j' : ℕ) : ℤ) = 0 :=
          Int.eq_zero_of_dvd_of_nonneg_of_lt (n := (ℓ : ℤ)) (by omega) (by omega)
            (by rw [← neg_sub]; exact h3.neg_right)
        exact Fin.ext (by omega)
      · have h0 : ((j' : ℕ) : ℤ) - ((k : ℕ) : ℤ) = 0 :=
          Int.eq_zero_of_dvd_of_nonneg_of_lt (n := (ℓ : ℤ)) (by omega) (by omega) h3
        exact Fin.ext (by omega)

private theorem exists_addOrderOf_eq_and_notMem_zmultiples {v : G} (hv : addOrderOf v = ℓ)
    (hcard : Nat.card (Submodule.torsionBy ℤ G (ℓ : ℤ)) = ℓ ^ 2) :
    ∃ w : G, addOrderOf w = ℓ ∧ w ∉ zmultiples v := by
  haveI hfin : Finite (Submodule.torsionBy ℤ G (ℓ : ℤ)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact (pow_pos (Fact.out : ℓ.Prime).pos 2).ne')
  have hsub : (zmultiples v : Set G) ⊆ (Submodule.torsionBy ℤ G (ℓ : ℤ) : Set G) :=
    zmultiples_le_torsionBy hv
  have hlt : (zmultiples v : Set G).ncard < (Submodule.torsionBy ℤ G (ℓ : ℤ) : Set G).ncard := by
    rw [show (zmultiples v : Set G).ncard = Nat.card (zmultiples v) from
        (Nat.card_coe_set_eq _).symm,
      show (Submodule.torsionBy ℤ G (ℓ : ℤ) : Set G).ncard
        = Nat.card (Submodule.torsionBy ℤ G (ℓ : ℤ)) from (Nat.card_coe_set_eq _).symm,
      Nat.card_zmultiples, hv, hcard, sq]
    exact (Nat.lt_mul_iff_one_lt_left (Fact.out : ℓ.Prime).pos).mpr (Fact.out : ℓ.Prime).one_lt
  obtain ⟨w, hwt, hwn⟩ := Set.exists_of_ssubset
    (hsub.ssubset_of_ne (fun heq => hlt.ne (by rw [heq])))
  refine ⟨w, ?_, hwn⟩
  refine addOrderOf_eq_prime ?_ (fun h0 => hwn (h0 ▸ zero_mem _))
  have hmem := (Submodule.mem_torsionBy_iff _ _).mp (SetLike.mem_coe.mp hwt)
  rwa [natCast_zsmul w ℓ] at hmem

private theorem exists_fin_family_zmultiples_injective {v : G} (hv : addOrderOf v = ℓ)
    (hcard : Nat.card (Submodule.torsionBy ℤ G (ℓ : ℤ)) = ℓ ^ 2) :
    ∃ Qb : Fin (ℓ + 1) → G, (∀ i, addOrderOf (Qb i) = ℓ) ∧
      Function.Injective (fun i => zmultiples (Qb i)) ∧ Qb 0 = v := by
  obtain ⟨w, hw, hnm⟩ := exists_addOrderOf_eq_and_notMem_zmultiples hv hcard
  exact ⟨zmFamily v w, addOrderOf_zmFamily hv hw hnm,
    zmultiples_zmFamily_injective hv hw hnm, rfl⟩

end ModularCurve.EllFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end Brick_ELL4B_C2
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

section Brick_ELL6_A2

set_option autoImplicit false

noncomputable section

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve"

namespace SsfrobR4a

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

private theorem order_inv (s : LaurentSeries K) (hs : s ≠ 0) : s⁻¹.order = -s.order := by
  have h := HahnSeries.order_mul hs (inv_ne_zero hs)
  rw [mul_inv_cancel₀ hs, HahnSeries.order_one] at h
  omega

private theorem map_ne_zero_of_ne_zero (ι : F →ₐ[K] LaurentSeries K) {f : F} (hf : f ≠ 0) : ι f ≠ 0 :=
  (map_ne_zero ι.toRingHom).mpr hf

section Induce

variable (w : Place K F) (ι : F →ₐ[K] LaurentSeries K)
  (hι : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order)
include hι

private theorem ord_pos_iff_order_pos {f : F} (hf : f ≠ 0) : 0 < w.ord f ↔ 0 < (ι f).order := by
  have hιf : ι f ≠ 0 := map_ne_zero_of_ne_zero ι hf
  have key : f⁻¹ ∈ w.toValuationSubring ↔ 0 ≤ -(ι f).order := by
    rw [hι, map_inv₀, order_inv _ hιf]
  rw [w.mem_iff_ord_nonneg (inv_ne_zero hf), w.ord_inv] at key
  constructor
  · intro hpos
    by_contra hle
    have h1 : 0 ≤ -(ι f).order := by omega
    have h2 := key.mpr h1
    omega
  · intro hpos
    by_contra hle
    have h1 : 0 ≤ -w.ord f := by omega
    have h2 := key.mp h1
    omega

end Induce
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

private theorem algHom_eq_of_apply_eq_of_ord_eq_one (w : Place K F) (x : F) (hx : w.ord x = 1)
    (ι ι' : F →ₐ[K] LaurentSeries K) (hιx : ι x = ι' x)
    (hι : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order)
    (hι' : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι' f).order) : ι = ι' := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hx
    exact zero_ne_one hx
  have hs0 : ι x ≠ 0 := map_ne_zero_of_ne_zero ι hx0
  have hm : 0 < (ι x).order :=
    (ord_pos_iff_order_pos w ι hι hx0).mp (by rw [hx]; exact one_pos)

  have key : ∀ n : ℕ, ∀ g : F, g ∈ w.toValuationSubring →
      ι g - ι' g = 0 ∨ (n : ℤ) * (ι x).order ≤ (ι g - ι' g).order := by
    intro n
    induction n with
    | zero =>
      intro g hg
      by_cases hd : ι g - ι' g = 0
      · exact Or.inl hd
      · right
        rw [Nat.cast_zero, zero_mul]
        have h1 : 0 ≤ (ι g).order := (hι g).mp hg
        have h2 : 0 ≤ (ι' g).order := (hι' g).mp hg
        have hd' : ι g + -(ι' g) ≠ 0 := by rwa [← sub_eq_add_neg]
        have h3 := HahnSeries.min_order_le_order_add hd'
        rw [HahnSeries.order_neg, ← sub_eq_add_neg] at h3
        exact le_trans (le_min h1 h2) h3
    | succ n ih =>
      intro f hf
      obtain ⟨c, hc⟩ : ∃ c : K, c = (ι f).coeff 0 := ⟨_, rfl⟩
      obtain ⟨g, hg⟩ : ∃ g : F, g = (f - algebraMap K F c) * x⁻¹ := ⟨_, rfl⟩
      have hf₁mem : f - algebraMap K F c ∈ w.toValuationSubring :=
        sub_mem hf (w.algebraMap_mem' c)
      have hxg : x * g = f - algebraMap K F c := by
        rw [hg, mul_comm, inv_mul_cancel_right₀ hx0]
      have hfg : f = algebraMap K F c + x * g := by
        rw [hxg]
        ring

      have hgmem : g ∈ w.toValuationSubring := by
        by_cases hf₁0 : f - algebraMap K F c = 0
        · rw [hg, hf₁0, zero_mul]
          exact zero_mem _
        · have hcoeff : (ι (f - algebraMap K F c)).coeff 0 = 0 := by
            rw [map_sub, AlgHom.commutes, algebraMap_laurentSeries_eq_single]
            simp [hc]
          have hord0 : 0 ≤ (ι (f - algebraMap K F c)).order := (hι _).mp hf₁mem
          have hιf₁ : ι (f - algebraMap K F c) ≠ 0 := map_ne_zero_of_ne_zero ι hf₁0
          have hord_ne : (ι (f - algebraMap K F c)).order ≠ 0 := by
            intro h0
            apply hιf₁
            rw [← HahnSeries.coeff_order_eq_zero, h0]
            exact hcoeff
          have hordpos : 0 < (ι (f - algebraMap K F c)).order :=
            lt_of_le_of_ne hord0 (Ne.symm hord_ne)
          have hw1 : 0 < w.ord (f - algebraMap K F c) :=
            (ord_pos_iff_order_pos w ι hι hf₁0).mpr hordpos
          have hg0 : g ≠ 0 := by
            rw [hg]
            exact mul_ne_zero hf₁0 (inv_ne_zero hx0)
          refine w.mem_of_ord_nonneg hg0 ?_
          rw [hg, w.ord_mul hf₁0 (inv_ne_zero hx0), w.ord_inv, hx]
          omega

      have hdiff : ι f - ι' f = ι x * (ι g - ι' g) := by
        rw [hfg, map_add, map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes, ← hιx]
        ring
      rcases ih g hgmem with h0 | hle
      · left
        rw [hdiff, h0, mul_zero]
      · by_cases hd0 : ι g - ι' g = 0
        · left
          rw [hdiff, hd0, mul_zero]
        · right
          rw [hdiff, HahnSeries.order_mul hs0 hd0, Nat.cast_succ]
          linarith

  have hO : ∀ g : F, g ∈ w.toValuationSubring → ι g = ι' g := by
    intro g hg
    by_contra hne
    have hd : ι g - ι' g ≠ 0 := sub_ne_zero.mpr hne
    rcases key ((ι g - ι' g).order.toNat + 1) g hg with h0 | hle
    · exact hd h0
    · have hN : (((ι g - ι' g).order.toNat + 1 : ℕ) : ℤ)
          ≤ (((ι g - ι' g).order.toNat + 1 : ℕ) : ℤ) * (ι x).order :=
        le_mul_of_one_le_right (Int.natCast_nonneg _) hm
      have h2 : (ι g - ι' g).order < (((ι g - ι' g).order.toNat + 1 : ℕ) : ℤ) := by
        have := Int.self_le_toNat (ι g - ι' g).order
        push_cast
        omega
      omega

  apply AlgHom.ext
  intro f
  by_cases hf : f ∈ w.toValuationSubring
  · exact hO f hf
  · have hinv : f⁻¹ ∈ w.toValuationSubring :=
      (w.toValuationSubring.mem_or_inv_mem f).resolve_left hf
    have h := hO f⁻¹ hinv
    rw [map_inv₀, map_inv₀] at h
    exact inv_injective h

private theorem card_le_one_of_ord_eq_one (w : Place K F) (x : F) (hx : w.ord x = 1)
    (x₀ : LaurentSeries K) (S : Finset (F →ₐ[K] LaurentSeries K))
    (hSx : ∀ ι ∈ S, ι x = x₀)
    (hSw : ∀ ι ∈ S, ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order) :
    S.card ≤ 1 :=
  Finset.card_le_one.mpr fun ι hι ι' hι' =>
    algHom_eq_of_apply_eq_of_ord_eq_one w x hx ι ι' ((hSx ι hι).trans (hSx ι' hι').symm)
      (hSw ι hι) (hSw ι' hι')

private theorem card_le_ord_of_ord_eq_one (w : Place K F) (x : F) (hx : w.ord x = 1)
    (x₀ : LaurentSeries K) (S : Finset (F →ₐ[K] LaurentSeries K))
    (hSx : ∀ ι ∈ S, ι x = x₀)
    (hSw : ∀ ι ∈ S, ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order) :
    (S.card : ℤ) ≤ w.ord x := by
  rw [hx]
  exact_mod_cast card_le_one_of_ord_eq_one w x hx x₀ S hSx hSw

private def Deep (N : ℤ) (d : LaurentSeries K) : Prop := d = 0 ∨ N ≤ d.order

private theorem Deep.mono {N N' : ℤ} {d : LaurentSeries K} (h : Deep N' d) (hle : N ≤ N') : Deep N d := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans hle h)

private theorem Deep.of_le {N : ℤ} {d : LaurentSeries K} (h : N ≤ d.order) : Deep N d := Or.inr h

private theorem Deep.add {N : ℤ} {d d' : LaurentSeries K} (h : Deep N d) (h' : Deep N d') :
    Deep N (d + d') := by
  rcases h with rfl | h
  · rwa [zero_add]
  rcases h' with rfl | h'
  · rw [add_zero]
    exact Or.inr h
  by_cases hs : d + d' = 0
  · exact Or.inl hs
  · exact Or.inr (le_trans (le_min h h') (HahnSeries.min_order_le_order_add hs))

private theorem Deep.neg {N : ℤ} {d : LaurentSeries K} (h : Deep N d) : Deep N (-d) := by
  rcases h with rfl | h
  · rw [neg_zero]
    exact Or.inl rfl
  · right
    rwa [HahnSeries.order_neg]

private theorem Deep.sub {N : ℤ} {d d' : LaurentSeries K} (h : Deep N d) (h' : Deep N d') :
    Deep N (d - d') := by
  rw [sub_eq_add_neg]
  exact h.add h'.neg

private theorem Deep.mul {N N' : ℤ} {d d' : LaurentSeries K} (h : Deep N d) (h' : Deep N' d') :
    Deep (N + N') (d * d') := by
  rcases h with rfl | h
  · rw [zero_mul]
    exact Or.inl rfl
  rcases h' with rfl | h'
  · rw [mul_zero]
    exact Or.inl rfl
  by_cases hd : d = 0
  · rw [hd, zero_mul]
    exact Or.inl rfl
  by_cases hd' : d' = 0
  · rw [hd', mul_zero]
    exact Or.inl rfl
  right
  rw [HahnSeries.order_mul hd hd']
  omega

private theorem Deep.order_le {N : ℤ} {d : LaurentSeries K} (h : Deep N d) (hd : d ≠ 0) : N ≤ d.order := by
  rcases h with h | h
  · exact absurd h hd
  · exact h

section Induce2

variable (w : Place K F) (ι : F →ₐ[K] LaurentSeries K)
  (hι : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order)
include hι

private theorem order_eq_zero_of_ord_eq_zero {v : F} (hv0 : v ≠ 0) (hv : w.ord v = 0) :
    (ι v).order = 0 := by
  have h1 : 0 ≤ (ι v).order := (hι v).mp (w.mem_of_ord_nonneg hv0 (by rw [hv]))
  have h2 : 0 ≤ (ι v⁻¹).order :=
    (hι v⁻¹).mp (w.mem_of_ord_nonneg (inv_ne_zero hv0) (by rw [w.ord_inv, hv, neg_zero]))
  rw [map_inv₀, order_inv _ (map_ne_zero_of_ne_zero ι hv0)] at h2
  omega

private theorem exists_eq_algebraMap_add_mul (t : F) (ht : w.ord t = 1) {f : F}
    (hf : f ∈ w.toValuationSubring) :
    ∃ c : K, ∃ g : F, g ∈ w.toValuationSubring ∧ f = algebraMap K F c + t * g := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at ht
    exact zero_ne_one ht
  obtain ⟨c, hc⟩ : ∃ c : K, c = (ι f).coeff 0 := ⟨_, rfl⟩
  obtain ⟨g, hg⟩ : ∃ g : F, g = (f - algebraMap K F c) * t⁻¹ := ⟨_, rfl⟩
  have hf₁mem : f - algebraMap K F c ∈ w.toValuationSubring :=
    sub_mem hf (w.algebraMap_mem' c)
  have hxg : t * g = f - algebraMap K F c := by
    rw [hg, mul_comm, inv_mul_cancel_right₀ ht0]
  refine ⟨c, g, ?_, by rw [hxg]; ring⟩
  by_cases hf₁0 : f - algebraMap K F c = 0
  · rw [hg, hf₁0, zero_mul]
    exact zero_mem _
  · have hcoeff : (ι (f - algebraMap K F c)).coeff 0 = 0 := by
      rw [map_sub, AlgHom.commutes, algebraMap_laurentSeries_eq_single]
      simp [hc]
    have hord0 : 0 ≤ (ι (f - algebraMap K F c)).order := (hι _).mp hf₁mem
    have hιf₁ : ι (f - algebraMap K F c) ≠ 0 := map_ne_zero_of_ne_zero ι hf₁0
    have hord_ne : (ι (f - algebraMap K F c)).order ≠ 0 := by
      intro h0
      apply hιf₁
      rw [← HahnSeries.coeff_order_eq_zero, h0]
      exact hcoeff
    have hordpos : 0 < (ι (f - algebraMap K F c)).order :=
      lt_of_le_of_ne hord0 (Ne.symm hord_ne)
    have hw1 : 0 < w.ord (f - algebraMap K F c) :=
      (ord_pos_iff_order_pos w ι hι hf₁0).mpr hordpos
    have hg0 : g ≠ 0 := by
      rw [hg]
      exact mul_ne_zero hf₁0 (inv_ne_zero ht0)
    refine w.mem_of_ord_nonneg hg0 ?_
    rw [hg, w.ord_mul hf₁0 (inv_ne_zero ht0), w.ord_inv, ht]
    omega

end Induce2
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

private theorem coeff_zero_eq_of_mem (w : Place K F) (ι ι' : F →ₐ[K] LaurentSeries K)
    (hι : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order)
    (hι' : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι' f).order)
    {v : F} (hv : v ∈ w.toValuationSubring) : (ι v).coeff 0 = (ι' v).coeff 0 := by
  obtain ⟨c, hc⟩ : ∃ c : K, c = (ι v).coeff 0 := ⟨_, rfl⟩
  have hmem : v - algebraMap K F c ∈ w.toValuationSubring := sub_mem hv (w.algebraMap_mem' c)
  have key : (ι' (v - algebraMap K F c)).coeff 0 = 0 := by
    by_cases h0 : v - algebraMap K F c = 0
    · rw [h0, map_zero]
      rfl
    · have hcoeff : (ι (v - algebraMap K F c)).coeff 0 = 0 := by
        rw [map_sub, AlgHom.commutes, algebraMap_laurentSeries_eq_single]
        simp [hc]
      have hord0 : 0 ≤ (ι (v - algebraMap K F c)).order := (hι _).mp hmem
      have hι0 : ι (v - algebraMap K F c) ≠ 0 := map_ne_zero_of_ne_zero ι h0
      have hord_ne : (ι (v - algebraMap K F c)).order ≠ 0 := by
        intro h00
        apply hι0
        rw [← HahnSeries.coeff_order_eq_zero, h00]
        exact hcoeff
      have hpos : 0 < w.ord (v - algebraMap K F c) :=
        (ord_pos_iff_order_pos w ι hι h0).mpr (lt_of_le_of_ne hord0 (Ne.symm hord_ne))
      have hpos' : 0 < (ι' (v - algebraMap K F c)).order :=
        (ord_pos_iff_order_pos w ι' hι' h0).mp hpos
      exact HahnSeries.coeff_eq_zero_of_lt_order hpos'
  rw [map_sub, AlgHom.commutes, algebraMap_laurentSeries_eq_single] at key
  simp only [HahnSeries.coeff_sub', Pi.sub_apply, HahnSeries.coeff_single_same] at key
  rw [← hc]
  exact (sub_eq_zero.mp key).symm

private theorem deep_sub_of_mem (w : Place K F) (t : F) (ht : w.ord t = 1)
    (ι ι' : F →ₐ[K] LaurentSeries K)
    (hι : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order)
    (hι' : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι' f).order)
    (k : ℤ) (hk : Deep k (ι t - ι' t)) :
    ∀ n : ℕ, ∀ f : F, f ∈ w.toValuationSubring → Deep (min (n : ℤ) k) (ι f - ι' f) := by
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at ht
    exact zero_ne_one ht
  have hγ : 1 ≤ (ι t).order := (ord_pos_iff_order_pos w ι hι ht0).mp (by rw [ht]; exact one_pos)
  intro n
  induction n with
  | zero =>
    intro f hf
    have h1 : Deep 0 (ι f) := Deep.of_le ((hι f).mp hf)
    have h2 : Deep 0 (ι' f) := Deep.of_le ((hι' f).mp hf)
    exact (h1.sub h2).mono (by simp)
  | succ n ih =>
    intro f hf
    obtain ⟨c, g, hg, hfg⟩ := exists_eq_algebraMap_add_mul w ι hι t ht hf
    have hdiff : ι f - ι' f = ι t * (ι g - ι' g) + (ι t - ι' t) * ι' g := by
      rw [hfg, map_add, map_add, map_mul, map_mul, AlgHom.commutes, AlgHom.commutes]
      ring
    rw [hdiff]
    refine Deep.add ?_ ?_
    · have h1 : Deep (ι t).order (ι t) := Deep.of_le le_rfl
      have h2 := h1.mul (ih g hg)
      refine h2.mono ?_
      rw [Nat.cast_succ]
      rcases le_total (n : ℤ) k with hnk | hnk
      · rw [min_eq_left hnk]
        have : min ((n : ℤ) + 1) k ≤ (n : ℤ) + 1 := min_le_left _ _
        omega
      · rw [min_eq_right hnk]
        have : min ((n : ℤ) + 1) k ≤ k := min_le_right _ _
        omega
    · have h2 : Deep 0 (ι' g) := Deep.of_le ((hι' g).mp hg)
      have h3 := hk.mul h2
      rw [add_zero] at h3
      exact h3.mono (min_le_right _ _)

private theorem deep_order_sub_of_mem (w : Place K F) (t : F) (ht : w.ord t = 1)
    (ι ι' : F →ₐ[K] LaurentSeries K)
    (hι : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order)
    (hι' : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι' f).order)
    {f : F} (hf : f ∈ w.toValuationSubring) :
    Deep (ι t - ι' t).order (ι f - ι' f) := by
  have h := deep_sub_of_mem w t ht ι ι' hι hι' (ι t - ι' t).order (Deep.of_le le_rfl)
    ((ι t - ι' t).order.toNat) f hf
  rwa [min_eq_right (Int.self_le_toNat _)] at h

private theorem leadingCoeff_pow (x : LaurentSeries K) (n : ℕ) :
    (x ^ n).leadingCoeff = x.leadingCoeff ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, HahnSeries.leadingCoeff_one]
  | succ n ih => rw [pow_succ, pow_succ, HahnSeries.leadingCoeff_mul, ih]

private theorem order_lt_order_sub {A B : LaurentSeries K} (hA : A ≠ 0) (hAB : A - B ≠ 0)
    (ho : A.order = B.order) (hlc : A.leadingCoeff = B.leadingCoeff) :
    A.order < (A - B).order := by
  have hB : B ≠ 0 := by
    rintro rfl
    rw [HahnSeries.leadingCoeff_zero, HahnSeries.leadingCoeff_eq_zero] at hlc
    exact hA hlc
  have hge : A.order ≤ (A - B).order := by
    have h := HahnSeries.min_order_le_order_add (x := A) (y := -B) (by rwa [← sub_eq_add_neg])
    rw [HahnSeries.order_neg, ← ho, min_self, ← sub_eq_add_neg] at h
    exact h
  refine lt_of_le_of_ne hge fun heq => ?_
  have hc : (A - B).coeff (A - B).order = 0 := by
    rw [← heq]
    simp only [HahnSeries.coeff_sub', Pi.sub_apply]
    rw [← HahnSeries.leadingCoeff_eq, ho, ← HahnSeries.leadingCoeff_eq, hlc, sub_self]
  exact hAB (HahnSeries.coeff_order_eq_zero.mp hc)

private theorem geom_sum₂_ne_zero_and_order {A B : LaurentSeries K} (hA : A ≠ 0) (hB : B ≠ 0)
    (ho : A.order = B.order) (hlc : A.leadingCoeff = B.leadingCoeff) (e : ℕ) (he : (e : K) ≠ 0) :
    (∑ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i)) ≠ 0 ∧
      (∑ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i)).order = ((e - 1 : ℕ) : ℤ) * A.order := by
  have he0 : e ≠ 0 := by
    rintro rfl
    exact he Nat.cast_zero
  have h1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
  have ha : A.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hA

  have hterm_ne : ∀ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i) ≠ 0 := fun i _ =>
    mul_ne_zero (pow_ne_zero _ hA) (pow_ne_zero _ hB)
  have hterm_ord : ∀ i ∈ Finset.range e,
      (A ^ i * B ^ (e - 1 - i)).order = ((e - 1 : ℕ) : ℤ) * A.order := by
    intro i hi
    have hi' : i ≤ e - 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [HahnSeries.order_mul (pow_ne_zero _ hA) (pow_ne_zero _ hB), HahnSeries.order_pow,
      HahnSeries.order_pow, ← ho, nsmul_eq_mul, nsmul_eq_mul, ← add_mul, ← Nat.cast_add,
      Nat.add_sub_cancel' hi']
  have hterm_lc : ∀ i ∈ Finset.range e,
      (A ^ i * B ^ (e - 1 - i)).leadingCoeff = A.leadingCoeff ^ (e - 1) := by
    intro i hi
    have hi' : i ≤ e - 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [HahnSeries.leadingCoeff_mul, leadingCoeff_pow, leadingCoeff_pow, ← hlc, ← pow_add,
      Nat.add_sub_cancel' hi']

  have hcoeff : (∑ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i)).coeff (((e - 1 : ℕ) : ℤ) * A.order)
      = (e : K) * A.leadingCoeff ^ (e - 1) := by
    rw [HahnSeries.coeff_sum]
    rw [Finset.sum_congr rfl fun i hi => by
      rw [← hterm_ord i hi, ← HahnSeries.leadingCoeff_eq, hterm_lc i hi]]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hcoeff_ne : (∑ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i)).coeff
      (((e - 1 : ℕ) : ℤ) * A.order) ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero he (pow_ne_zero _ ha)
  have hne : (∑ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i)) ≠ 0 := by
    intro h0
    rw [h0] at hcoeff_ne
    exact hcoeff_ne rfl
  refine ⟨hne, le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hcoeff_ne) ?_⟩

  by_contra hlt
  push Not at hlt
  have hz : (∑ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i)).coeff
      (∑ i ∈ Finset.range e, A ^ i * B ^ (e - 1 - i)).order = 0 := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_zero fun i hi => ?_
    exact HahnSeries.coeff_eq_zero_of_lt_order (by rw [hterm_ord i hi]; exact hlt)
  exact hne (HahnSeries.coeff_order_eq_zero.mp hz)

private theorem apply_eq_of_leadingCoeff_eq (w : Place K F) (t : F) (ht : w.ord t = 1)
    (e : ℕ) (he : (e : K) ≠ 0) (v : F) (hv0 : v ≠ 0) (hv : w.ord v = 0)
    (ι ι' : F →ₐ[K] LaurentSeries K)
    (hι : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order)
    (hι' : ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι' f).order)
    (hx : ι (t ^ e * v) = ι' (t ^ e * v))
    (hlc : (ι t).leadingCoeff = (ι' t).leadingCoeff) : ι t = ι' t := by
  have he0 : e ≠ 0 := by
    rintro rfl
    exact he Nat.cast_zero
  have h1 : 1 ≤ e := Nat.one_le_iff_ne_zero.mpr he0
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at ht
    exact zero_ne_one ht
  have hA : ι t ≠ 0 := map_ne_zero_of_ne_zero ι ht0
  have hB : ι' t ≠ 0 := map_ne_zero_of_ne_zero ι' ht0
  have hV : ι v ≠ 0 := map_ne_zero_of_ne_zero ι hv0
  have hV' : ι' v ≠ 0 := map_ne_zero_of_ne_zero ι' hv0
  have hγ : 1 ≤ (ι t).order := (ord_pos_iff_order_pos w ι hι ht0).mp (by rw [ht]; exact one_pos)
  have hVo : (ι v).order = 0 := order_eq_zero_of_ord_eq_zero w ι hι hv0 hv
  have hV'o : (ι' v).order = 0 := order_eq_zero_of_ord_eq_zero w ι' hι' hv0 hv

  rw [map_mul, map_mul, map_pow, map_pow] at hx
  have ho : (ι t).order = (ι' t).order := by
    have h := congrArg HahnSeries.order hx
    rw [HahnSeries.order_mul (pow_ne_zero _ hA) hV, HahnSeries.order_mul (pow_ne_zero _ hB) hV',
      HahnSeries.order_pow, HahnSeries.order_pow, hVo, hV'o, nsmul_eq_mul, nsmul_eq_mul] at h
    have he' : (e : ℤ) ≠ 0 := by exact_mod_cast he0
    exact mul_left_cancel₀ he' (by linarith)
  by_contra hne
  have hδ : ι t - ι' t ≠ 0 := sub_ne_zero.mpr hne
  have hk : (ι t).order < (ι t - ι' t).order := order_lt_order_sub hA hδ ho hlc

  have hvmem : v ∈ w.toValuationSubring := w.mem_of_ord_nonneg hv0 (by rw [hv])
  have hdeep : Deep (ι t - ι' t).order (ι v - ι' v) :=
    deep_order_sub_of_mem w t ht ι ι' hι hι' hvmem

  obtain ⟨hG, hGo⟩ := geom_sum₂_ne_zero_and_order hA hB ho hlc e he
  have hid : (∑ i ∈ Finset.range e, ι t ^ i * ι' t ^ (e - 1 - i)) * (ι t - ι' t) * ι v
      = ι' t ^ e * (ι' v - ι v) := by
    rw [geom_sum₂_mul]
    linear_combination hx
  by_cases hVV : ι' v - ι v = 0
  · rw [hVV, mul_zero] at hid
    exact (mul_ne_zero (mul_ne_zero hG hδ) hV) hid
  · have hL := congrArg HahnSeries.order hid
    rw [HahnSeries.order_mul (mul_ne_zero hG hδ) hV, HahnSeries.order_mul hG hδ, hGo, hVo,
      HahnSeries.order_mul (pow_ne_zero _ hB) hVV, HahnSeries.order_pow, nsmul_eq_mul, ← ho] at hL
    have hR : (ι t - ι' t).order ≤ (ι' v - ι v).order := by
      have h := hdeep.neg
      rw [neg_sub] at h
      exact h.order_le hVV
    have hcast : ((e - 1 : ℕ) : ℤ) = (e : ℤ) - 1 := by omega
    rw [hcast] at hL
    nlinarith

private theorem card_le_ord_of_cast_ne_zero (w : Place K F) (x : F) (hx : 0 < w.ord x)
    (he : ((w.ord x).toNat : K) ≠ 0) (x₀ : LaurentSeries K)
    (S : Finset (F →ₐ[K] LaurentSeries K))
    (hSx : ∀ ι ∈ S, ι x = x₀)
    (hSw : ∀ ι ∈ S, ∀ f : F, f ∈ w.toValuationSubring ↔ 0 ≤ (ι f).order) :
    (S.card : ℤ) ≤ w.ord x := by
  classical

  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have ht : w.ord (π : F) = 1 := w.ord_coe_irreducible hπ
  have ht0 : (π : F) ≠ 0 := by
    intro h0
    rw [h0, Place.ord_zero] at ht
    exact zero_ne_one ht
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hx
    exact lt_irrefl _ hx
  obtain ⟨e, he'⟩ : ∃ e : ℕ, e = (w.ord x).toNat := ⟨_, rfl⟩
  have hecast : (e : ℤ) = w.ord x := by rw [he', Int.toNat_of_nonneg hx.le]
  rw [← he'] at he
  have he0 : e ≠ 0 := by
    rintro rfl
    exact he Nat.cast_zero
  have hepos : 0 < e := Nat.pos_of_ne_zero he0
  obtain ⟨v, hvdef⟩ : ∃ v : F, v = ((π : F) ^ e)⁻¹ * x := ⟨_, rfl⟩
  have hpow0 : (π : F) ^ e ≠ 0 := pow_ne_zero _ ht0
  have hxv : x = (π : F) ^ e * v := by rw [hvdef, mul_inv_cancel_left₀ hpow0]
  have hv0 : v ≠ 0 := by
    rw [hvdef]
    exact mul_ne_zero (inv_ne_zero hpow0) hx0
  have hordpow : w.ord ((π : F) ^ e) = e := by
    rw [← zpow_natCast, w.ord_zpow, ht, mul_one]
  have hv : w.ord v = 0 := by
    rw [hvdef, w.ord_mul (inv_ne_zero hpow0) hx0, w.ord_inv, hordpow, ← hecast]
    ring

  rcases S.eq_empty_or_nonempty with hS | ⟨ι₀, hι₀⟩
  · rw [hS, Finset.card_empty, Nat.cast_zero]
    exact hx.le
  obtain ⟨c, hc⟩ : ∃ c : K, c = (ι₀ v).coeff 0 := ⟨_, rfl⟩
  have hvmem : v ∈ w.toValuationSubring := w.mem_of_ord_nonneg hv0 (by rw [hv])

  have hlcv : ∀ ι ∈ S, (ι v).leadingCoeff = c := by
    intro ι hι
    rw [HahnSeries.leadingCoeff_eq, order_eq_zero_of_ord_eq_zero w ι (hSw ι hι) hv0 hv, hc]
    exact coeff_zero_eq_of_mem w ι ι₀ (hSw ι hι) (hSw ι₀ hι₀) hvmem
  have hc0 : c ≠ 0 := by
    rw [← hlcv ι₀ hι₀]
    exact HahnSeries.leadingCoeff_ne_zero.mpr (map_ne_zero_of_ne_zero ι₀ hv0)
  have hroot : ∀ ι ∈ S, (ι (π : F)).leadingCoeff ^ e = x₀.leadingCoeff * c⁻¹ := by
    intro ι hι
    have h := hSx ι hι
    rw [hxv, map_mul, map_pow] at h
    have hl := congrArg HahnSeries.leadingCoeff h
    rw [HahnSeries.leadingCoeff_mul, leadingCoeff_pow, hlcv ι hι] at hl
    rw [← hl, mul_inv_cancel_right₀ hc0]

  have hmaps : Set.MapsTo (fun ι : F →ₐ[K] LaurentSeries K => (ι (π : F)).leadingCoeff)
      (↑S : Set (F →ₐ[K] LaurentSeries K))
      (↑(Polynomial.nthRoots e (x₀.leadingCoeff * c⁻¹)).toFinset : Set K) := by
    intro ι hι
    rw [Finset.mem_coe] at hι
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hepos]
    exact hroot ι hι
  have hinj : Set.InjOn (fun ι : F →ₐ[K] LaurentSeries K => (ι (π : F)).leadingCoeff)
      (↑S : Set (F →ₐ[K] LaurentSeries K)) := by
    intro ι hι ι' hι' hll
    rw [Finset.mem_coe] at hι hι'
    have hxx : ι ((π : F) ^ e * v) = ι' ((π : F) ^ e * v) := by
      rw [← hxv, hSx ι hι, hSx ι' hι']
    have htt : ι (π : F) = ι' (π : F) :=
      apply_eq_of_leadingCoeff_eq w (π : F) ht e he v hv0 hv ι ι' (hSw ι hι) (hSw ι' hι') hxx hll
    exact algHom_eq_of_apply_eq_of_ord_eq_one w (π : F) ht ι ι' htt (hSw ι hι) (hSw ι' hι')
  have hcard : S.card ≤ (Polynomial.nthRoots e (x₀.leadingCoeff * c⁻¹)).toFinset.card :=
    Finset.card_le_card_of_injOn _ hmaps hinj
  have hroots : (Polynomial.nthRoots e (x₀.leadingCoeff * c⁻¹)).toFinset.card ≤ e :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_nthRoots _ _)
  rw [← hecast]
  exact_mod_cast le_trans hcard hroots

end SsfrobR4a
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end Brick_ELL6_A2
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

section Brick_ELL6_B

set_option autoImplicit false

noncomputable section

open WeierstrassCurve AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
namespace EllFam
p2m_open "ModularCurve"

private def fam1728 (K : Type*) [CommRing K] : WeierstrassCurve (PowerSeries K) :=
  ⟨0, 0, 0, 1, PowerSeries.X⟩

private def fam0 (K : Type*) [CommRing K] : WeierstrassCurve (PowerSeries K) :=
  ⟨0, 0, 1, PowerSeries.X, 0⟩

section Deck

variable {K : Type*} [Field K]

private theorem inv_pow_four_of_pow_four (u : Kˣ) (hu : (u : K) ^ 4 = 1) :
    ((u⁻¹ : Kˣ) : K) ^ 4 = 1 := by
  rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_one]

private theorem inv_pow_six_of_pow_four (u : Kˣ) (hu : (u : K) ^ 4 = 1) :
    ((u⁻¹ : Kˣ) : K) ^ 6 = (u : K) ^ 2 := by
  have h8 : ((u⁻¹ : Kˣ) : K) ^ 6 * (u : K) ^ 6 = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  have hu8 : (u : K) ^ 6 = (u : K) ^ 2 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, pow_add, hu, one_mul]
  have hne : (u : K) ^ 2 ≠ 0 := pow_ne_zero _ u.ne_zero
  rw [hu8] at h8
  have hsq : (u : K) ^ 2 * (u : K) ^ 2 = 1 := by rw [← pow_add]; exact hu
  calc ((u⁻¹ : Kˣ) : K) ^ 6 = ((u⁻¹ : Kˣ) : K) ^ 6 * ((u : K) ^ 2 * (u : K) ^ 2) := by
        rw [hsq, mul_one]
    _ = (((u⁻¹ : Kˣ) : K) ^ 6 * (u : K) ^ 2) * (u : K) ^ 2 := by ring
    _ = (u : K) ^ 2 := by rw [h8, one_mul]

private theorem pow_six_of_aut_ofJ0 (u : Kˣ) (t : K) (ht : t * (1 + t) = 0)
    (hu : (u : K) ^ 3 = 1 + 2 * t) : (u : K) ^ 6 = 1 := by
  calc (u : K) ^ 6 = ((u : K) ^ 3) ^ 2 := by ring
    _ = 1 + 4 * (t * (1 + t)) := by rw [hu]; ring
    _ = 1 := by rw [ht, mul_zero, add_zero]

private theorem inv_pow_four_of_aut_ofJ0 (u : Kˣ) (t : K) (ht : t * (1 + t) = 0)
    (hu : (u : K) ^ 3 = 1 + 2 * t) : ((u⁻¹ : Kˣ) : K) ^ 4 = (u : K) ^ 2 := by
  have h6 := pow_six_of_aut_ofJ0 u t ht hu
  have h : ((u⁻¹ : Kˣ) : K) ^ 4 * (u : K) ^ 4 = 1 := by
    rw [← mul_pow, Units.inv_mul, one_pow]
  calc ((u⁻¹ : Kˣ) : K) ^ 4 = ((u⁻¹ : Kˣ) : K) ^ 4 * (u : K) ^ 6 := by rw [h6, mul_one]
    _ = (((u⁻¹ : Kˣ) : K) ^ 4 * (u : K) ^ 4) * (u : K) ^ 2 := by ring
    _ = (u : K) ^ 2 := by rw [h, one_mul]

private theorem inv_pow_three_mul_of_aut_ofJ0 (u : Kˣ) (t : K)
    (hu : (u : K) ^ 3 = 1 + 2 * t) : ((u⁻¹ : Kˣ) : K) ^ 3 * (1 + 2 * t) = 1 := by
  rw [← hu, ← mul_pow, Units.inv_mul, one_pow]

private theorem map_smul_fam1728_eq_map_rescale (u : Kˣ) (hu : (u : K) ^ 4 = 1) :
    ((⟨u, 0, 0, 0⟩ : VariableChange K).map (PowerSeries.C (R := K))) • fam1728 K
      = (fam1728 K).map (PowerSeries.rescale ((u : K) ^ 2)) := by
  have h4 : (PowerSeries.C (R := K)) ((u⁻¹ : Kˣ) : K) ^ 4 = 1 := by
    rw [← map_pow, inv_pow_four_of_pow_four u hu, map_one]
  have h6 : (PowerSeries.C (R := K)) ((u⁻¹ : Kˣ) : K) ^ 6 = PowerSeries.C (R := K) ((u : K) ^ 2) := by
    rw [← map_pow, inv_pow_six_of_pow_four u hu]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · simp [variableChange_a₁, VariableChange.map, WeierstrassCurve.map, fam1728]
  · simp [variableChange_a₂, VariableChange.map, WeierstrassCurve.map, fam1728]
  · simp [variableChange_a₃, VariableChange.map, WeierstrassCurve.map, fam1728]
  · simp only [variableChange_a₄, VariableChange.map, WeierstrassCurve.map, fam1728,
      Units.coe_map_inv, MonoidHom.coe_coe, map_zero, map_one]
    linear_combination h4
  · simp only [variableChange_a₆, VariableChange.map, WeierstrassCurve.map, fam1728,
      Units.coe_map_inv, MonoidHom.coe_coe, map_zero, PowerSeries.rescale_X]
    linear_combination PowerSeries.X * h6

private theorem map_smul_fam0_eq_map_rescale (u : Kˣ) (t : K) (ht : t * (1 + t) = 0)
    (hu : (u : K) ^ 3 = 1 + 2 * t) :
    ((⟨u, 0, 0, t⟩ : VariableChange K).map (PowerSeries.C (R := K))) • fam0 K
      = (fam0 K).map (PowerSeries.rescale ((u : K) ^ 2)) := by
  have h3 : (PowerSeries.C (R := K)) ((u⁻¹ : Kˣ) : K) ^ 3
      * (1 + 2 * PowerSeries.C (R := K) t) = 1 := by
    rw [← map_pow, show (1 + 2 * PowerSeries.C (R := K) t : PowerSeries K)
        = PowerSeries.C (R := K) (1 + 2 * t) by rw [map_add, map_one, map_mul, map_ofNat],
      ← map_mul, inv_pow_three_mul_of_aut_ofJ0 u t hu, map_one]
  have h4 : (PowerSeries.C (R := K)) ((u⁻¹ : Kˣ) : K) ^ 4 = PowerSeries.C (R := K) ((u : K) ^ 2) := by
    rw [← map_pow, inv_pow_four_of_aut_ofJ0 u t ht hu]
  have ht' : PowerSeries.C (R := K) t * (1 + PowerSeries.C (R := K) t) = 0 := by
    rw [show (1 + PowerSeries.C (R := K) t : PowerSeries K) = PowerSeries.C (R := K) (1 + t) by
        rw [map_add, map_one], ← map_mul, ht, map_zero]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · simp [variableChange_a₁, VariableChange.map, WeierstrassCurve.map, fam0]
  · simp [variableChange_a₂, VariableChange.map, WeierstrassCurve.map, fam0]
  · simp only [variableChange_a₃, VariableChange.map, WeierstrassCurve.map, fam0,
      Units.coe_map_inv, MonoidHom.coe_coe, map_zero, map_one]
    linear_combination h3
  · simp only [variableChange_a₄, VariableChange.map, WeierstrassCurve.map, fam0,
      Units.coe_map_inv, MonoidHom.coe_coe, map_zero, PowerSeries.rescale_X]
    linear_combination PowerSeries.X * h4
  · simp only [variableChange_a₆, VariableChange.map, WeierstrassCurve.map, fam0,
      Units.coe_map_inv, MonoidHom.coe_coe, map_zero]
    linear_combination (-(PowerSeries.C (R := K) ((u⁻¹ : Kˣ) : K) ^ 6)) * ht'

private theorem rescale_j_fam1728 [(fam1728 K).IsElliptic] (u : Kˣ) (hu : (u : K) ^ 4 = 1) :
    PowerSeries.rescale ((u : K) ^ 2) (fam1728 K).j = (fam1728 K).j := by
  have key : ∀ (W W' : WeierstrassCurve (PowerSeries K)) [W.IsElliptic] [W'.IsElliptic],
      W = W' → W.j = W'.j := by
    rintro W W' _ _ rfl
    rfl
  rw [← WeierstrassCurve.map_j, ← key _ _ (map_smul_fam1728_eq_map_rescale u hu),
    variableChange_j]

private theorem rescale_j_fam0 [(fam0 K).IsElliptic] (u : Kˣ) (t : K) (ht : t * (1 + t) = 0)
    (hu : (u : K) ^ 3 = 1 + 2 * t) :
    PowerSeries.rescale ((u : K) ^ 2) (fam0 K).j = (fam0 K).j := by
  have key : ∀ (W W' : WeierstrassCurve (PowerSeries K)) [W.IsElliptic] [W'.IsElliptic],
      W = W' → W.j = W'.j := by
    rintro W W' _ _ rfl
    rfl
  rw [← WeierstrassCurve.map_j, ← key _ _ (map_smul_fam0_eq_map_rescale u t ht hu),
    variableChange_j]

end Deck
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

end ModularCurve.EllFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

namespace SsfrobDeck

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve HahnSeries"

variable {K : Type*} [Field K]

private theorem qTwist_algebraMap (u : Kˣ) (a : K) :
    qTwist u (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a := by
  rw [algebraMap_laurentSeries_eq_single, qTwist_single, zpow_zero, Units.val_one, one_mul]

private def qTwistAlgHom (u : Kˣ) : LaurentSeries K →ₐ[K] LaurentSeries K :=
  { qTwist u with commutes' := qTwist_algebraMap u }

@[scoped simp]
private theorem qTwistAlgHom_apply (u : Kˣ) (f : LaurentSeries K) : qTwistAlgHom u f = qTwist u f := rfl

private def qTwistAlgEquiv (u : Kˣ) : LaurentSeries K ≃ₐ[K] LaurentSeries K :=
  AlgEquiv.ofAlgHom (qTwistAlgHom u) (qTwistAlgHom u⁻¹)
    (by ext f; simp [qTwist_qTwist])
    (by ext f; simp [qTwist_qTwist])

@[scoped simp]
private theorem qTwistAlgEquiv_apply (u : Kˣ) (f : LaurentSeries K) : qTwistAlgEquiv u f = qTwist u f :=
  rfl

private theorem order_qTwist (u : Kˣ) (f : LaurentSeries K) : (qTwist u f).order = f.order := by
  by_cases hf : f = 0
  · rw [hf, map_zero]
  have hq : qTwist u f ≠ 0 := fun h => hf (qTwist_injective u (h.trans (map_zero _).symm))
  have hfc : f.coeff f.order ≠ 0 := fun h0 => hf (HahnSeries.coeff_order_eq_zero.mp h0)
  have hqc : (qTwist u f).coeff (qTwist u f).order ≠ 0 := fun h0 =>
    hq (HahnSeries.coeff_order_eq_zero.mp h0)
  apply le_antisymm
  · refine HahnSeries.order_le_of_coeff_ne_zero ?_
    rw [qTwist_coeff]
    exact mul_ne_zero (Units.ne_zero _) hfc
  · refine HahnSeries.order_le_of_coeff_ne_zero ?_
    rw [qTwist_coeff] at hqc
    exact right_ne_zero_of_mul hqc

private theorem qTwist_coe_powerSeries (u : Kˣ) (p : PowerSeries K) :
    qTwist u (p : LaurentSeries K) = ((PowerSeries.rescale (u : K) p : PowerSeries K) : LaurentSeries K) := by
  ext k
  rw [qTwist_coeff, PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs with hk
  · rw [mul_zero]
  · rw [PowerSeries.coeff_rescale, ← zpow_natCast, Int.natAbs_of_nonneg (not_lt.mp hk),
      Units.val_zpow_eq_zpow_val]

private theorem qTwist_comp_ofPowerSeries (u : Kˣ) :
    (qTwist u).comp (HahnSeries.ofPowerSeries ℤ K)
      = (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.rescale (u : K)) :=
  RingHom.ext fun p => qTwist_coe_powerSeries u p

private theorem coeff_eq_zero_of_qTwist_eq_self (u : Kˣ) {f : LaurentSeries K} (h : qTwist u f = f)
    (k : ℤ) (hk : ((u ^ k : Kˣ) : K) ≠ 1) : f.coeff k = 0 := by
  have hc := congrArg (fun g : LaurentSeries K => g.coeff k) h
  simp only [qTwist_coeff] at hc
  have h' : (((u ^ k : Kˣ) : K) - 1) * f.coeff k = 0 := by rw [sub_mul, one_mul, hc, sub_self]
  exact (mul_eq_zero.mp h').resolve_left (sub_ne_zero.mpr hk)

private theorem dvd_order_of_qTwist_eq_self (u : Kˣ) (d : ℤ) (hd : ∀ k : ℤ, ((u ^ k : Kˣ) : K) = 1 → d ∣ k)
    {f : LaurentSeries K} (hf : f ≠ 0) (h : qTwist u f = f) : d ∣ f.order := by
  by_contra hnd
  exact hf (HahnSeries.coeff_order_eq_zero.mp
    (coeff_eq_zero_of_qTwist_eq_self u h f.order fun h1 => hnd (hd _ h1)))

end SsfrobDeck
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

namespace SsfrobDeck

p2m_open "ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve AlgebraicCurve"

variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]

private theorem mem_toValuationSubring_iff_order_nonneg (w : Place K F)
    (ι : F →ₐ[K] LaurentSeries K) (γ : ℕ) (hγ : 0 < γ)
    (h : ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order) (x : F) :
    x ∈ w.toValuationSubring ↔ 0 ≤ (ι x).order := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [w.mem_iff_ord_nonneg hx, ← h x]
  constructor
  · intro h0
    exact mul_nonneg h0 (Int.natCast_nonneg γ)
  · intro h0
    by_contra hneg
    push Not at hneg
    have : w.ord x * (γ : ℤ) < 0 := mul_neg_of_neg_of_pos hneg (by exact_mod_cast hγ)
    exact absurd h0 (not_le.mpr this)

private theorem place_eq_of_ord_mul_eq_order (w w' : Place K F)
    (ι ι' : F →ₐ[K] LaurentSeries K) (γ γ' : ℕ) (hγ : 0 < γ) (hγ' : 0 < γ')
    (h : ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order)
    (h' : ∀ x : F, w'.ord x * (γ' : ℤ) = (ι' x).order)
    (hιι' : ∀ x : F, (ι' x).order = (ι x).order) : w' = w := by
  refine Place.ext (ValuationSubring.ext _ _ fun x => ?_)
  rw [mem_toValuationSubring_iff_order_nonneg w' ι' γ' hγ' h' x,
    mem_toValuationSubring_iff_order_nonneg w ι γ hγ h x, hιι' x]

private theorem index_eq_of_ord_mul_eq_order (w w' : Place K F)
    (ι ι' : F →ₐ[K] LaurentSeries K) (γ γ' : ℕ) (hγ : 0 < γ) (hγ' : 0 < γ')
    (h : ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order)
    (h' : ∀ x : F, w'.ord x * (γ' : ℤ) = (ι' x).order)
    (hιι' : ∀ x : F, (ι' x).order = (ι x).order) : γ' = γ := by
  have hw : w' = w := place_eq_of_ord_mul_eq_order w w' ι ι' γ γ' hγ hγ' h h' hιι'
  subst hw
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w'.toValuationSubring
  have h1 : w'.ord (π : F) = 1 := w'.ord_coe_irreducible hπ
  have e1 := h (π : F)
  have e2 := h' (π : F)
  rw [h1, one_mul] at e1 e2
  rw [hιι', ← e1] at e2
  exact_mod_cast e2

private theorem place_eq_of_eq_qTwist_comp (w w' : Place K F)
    (ι ι' : F →ₐ[K] LaurentSeries K) (γ γ' : ℕ) (hγ : 0 < γ) (hγ' : 0 < γ')
    (h : ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order)
    (h' : ∀ x : F, w'.ord x * (γ' : ℤ) = (ι' x).order)
    (u : Kˣ) (hιι' : ∀ x : F, ι' x = qTwist u (ι x)) : w' = w ∧ γ' = γ := by
  have ho : ∀ x : F, (ι' x).order = (ι x).order := fun x => by rw [hιι', order_qTwist]
  exact ⟨place_eq_of_ord_mul_eq_order w w' ι ι' γ γ' hγ hγ' h h' ho,
    index_eq_of_ord_mul_eq_order w w' ι ι' γ γ' hγ hγ' h h' ho⟩

private theorem dvd_index_of_qTwist_comp_eq (w : Place K F) (ι : F →ₐ[K] LaurentSeries K) (γ : ℕ)
    (h : ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order)
    (u : Kˣ) (hfix : ∀ x : F, qTwist u (ι x) = ι x)
    (d : ℤ) (hd : ∀ k : ℤ, ((u ^ k : Kˣ) : K) = 1 → d ∣ k) : d ∣ (γ : ℤ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
  have h1 : w.ord (π : F) = 1 := w.ord_coe_irreducible hπ
  have hπ0 : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hι0 : ι (π : F) ≠ 0 := by
    simpa using hπ0
  have e1 := h (π : F)
  rw [h1, one_mul] at e1
  rw [e1]
  exact dvd_order_of_qTwist_eq_self u d hd hι0 (hfix _)

private theorem ord_mul_index_eq (w : Place K F) (ι : F →ₐ[K] LaurentSeries K) (γ : ℕ)
    (h : ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order) (x₁ : F) (x₀ : LaurentSeries K)
    (hx : ι x₁ = x₀) : w.ord x₁ * (γ : ℤ) = x₀.order := by
  rw [h, hx]

private theorem ord_eq_one_or_eq_of_prime (w : Place K F) (ι : F →ₐ[K] LaurentSeries K) (γ : ℕ)
    (h : ∀ x : F, w.ord x * (γ : ℤ) = (ι x).order) (x₁ : F) (x₀ : LaurentSeries K)
    (hx : ι x₁ = x₀) (m : ℕ) (hm : m.Prime) (hx₀ : x₀.order = m) (hpos : 0 ≤ w.ord x₁) :
    w.ord x₁ = 1 ∨ w.ord x₁ = m := by
  have e := ord_mul_index_eq w ι γ h x₁ x₀ hx
  rw [hx₀] at e
  lift w.ord x₁ to ℕ using hpos with n hn
  have hdvd : n ∣ m := ⟨γ, by exact_mod_cast e.symm⟩
  rcases hm.eq_one_or_self_of_dvd n hdvd with h1 | h2
  · exact Or.inl (by exact_mod_cast h1)
  · exact Or.inr (by exact_mod_cast h2)

end SsfrobDeck
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end Brick_ELL6_B
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

section Brick_ELL6_C

set_option autoImplicit false

namespace SsfrobCount

open Finset

section Fibre

variable {E T : Type*} [Fintype E] [DecidableEq T]

private theorem card_filter_eq_of_sum_eq_card (pl : E → T) (S : Finset T) (hS : ∀ i, pl i ∈ S)
    (e : T → ℕ) (hsum : ∑ w ∈ S, e w = Fintype.card E)
    (hle : ∀ w ∈ S, (Finset.univ.filter fun i => pl i = w).card ≤ e w) :
    ∀ w ∈ S, (Finset.univ.filter fun i => pl i = w).card = e w := by
  have htot : (Finset.univ : Finset E).card
      = ∑ w ∈ S, (Finset.univ.filter fun i => pl i = w).card :=
    Finset.card_eq_sum_card_fiberwise fun i _ => Finset.mem_coe.mpr (hS i)
  rw [Finset.card_univ] at htot
  exact (Finset.sum_eq_sum_iff_of_le hle).mp (htot.symm.trans hsum.symm)

private theorem exists_apply_eq_of_sum_eq_card (pl : E → T) (S : Finset T) (hS : ∀ i, pl i ∈ S)
    (e : T → ℕ) (hsum : ∑ w ∈ S, e w = Fintype.card E)
    (hle : ∀ w ∈ S, (Finset.univ.filter fun i => pl i = w).card ≤ e w)
    (hpos : ∀ w ∈ S, 0 < e w) :
    ∀ w ∈ S, ∃ i, pl i = w := by
  intro w hw
  have hne : (Finset.univ.filter fun i => pl i = w).Nonempty := by
    rw [← Finset.card_pos, card_filter_eq_of_sum_eq_card pl S hS e hsum hle w hw]
    exact hpos w hw
  obtain ⟨i, hi⟩ := hne
  exact ⟨i, (Finset.mem_filter.mp hi).2⟩

end Fibre
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

section Orbit

variable {Γ E T : Type*} [Group Γ] [MulAction Γ E] [Fintype E] [DecidableEq T]

omit [Fintype E] [DecidableEq T] in

private theorem orbit_subset_setOf_apply_eq (pl : E → T) (hinv : ∀ (g : Γ) (i : E), pl (g • i) = pl i)
    (i : E) : MulAction.orbit Γ i ⊆ {i' | pl i' = pl i} := by
  rintro _ ⟨g, rfl⟩
  exact hinv g i

omit [DecidableEq T] in

private theorem le_ncard_orbit_of_stabilizer_le (pl : E → T) (e : T → ℕ) (K₀ : Subgroup Γ) (i : E)
    (hdich : e (pl i) = 1 ∨ e (pl i) = K₀.index)
    (hfix : e (pl i) ≠ 1 → MulAction.stabilizer Γ i ≤ K₀) :
    e (pl i) ≤ (MulAction.orbit Γ i).ncard := by
  have hpos : 0 < (MulAction.orbit Γ i).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨i, MulAction.mem_orbit_self i⟩
  by_cases h1 : e (pl i) = 1
  · rw [h1]
    exact hpos
  · have hidx : e (pl i) = K₀.index := hdich.resolve_left h1
    rw [hidx, ← MulAction.index_stabilizer]
    rw [← MulAction.index_stabilizer] at hpos
    exact Nat.le_of_dvd hpos (Subgroup.index_dvd_of_le (hfix h1))

variable (pl : E → T) (hinv : ∀ (g : Γ) (i : E), pl (g • i) = pl i)
  (S : Finset T) (hS : ∀ i, pl i ∈ S)
  (e : T → ℕ) (hsum : ∑ w ∈ S, e w = Fintype.card E)
  (hle : ∀ w ∈ S, (Finset.univ.filter fun i => pl i = w).card ≤ e w)
  (horb : ∀ i, e (pl i) ≤ (MulAction.orbit Γ i).ncard)

include hinv hS hsum hle horb

private theorem orbit_eq_setOf_apply_eq (i : E) : MulAction.orbit Γ i = {i' | pl i' = pl i} := by
  classical
  have hfib : ({i' | pl i' = pl i} : Set E) = ↑(Finset.univ.filter fun i' => pl i' = pl i) := by
    ext i'
    simp
  refine Set.eq_of_subset_of_ncard_le (orbit_subset_setOf_apply_eq pl hinv i) ?_ (Set.toFinite _)
  rw [hfib, Set.ncard_coe_finset, card_filter_eq_of_sum_eq_card pl S hS e hsum hle _ (hS i)]
  exact horb i

private theorem ncard_orbit_eq (i : E) : (MulAction.orbit Γ i).ncard = e (pl i) := by
  classical
  rw [orbit_eq_setOf_apply_eq pl hinv S hS e hsum hle horb i]
  have hfib : ({i' | pl i' = pl i} : Set E) = ↑(Finset.univ.filter fun i' => pl i' = pl i) := by
    ext i'
    simp
  rw [hfib, Set.ncard_coe_finset, card_filter_eq_of_sum_eq_card pl S hS e hsum hle _ (hS i)]

private theorem exists_smul_eq_of_apply_eq {i i' : E} (h : pl i = pl i') : ∃ g : Γ, g • i = i' := by
  have hmem : i' ∈ MulAction.orbit Γ i := by
    rw [orbit_eq_setOf_apply_eq pl hinv S hS e hsum hle horb i]
    exact h.symm
  exact MulAction.mem_orbit_iff.mp hmem

omit hsum hle horb in

private def orbitLift : MulAction.orbitRel.Quotient Γ E → ↥S :=
  Quotient.lift (fun i => (⟨pl i, hS i⟩ : ↥S)) fun a b hab => by
    have hab' : a ∈ MulAction.orbit Γ b := hab
    obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hab'
    exact Subtype.ext (hinv g b)

omit [Fintype E] [DecidableEq T] hsum hle horb in
private theorem orbitLift_mk (i : E) :
    orbitLift pl hinv S hS (Quotient.mk (MulAction.orbitRel Γ E) i) = ⟨pl i, hS i⟩ := rfl

private theorem orbitLift_bijective (hpos : ∀ w ∈ S, 0 < e w) :
    Function.Bijective (orbitLift pl hinv S hS) := by
  constructor
  · intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b hab
    have hab' : pl a = pl b := congrArg Subtype.val hab
    obtain ⟨g, hg⟩ := exists_smul_eq_of_apply_eq pl hinv S hS e hsum hle horb hab'.symm
    exact Quotient.sound (MulAction.mem_orbit_iff.mpr ⟨g, hg⟩)
  · intro w
    obtain ⟨i, hi⟩ := exists_apply_eq_of_sum_eq_card pl S hS e hsum hle hpos w.1 w.2
    exact ⟨Quotient.mk _ i, Subtype.ext hi⟩

end Orbit
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end SsfrobCount
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end Brick_ELL6_C
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

section Brick_ELL7_ORD

set_option autoImplicit false

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
namespace EllFam
p2m_open "ModularCurve"

section Orders

variable {K : Type*} [Field K]

private theorem two_ne_zero_of_six_ne_zero (h6 : (6 : K) ≠ 0) : (2 : K) ≠ 0 := by
  intro h2
  apply h6
  rw [show (6 : K) = 2 * 3 by norm_num, h2, zero_mul]

private theorem three_ne_zero_of_six_ne_zero (h6 : (6 : K) ≠ 0) : (3 : K) ≠ 0 := by
  intro h3
  apply h6
  rw [show (6 : K) = 2 * 3 by norm_num, h3, mul_zero]

private theorem algebraMap_laurentSeries_ne_zero {p : PowerSeries K} (hp : p ≠ 0) :
    algebraMap (PowerSeries K) (LaurentSeries K) p ≠ 0 := by
  rw [LaurentSeries.coe_algebraMap]
  exact fun h => hp (HahnSeries.ofPowerSeries_injective (h.trans (map_zero _).symm))

private theorem order_algebraMap_laurentSeries_eq (n : ℕ) {p : PowerSeries K}
    (h0 : ∀ k, k < n → PowerSeries.coeff k p = 0)
    (hn : PowerSeries.coeff n p ≠ 0) :
    (algebraMap (PowerSeries K) (LaurentSeries K) p).order = n := by
  rw [LaurentSeries.coe_algebraMap]
  have hcn : (HahnSeries.ofPowerSeries ℤ K p).coeff (n : ℤ) = PowerSeries.coeff n p := by
    have hc : (HahnSeries.ofPowerSeries ℤ K p).coeff (n : ℤ)
        = if (n : ℤ) < 0 then 0 else PowerSeries.coeff (n : ℤ).natAbs p :=
      PowerSeries.coeff_coe (f := p) (n : ℤ)
    rw [hc, if_neg (not_lt.mpr (Int.natCast_nonneg n)), Int.natAbs_natCast]
  have hne : HahnSeries.ofPowerSeries ℤ K p ≠ 0 := by
    intro h
    apply hn
    rw [← hcn, h]
    simp
  apply le_antisymm
  · exact HahnSeries.order_le_of_coeff_ne_zero (by rw [hcn]; exact hn)
  · rw [HahnSeries.le_order_iff_forall hne]
    intro j hj
    have hc : (HahnSeries.ofPowerSeries ℤ K p).coeff j
        = if j < 0 then 0 else PowerSeries.coeff j.natAbs p :=
      PowerSeries.coeff_coe (f := p) j
    rw [hc]
    split_ifs with hj0
    · rfl
    · refine h0 j.natAbs ?_
      have h1 : (j.natAbs : ℤ) < (n : ℤ) := by
        rw [Int.natAbs_of_nonneg (not_lt.mp hj0)]
        exact hj
      exact_mod_cast h1

private theorem order_algebraMap_laurentSeries_eq_zero {p : PowerSeries K}
    (hp : PowerSeries.constantCoeff (R := K) p ≠ 0) :
    (algebraMap (PowerSeries K) (LaurentSeries K) p).order = 0 := by
  have h := order_algebraMap_laurentSeries_eq 0 (p := p)
    (fun k hk => absurd hk (Nat.not_lt_zero k))
    (by rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]; exact hp)
  exact_mod_cast h

private theorem order_algebraMap_laurentSeries_base (x : K) :
    (algebraMap K (LaurentSeries K) x).order = 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_zero, HahnSeries.order_zero]
  · rw [ModularCurve.algebraMap_laurentSeries_eq_single, HahnSeries.order_single hx]

private theorem j_mul_Δ {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsElliptic] :
    W.j * W.Δ = W.c₄ ^ 3 := by
  have hj : W.j = ↑W.Δ'⁻¹ * W.c₄ ^ 3 := rfl
  rw [hj, ← W.coe_Δ']
  calc (↑W.Δ'⁻¹ * W.c₄ ^ 3) * ↑W.Δ' = W.c₄ ^ 3 * (↑W.Δ'⁻¹ * ↑W.Δ') := by ring
    _ = W.c₄ ^ 3 := by rw [Units.inv_mul, mul_one]

private theorem Δ_fam1728 : (fam1728 K).Δ = -64 - 432 * PowerSeries.X ^ 2 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, fam1728]
  ring

private theorem constantCoeff_Δ_fam1728 :
    PowerSeries.constantCoeff (R := K) (fam1728 K).Δ = -64 := by
  rw [Δ_fam1728]
  simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat, PowerSeries.constantCoeff_X]
  norm_num

private theorem Δ_fam0 : (fam0 K).Δ = -27 - 64 * PowerSeries.X ^ 3 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, fam0]
  ring

private theorem constantCoeff_Δ_fam0 :
    PowerSeries.constantCoeff (R := K) (fam0 K).Δ = -27 := by
  rw [Δ_fam0]
  simp only [map_sub, map_mul, map_pow, map_neg, map_ofNat, PowerSeries.constantCoeff_X]
  norm_num

private theorem c₆_sq_fam1728 :
    (fam1728 K).c₆ ^ 2 = PowerSeries.C (R := K) 746496 * PowerSeries.X ^ 2 := by
  simp only [WeierstrassCurve.c₆, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, fam1728, map_ofNat]
  ring

private theorem c₄_cube_fam0 :
    (fam0 K).c₄ ^ 3 = PowerSeries.C (R := K) (-110592) * PowerSeries.X ^ 3 := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, fam0,
    map_neg, map_ofNat]
  ring

private theorem constantCoeff_Δ_fam1728_ne_zero (h6 : (6 : K) ≠ 0) :
    PowerSeries.constantCoeff (R := K) (fam1728 K).Δ ≠ 0 := by
  rw [constantCoeff_Δ_fam1728]
  refine neg_ne_zero.mpr ?_
  rw [show (64 : K) = 2 ^ 6 by norm_num]
  exact pow_ne_zero 6 (two_ne_zero_of_six_ne_zero h6)

private theorem constantCoeff_Δ_fam0_ne_zero (h6 : (6 : K) ≠ 0) :
    PowerSeries.constantCoeff (R := K) (fam0 K).Δ ≠ 0 := by
  rw [constantCoeff_Δ_fam0]
  refine neg_ne_zero.mpr ?_
  rw [show (27 : K) = 3 ^ 3 by norm_num]
  exact pow_ne_zero 3 (three_ne_zero_of_six_ne_zero h6)

private theorem num746496_ne_zero (h6 : (6 : K) ≠ 0) : (746496 : K) ≠ 0 := by
  rw [show (746496 : K) = 2 ^ 10 * 3 ^ 6 by norm_num]
  exact mul_ne_zero (pow_ne_zero 10 (two_ne_zero_of_six_ne_zero h6))
    (pow_ne_zero 6 (three_ne_zero_of_six_ne_zero h6))

private theorem neg_num110592_ne_zero (h6 : (6 : K) ≠ 0) : (-110592 : K) ≠ 0 := by
  refine neg_ne_zero.mpr ?_
  rw [show (110592 : K) = 2 ^ 12 * 3 ^ 3 by norm_num]
  exact mul_ne_zero (pow_ne_zero 12 (two_ne_zero_of_six_ne_zero h6))
    (pow_ne_zero 3 (three_ne_zero_of_six_ne_zero h6))

private theorem isElliptic_fam1728 (h6 : (6 : K) ≠ 0) : (fam1728 K).IsElliptic :=
  ⟨PowerSeries.isUnit_iff_constantCoeff.mpr
    (isUnit_iff_ne_zero.mpr (constantCoeff_Δ_fam1728_ne_zero h6))⟩

private theorem isElliptic_fam0 (h6 : (6 : K) ≠ 0) : (fam0 K).IsElliptic :=
  ⟨PowerSeries.isUnit_iff_constantCoeff.mpr
    (isUnit_iff_ne_zero.mpr (constantCoeff_Δ_fam0_ne_zero h6))⟩

private theorem key_fam1728 [(fam1728 K).IsElliptic] :
    ((fam1728 K).j - PowerSeries.C (R := K) 1728) * (fam1728 K).Δ
      = PowerSeries.C (R := K) 746496 * PowerSeries.X ^ 2 := by
  have h1 := j_mul_Δ (fam1728 K)
  have h2 := (fam1728 K).c_relation
  have h3 := c₆_sq_fam1728 (K := K)
  rw [show PowerSeries.C (R := K) 1728 = (1728 : PowerSeries K) from map_ofNat _ _]
  linear_combination h1 - h2 + h3

private theorem key_fam0 [(fam0 K).IsElliptic] :
    ((fam0 K).j - PowerSeries.C (R := K) 0) * (fam0 K).Δ
      = PowerSeries.C (R := K) (-110592) * PowerSeries.X ^ 3 := by
  rw [map_zero, sub_zero, j_mul_Δ]
  exact c₄_cube_fam0

private theorem order_j_genFibre_sub_of_mul_eq (W : WeierstrassCurve (PowerSeries K)) [W.IsElliptic]
    {a c : K} {n : ℕ} (hc : c ≠ 0)
    (hΔ0 : PowerSeries.constantCoeff (R := K) W.Δ ≠ 0)
    (key : (W.j - PowerSeries.C (R := K) a) * W.Δ
      = PowerSeries.C (R := K) c * PowerSeries.X ^ n) :
    ((genFibre W).j - algebraMap K (LaurentSeries K) a).order = n := by
  have hAkey : ((genFibre W).j - algebraMap K (LaurentSeries K) a)
      * algebraMap (PowerSeries K) (LaurentSeries K) W.Δ
      = algebraMap (PowerSeries K) (LaurentSeries K)
          (PowerSeries.C (R := K) c * PowerSeries.X ^ n) := by
    rw [j_genFibre, algebraMap_laurentSeries_factor, ← map_sub, ← map_mul, key]
  have hRHSord : (algebraMap (PowerSeries K) (LaurentSeries K)
      (PowerSeries.C (R := K) c * PowerSeries.X ^ n)).order = n :=
    order_algebraMap_laurentSeries_eq n
      (fun k hk => by
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_neg (Nat.ne_of_lt hk),
          mul_zero])
      (by
        rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one]
        exact hc)
  have hPne : PowerSeries.C (R := K) c * PowerSeries.X ^ n ≠ 0 := by
    intro h
    apply hc
    have hcoeff : PowerSeries.coeff n (PowerSeries.C (R := K) c * PowerSeries.X ^ n)
        = PowerSeries.coeff n (0 : PowerSeries K) := by rw [h]
    rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, if_pos rfl, mul_one,
      map_zero] at hcoeff
    exact hcoeff
  have hRHSne := algebraMap_laurentSeries_ne_zero hPne
  have hΔne : algebraMap (PowerSeries K) (LaurentSeries K) W.Δ ≠ 0 :=
    algebraMap_laurentSeries_ne_zero fun h => hΔ0 (by rw [h, map_zero])
  have hΔord : (algebraMap (PowerSeries K) (LaurentSeries K) W.Δ).order = 0 :=
    order_algebraMap_laurentSeries_eq_zero hΔ0
  have hfne : (genFibre W).j - algebraMap K (LaurentSeries K) a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hAkey
    exact hRHSne hAkey.symm
  have hmul := HahnSeries.order_mul hfne hΔne
  rw [hAkey, hRHSord, hΔord, add_zero] at hmul
  exact hmul.symm

private theorem order_j_genFibre_fam1728_sub (h6 : (6 : K) ≠ 0) [(fam1728 K).IsElliptic] :
    ((genFibre (fam1728 K)).j - algebraMap K (LaurentSeries K) 1728).order = 2 := by
  have h := order_j_genFibre_sub_of_mul_eq (fam1728 K) (num746496_ne_zero h6)
    (constantCoeff_Δ_fam1728_ne_zero h6) key_fam1728
  exact_mod_cast h

private theorem order_j_genFibre_fam0 (h6 : (6 : K) ≠ 0) [(fam0 K).IsElliptic] :
    ((genFibre (fam0 K)).j).order = 3 := by
  have h := order_j_genFibre_sub_of_mul_eq (fam0 K) (neg_num110592_ne_zero h6)
    (constantCoeff_Δ_fam0_ne_zero h6) key_fam0
  rw [map_zero, sub_zero] at h
  exact_mod_cast h

private theorem order_j_genFibre_fam0_sub (h6 : (6 : K) ≠ 0) [(fam0 K).IsElliptic] :
    ((genFibre (fam0 K)).j - algebraMap K (LaurentSeries K) 0).order = 3 := by
  rw [map_zero, sub_zero]
  exact order_j_genFibre_fam0 h6

private theorem j_fam1728_notMem_range_C (h6 : (6 : K) ≠ 0) [(fam1728 K).IsElliptic] :
    (fam1728 K).j ∉ Set.range (PowerSeries.C (R := K)) := by
  rintro ⟨d, hd⟩
  have h2 := order_j_genFibre_fam1728_sub h6
  rw [j_genFibre, ← hd, ← algebraMap_laurentSeries_factor, ← map_sub,
    order_algebraMap_laurentSeries_base] at h2
  exact absurd h2 (by norm_num)

private theorem j_fam0_notMem_range_C (h6 : (6 : K) ≠ 0) [(fam0 K).IsElliptic] :
    (fam0 K).j ∉ Set.range (PowerSeries.C (R := K)) := by
  rintro ⟨d, hd⟩
  have h3 := order_j_genFibre_fam0 h6
  rw [j_genFibre, ← hd, ← algebraMap_laurentSeries_factor,
    order_algebraMap_laurentSeries_base] at h3
  exact absurd h3 (by norm_num)

end Orders
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end ModularCurve.EllFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end Brick_ELL7_ORD
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

section Brick_DECK_ELL

set_option autoImplicit false

noncomputable section

open WeierstrassCurve

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
namespace EllFam
p2m_open "ModularCurve"

end ModularCurve.EllFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

namespace ModularCurve
p2m_export "ModularCurve" "sum_ord_jGeomGen_sub_eq_dedekindPsi jGeomGen jNGeomGen dedekindPsi ModularPolynomialData jqModC jqNModC jqNModC_one modularFunctionFieldC jqModC_mem jqNModC_mem fibrePoly transcendental_jqModC relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi algebraMap_laurentSeries_eq_single qTwist qTwist_coeff qTwist_single qTwist_one_apply qTwist_qTwist qTwist_injective exists_modularPolynomialData_evalSymm isSeparable_jqNModC_of_modularPolynomialData ModularPolynomialData.eval_jqNModC_mul_eq_zero ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j modularFunctionFieldC_algHom_ext isSeparable_jqNModC_of_good"
namespace EllFam
p2m_open "ModularCurve"

section DeckEll

variable {K : Type*} [Field K]

private theorem qTwist_j_genFibre_fam1728 [IsAlgClosed K] [(fam1728 K).IsElliptic]
    (u : Kˣ) (hu : u ∈ rootsOfUnity 2 K) :
    ModularCurve.qTwist u ((genFibre (fam1728 K)).j) = (genFibre (fam1728 K)).j := by
  have hu2 : (u : K) ^ 2 = 1 := (mem_rootsOfUnity' 2 u).mp hu
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq (u : K) (n := 2) (by norm_num)
  have hv0 : v ≠ 0 := by
    intro h
    exact u.ne_zero (by rw [← hv, h, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hv4 : ((Units.mk0 v hv0 : Kˣ) : K) ^ 4 = 1 := by
    show v ^ 4 = 1
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, hv, hu2]
  have hres := rescale_j_fam1728 (K := K) (Units.mk0 v hv0) hv4
  rw [show ((Units.mk0 v hv0 : Kˣ) : K) ^ 2 = (u : K) from hv] at hres
  rw [j_genFibre, LaurentSeries.coe_algebraMap]
  exact (SsfrobDeck.qTwist_coe_powerSeries u ((fam1728 K).j)).trans
    (congrArg (⇑(HahnSeries.ofPowerSeries ℤ K)) hres)

private theorem qTwist_j_genFibre_fam0 [(fam0 K).IsElliptic]
    (u : Kˣ) (hu : u ∈ rootsOfUnity 3 K) :
    ModularCurve.qTwist u ((genFibre (fam0 K)).j) = (genFibre (fam0 K)).j := by
  have hu3 : (u : K) ^ 3 = 1 := (mem_rootsOfUnity' 3 u).mp hu
  have ht : (0 : K) * (1 + 0) = 0 := by ring
  have hv3 : ((u ^ 2 : Kˣ) : K) ^ 3 = 1 + 2 * 0 := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, show (2 * 3 : ℕ) = 3 * 2 by norm_num, pow_mul,
      hu3, one_pow]
    ring
  have hres := rescale_j_fam0 (K := K) (u ^ 2) 0 ht hv3
  have hsq : ((u ^ 2 : Kˣ) : K) ^ 2 = (u : K) := by
    rw [Units.val_pow_eq_pow_val, ← pow_mul, show (2 * 2 : ℕ) = 3 + 1 by norm_num, pow_add,
      hu3, one_mul, pow_one]
  rw [hsq] at hres
  rw [j_genFibre, LaurentSeries.coe_algebraMap]
  exact (SsfrobDeck.qTwist_coe_powerSeries u ((fam0 K).j)).trans
    (congrArg (⇑(HahnSeries.ofPowerSeries ℤ K)) hres)

private theorem natCard_rootsOfUnity_two [IsAlgClosed K] (h2 : (2 : K) ≠ 0) :
    Nat.card (rootsOfUnity 2 K) = 2 := by
  haveI : NeZero ((2 : ℕ) : K) := ⟨by rw [Nat.cast_ofNat]; exact h2⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K 2

private theorem natCard_rootsOfUnity_three [IsAlgClosed K] (h3 : (3 : K) ≠ 0) :
    Nat.card (rootsOfUnity 3 K) = 3 := by
  haveI : NeZero ((3 : ℕ) : K) := ⟨by rw [Nat.cast_ofNat]; exact h3⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K 3

end DeckEll
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end ModularCurve.EllFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end Brick_DECK_ELL
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

section Brick_FAM_generic

set_option autoImplicit false

noncomputable section

open WeierstrassCurve

namespace SsfrobFam

variable {K : Type*} [Field K]

private def famNe (K : Type*) [Field K] (a : K) : WeierstrassCurve (PowerSeries K) :=
  ofJNe0Or1728 (PowerSeries.C (R := K) a + PowerSeries.X)

private theorem factUnit {a : K} (ha : a ≠ 0) :
    Fact (IsUnit (PowerSeries.C (R := K) a + PowerSeries.X)) := by
  refine ⟨PowerSeries.isUnit_iff_constantCoeff.mpr ?_⟩
  have h : PowerSeries.constantCoeff (R := K) (PowerSeries.C (R := K) a + PowerSeries.X) = a := by
    simp
  rw [h]
  exact isUnit_iff_ne_zero.mpr ha

private theorem factUnit1728 {a : K} (ha' : a ≠ 1728) :
    Fact (IsUnit (PowerSeries.C (R := K) a + PowerSeries.X - 1728)) := by
  refine ⟨PowerSeries.isUnit_iff_constantCoeff.mpr ?_⟩
  have h : PowerSeries.constantCoeff (R := K)
      (PowerSeries.C (R := K) a + PowerSeries.X - 1728) = a - 1728 := by
    simp [map_ofNat]
  rw [h]
  exact isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr ha')

private theorem isElliptic_famNe (a : K) (ha : a ≠ 0) (ha' : a ≠ 1728) : (famNe K a).IsElliptic := by
  haveI := factUnit ha
  haveI := factUnit1728 ha'
  exact inferInstanceAs (ofJNe0Or1728 (PowerSeries.C (R := K) a + PowerSeries.X)).IsElliptic

private theorem j_famNe (a : K) (ha : a ≠ 0) (ha' : a ≠ 1728) :
    haveI := isElliptic_famNe a ha ha'
    (famNe K a).j = PowerSeries.C (R := K) a + PowerSeries.X := by
  haveI := factUnit ha
  haveI := factUnit1728 ha'
  haveI := isElliptic_famNe a ha ha'
  show (ofJNe0Or1728 (PowerSeries.C (R := K) a + PowerSeries.X)).j = _
  exact ofJNe0Or1728_j _

private theorem j_map_constantCoeff (a : K) (ha : a ≠ 0) (ha' : a ≠ 1728) :
    haveI := isElliptic_famNe a ha ha'
    ((famNe K a).map (PowerSeries.constantCoeff (R := K))).j = a := by
  haveI := isElliptic_famNe a ha ha'
  rw [WeierstrassCurve.map_j, j_famNe a ha ha']
  simp

private theorem order_j_sub_algebraMap (a : K) (ha : a ≠ 0) (ha' : a ≠ 1728) :
    haveI := isElliptic_famNe a ha ha'
    (((famNe K a).map (algebraMap (PowerSeries K) (LaurentSeries K))).j
      - algebraMap K (LaurentSeries K) a).order = 1 := by
  haveI := isElliptic_famNe a ha ha'
  rw [WeierstrassCurve.map_j, j_famNe a ha ha']
  have h1 : (algebraMap (PowerSeries K) (LaurentSeries K))
      (PowerSeries.C (R := K) a + PowerSeries.X)
      = algebraMap K (LaurentSeries K) a + HahnSeries.single (1 : ℤ) (1 : K) := by
    rw [map_add]
    congr 1
    all_goals
      first
      | rfl
      | (rw [LaurentSeries.coe_algebraMap]; exact HahnSeries.ofPowerSeries_X)
  rw [h1, add_sub_cancel_left]
  exact HahnSeries.order_single one_ne_zero

end SsfrobFam
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

end Brick_FAM_generic
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck"

section Brick_ASSEMBLY_SRC_v5

set_option autoImplicit false

noncomputable section

namespace SsfrobPsi

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam"

section Core

variable {K : Type*} [Field K]

private def phiAt {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (x₀ : LaurentSeries K) :
    Polynomial (LaurentSeries K) :=
  data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)

private theorem phiAt_ne_zero {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (x₀ : LaurentSeries K) :
    phiAt data x₀ ≠ 0 :=
  (data.monic.map _).ne_zero

open scoped Classical in

private def rootFinset {N : ℕ} [NeZero N] (data : ModularPolynomialData N) (x₀ : LaurentSeries K) :
    Finset (LaurentSeries K) :=
  (phiAt data x₀).roots.toFinset

open scoped Classical in
private theorem mem_rootFinset_iff {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    (x₀ y : LaurentSeries K) : y ∈ rootFinset data x₀ ↔ (phiAt data x₀).IsRoot y := by
  rw [rootFinset, Multiset.mem_toFinset, Polynomial.mem_roots (phiAt_ne_zero data x₀)]

private theorem isRoot_phiAt_qTwist {N : ℕ} [NeZero N] (data : ModularPolynomialData N)
    {x₀ : LaurentSeries K} (u : Kˣ) (hu : qTwist u x₀ = x₀) {y : LaurentSeries K}
    (hy : (phiAt data x₀).IsRoot y) : (phiAt data x₀).IsRoot (qTwist u y) := by
  have hcomp : (qTwist u).comp (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)
      = Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀ := by
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, hu]
  rw [Polynomial.IsRoot.def, phiAt, Polynomial.eval_map] at hy ⊢
  have h2 := Polynomial.hom_eval₂ (p := data.Φ)
    (f := Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀) (g := qTwist u) y
  rw [hcomp, hy, map_zero] at h2
  exact h2.symm

private structure Deck (x₀ : LaurentSeries K) where

  Γ : Subgroup Kˣ

  fix : ∀ u ∈ Γ, qTwist u x₀ = x₀

private def Deck.trivial (x₀ : LaurentSeries K) : Deck x₀ :=
  ⟨⊥, fun u hu => by rw [Subgroup.mem_bot.mp hu, qTwist_one_apply]⟩

private def Deck.ofSubgroup {x₀ : LaurentSeries K} (Γ : Subgroup Kˣ) (hΓ : ∀ u ∈ Γ, qTwist u x₀ = x₀) :
    Deck x₀ :=
  ⟨Γ, hΓ⟩

private theorem Deck.ofSubgroup_Γ {x₀ : LaurentSeries K} (Γ : Subgroup Kˣ)
    (hΓ : ∀ u ∈ Γ, qTwist u x₀ = x₀) : (Deck.ofSubgroup Γ hΓ).Γ = Γ :=
  rfl

variable {N : ℕ} [NeZero N]

private def Roots (data : ModularPolynomialData N) (x₀ : LaurentSeries K) : Type _ :=
  {y : LaurentSeries K // y ∈ rootFinset data x₀}

private scoped instance instFintypeRoots (data : ModularPolynomialData N) (x₀ : LaurentSeries K) :
    Fintype (Roots data x₀) :=
  inferInstanceAs (Fintype {y : LaurentSeries K // y ∈ rootFinset data x₀})

private theorem card_roots (data : ModularPolynomialData N) (x₀ : LaurentSeries K) :
    Fintype.card (Roots data x₀) = (rootFinset data x₀).card :=
  Fintype.card_coe _

private theorem isRoot_val {data : ModularPolynomialData N} {x₀ : LaurentSeries K} (y : Roots data x₀) :
    (phiAt data x₀).IsRoot y.1 :=
  (mem_rootFinset_iff data x₀ _).mp y.2

private scoped instance Deck.instMulActionRoots {x₀ : LaurentSeries K} (D : Deck x₀)
    (data : ModularPolynomialData N) : MulAction ↥D.Γ (Roots data x₀) where
  smul g y := ⟨qTwist (g : Kˣ) y.1, (mem_rootFinset_iff data x₀ _).mpr
    (isRoot_phiAt_qTwist data (g : Kˣ) (D.fix _ g.2) (isRoot_val y))⟩
  one_smul y := Subtype.ext (show qTwist ((1 : ↥D.Γ) : Kˣ) y.1 = y.1 by
    rw [Subgroup.coe_one, qTwist_one_apply])
  mul_smul g h y := Subtype.ext (show qTwist ((g * h : ↥D.Γ) : Kˣ) y.1
      = qTwist (g : Kˣ) (qTwist (h : Kˣ) y.1) by
    rw [Subgroup.coe_mul, qTwist_qTwist])

p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck"
private theorem Deck.smul_val {x₀ : LaurentSeries K} {D : Deck x₀} {data : ModularPolynomialData N}
    (g : ↥D.Γ) (y : Roots data x₀) : (g • y).1 = qTwist (g : Kˣ) y.1 :=
  rfl

private theorem transcendental_of_order_sub_pos [IsAlgClosed K] {x₀ : LaurentSeries K} {a : K}
    (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) : Transcendental K x₀ := by
  refine transcendental_of_notMem_range_of_isAlgClosed ?_
  rintro ⟨c, hc⟩
  have h : x₀ - algebraMap K (LaurentSeries K) a = algebraMap K (LaurentSeries K) (c - a) := by
    rw [map_sub, hc]
  rw [h] at hord
  rcases eq_or_ne (c - a) 0 with h0 | h0
  · rw [h0, map_zero, HahnSeries.order_zero] at hord
    exact lt_irrefl _ hord
  · rw [algebraMap_laurentSeries_eq_single, HahnSeries.order_single h0] at hord
    exact lt_irrefl _ hord

private theorem j_specialFibre_eq_of_order_pos (W : WeierstrassCurve (PowerSeries K)) [W.IsElliptic]
    {a : K} (hord : 0 < ((genFibre W).j - algebraMap K (LaurentSeries K) a).order) :
    (W.map (PowerSeries.constantCoeff (R := K))).j = a := by
  have h : (genFibre W).j - algebraMap K (LaurentSeries K) a
      = algebraMap (PowerSeries K) (LaurentSeries K) (W.j - PowerSeries.C (R := K) a) := by
    rw [j_genFibre, algebraMap_laurentSeries_factor, map_sub]
  have h0 : (algebraMap (PowerSeries K) (LaurentSeries K)
      (W.j - PowerSeries.C (R := K) a)).coeff 0 = 0 :=
    HahnSeries.coeff_eq_zero_of_lt_order (by rw [← h]; exact hord)
  rw [LaurentSeries.coe_algebraMap, PowerSeries.coeff_coe, if_neg (lt_irrefl _), Int.natAbs_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, map_sub, PowerSeries.constantCoeff_C,
    sub_eq_zero] at h0
  rw [W.map_j]
  exact h0

end Core
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck"

section Assembly

variable (q : ℕ) {N : ℕ} [NeZero N] {K : Type*} [Field K] [Fact q.Prime] [CharP K q] [IsAlgClosed K]
  (hqN : ¬ q ∣ N) {data : ModularPolynomialData N} {x₀ : LaurentSeries K} {D : Deck x₀} {a : K}

private abbrev jSub (K : Type*) [Field K] (N : ℕ) [NeZero N] (a : K) : ↥(modularFunctionFieldC K N) :=
  jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) a

private def emb (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) (y : Roots data x₀) :
    ↥(modularFunctionFieldC K N) →ₐ[K] LaurentSeries K :=
  ιOfRoot q N K hqN data (transcendental_of_order_sub_pos hord) (isRoot_val y)

private def pl (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) (y : Roots data x₀) :
    Place K ↥(modularFunctionFieldC K N) :=
  wOfRoot q N K hqN data (transcendental_of_order_sub_pos hord) (isRoot_val y) hord

private def idx (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) (y : Roots data x₀) : ℕ :=
  gammaOfRoot q N K hqN data (transcendental_of_order_sub_pos hord) (isRoot_val y) hord

private theorem emb_jGeomGen (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (y : Roots data x₀) : emb q hqN hord y (jGeomGen K N) = x₀ :=
  ιOfRoot_jGeomGen q N K hqN data _ _

private theorem emb_jNGeomGen (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (y : Roots data x₀) : emb q hqN hord y (jNGeomGen K N) = y.1 :=
  ιOfRoot_jNGeomGen q N K hqN data _ _

private theorem emb_jSub (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (y : Roots data x₀) :
    emb q hqN hord y (jSub K N a) = x₀ - algebraMap K (LaurentSeries K) a := by
  show emb q hqN hord y (jGeomGen K N - algebraMap K ↥(modularFunctionFieldC K N) a) = _
  rw [map_sub, emb_jGeomGen, AlgHom.commutes]

private theorem emb_injective (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) :
    Function.Injective (emb q hqN hord (data := data)) := by
  intro y y' h
  apply Subtype.ext
  rw [← emb_jNGeomGen q hqN hord y, ← emb_jNGeomGen q hqN hord y', h]

private theorem emb_smul (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (g : ↥D.Γ) (y : Roots data x₀) :
    emb q hqN hord (g • y) = (SsfrobDeck.qTwistAlgHom (g : Kˣ)).comp (emb q hqN hord y) := by
  refine modularFunctionFieldC_algHom_ext K N ?_ ?_
  · show emb q hqN hord (g • y) (jGeomGen K N) = qTwist (g : Kˣ) (emb q hqN hord y (jGeomGen K N))
    rw [emb_jGeomGen, emb_jGeomGen, D.fix _ g.2]
  · show emb q hqN hord (g • y) (jNGeomGen K N) = qTwist (g : Kˣ) (emb q hqN hord y (jNGeomGen K N))
    rw [emb_jNGeomGen, emb_jNGeomGen]
    rfl

private theorem ord_pl_mul_idx (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (y : Roots data x₀) (z : ↥(modularFunctionFieldC K N)) :
    (pl q hqN hord y).ord z * (idx q hqN hord y : ℤ) = (emb q hqN hord y z).order :=
  ord_wOfAlgHom_mul_gamma (emb q hqN hord y)
    (exists_order_ne_zero_of_order_sub_pos q N K hqN data _ _ hord) z

private theorem idx_pos (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) (y : Roots data x₀) :
    0 < idx q hqN hord y :=
  gammaOfAlgHom_pos (emb q hqN hord y) (exists_order_ne_zero_of_order_sub_pos q N K hqN data _ _ hord)

private theorem mem_pl_iff (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) (y : Roots data x₀)
    (z : ↥(modularFunctionFieldC K N)) :
    z ∈ (pl q hqN hord y).toValuationSubring ↔ 0 ≤ (emb q hqN hord y z).order :=
  mem_wOfAlgHom_iff (emb q hqN hord y) (exists_order_ne_zero_of_order_sub_pos q N K hqN data _ _ hord) z

private theorem pl_ord_pos (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order) (y : Roots data x₀) :
    0 < (pl q hqN hord y).ord (jSub K N a) :=
  wOfRoot_ord_j_sub_pos q N K hqN data _ _ hord

private theorem pl_smul (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (g : ↥D.Γ) (y : Roots data x₀) :
    pl q hqN hord (g • y) = pl q hqN hord y ∧ idx q hqN hord (g • y) = idx q hqN hord y :=
  SsfrobDeck.place_eq_of_eq_qTwist_comp (pl q hqN hord y) (pl q hqN hord (g • y))
    (emb q hqN hord y) (emb q hqN hord (g • y)) (idx q hqN hord y) (idx q hqN hord (g • y))
    (idx_pos q hqN hord y) (idx_pos q hqN hord (g • y))
    (ord_pl_mul_idx q hqN hord y) (ord_pl_mul_idx q hqN hord (g • y)) (g : Kˣ)
    (fun z => by rw [emb_smul]; rfl)

private theorem ord_pl_mul_idx_eq (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (y : Roots data x₀) :
    (pl q hqN hord y).ord (jSub K N a) * (idx q hqN hord y : ℤ)
      = (x₀ - algebraMap K (LaurentSeries K) a).order := by
  rw [ord_pl_mul_idx, emb_jSub]

private theorem pow_idx_eq_one_of_smul_eq (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    {g : ↥D.Γ} {y : Roots data x₀} (hg : g • y = y) :
    ((g : Kˣ) : K) ^ idx q hqN hord y = 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (pl q hqN hord y).toValuationSubring
  have h1 : (pl q hqN hord y).ord (π : ↥(modularFunctionFieldC K N)) = 1 :=
    (pl q hqN hord y).ord_coe_irreducible hπ
  have hπ0 : (π : ↥(modularFunctionFieldC K N)) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hf0 : emb q hqN hord y (π : ↥(modularFunctionFieldC K N)) ≠ 0 := by
    simpa using hπ0
  have hford : (emb q hqN hord y (π : ↥(modularFunctionFieldC K N))).order
      = (idx q hqN hord y : ℤ) := by
    rw [← ord_pl_mul_idx q hqN hord y (π : ↥(modularFunctionFieldC K N)), h1, one_mul]
  have hfix : qTwist (g : Kˣ) (emb q hqN hord y (π : ↥(modularFunctionFieldC K N)))
      = emb q hqN hord y (π : ↥(modularFunctionFieldC K N)) := by
    have h := emb_smul q hqN hord g y
    rw [hg] at h
    have h' := DFunLike.congr_fun h (π : ↥(modularFunctionFieldC K N))
    rw [AlgHom.comp_apply, SsfrobDeck.qTwistAlgHom_apply] at h'
    exact h'.symm
  by_contra hne
  refine hf0 (HahnSeries.coeff_order_eq_zero.mp
    (SsfrobDeck.coeff_eq_zero_of_qTwist_eq_self (g : Kˣ) hfix _ ?_))
  rw [hford, zpow_natCast, Units.val_pow_eq_pow_val]
  exact hne

private theorem card_stabilizer_le_idx (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (y : Roots data x₀) :
    Nat.card ↥(MulAction.stabilizer ↥D.Γ y) ≤ idx q hqN hord y := by
  classical
  have hγ : 0 < idx q hqN hord y := idx_pos q hqN hord y
  let φ : ↥(MulAction.stabilizer ↥D.Γ y) →
      {x : K // x ∈ (Polynomial.nthRoots (idx q hqN hord y) (1 : K)).toFinset} :=
    fun g => ⟨(((g : ↥D.Γ) : Kˣ) : K), by
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hγ]
      exact pow_idx_eq_one_of_smul_eq q hqN hord (MulAction.mem_stabilizer_iff.mp g.2)⟩
  have hφ : Function.Injective φ := by
    intro g g' h
    have h' : (((g : ↥D.Γ) : Kˣ) : K) = (((g' : ↥D.Γ) : Kˣ) : K) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Units.ext h'))
  calc Nat.card ↥(MulAction.stabilizer ↥D.Γ y)
      ≤ Nat.card {x : K // x ∈ (Polynomial.nthRoots (idx q hqN hord y) (1 : K)).toFinset} :=
        Nat.card_le_card_of_injective φ hφ
    _ = (Polynomial.nthRoots (idx q hqN hord y) (1 : K)).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ Multiset.card (Polynomial.nthRoots (idx q hqN hord y) (1 : K)) :=
        Multiset.toFinset_card_le _
    _ ≤ idx q hqN hord y := Polynomial.card_nthRoots _ _

private theorem toNat_ord_le_ncard_orbit (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    (hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥D.Γ) (y : Roots data x₀) :
    ((pl q hqN hord y).ord (jSub K N a)).toNat ≤ (MulAction.orbit ↥D.Γ y).ncard := by
  have hkey : (pl q hqN hord y).ord (jSub K N a) * (idx q hqN hord y : ℤ) = Nat.card ↥D.Γ := by
    rw [ord_pl_mul_idx_eq, hm]
  have hE : ((((pl q hqN hord y).ord (jSub K N a)).toNat : ℕ) : ℤ)
      = (pl q hqN hord y).ord (jSub K N a) :=
    Int.toNat_of_nonneg (pl_ord_pos q hqN hord y).le
  have hEq : ((pl q hqN hord y).ord (jSub K N a)).toNat * idx q hqN hord y = Nat.card ↥D.Γ := by
    have h : ((((pl q hqN hord y).ord (jSub K N a)).toNat * idx q hqN hord y : ℕ) : ℤ)
        = (Nat.card ↥D.Γ : ℤ) := by
      rw [Nat.cast_mul, hE]
      exact hkey
    exact_mod_cast h
  have hos : (MulAction.orbit ↥D.Γ y).ncard * Nat.card ↥(MulAction.stabilizer ↥D.Γ y)
      = Nat.card ↥D.Γ := by
    rw [← MulAction.index_stabilizer]
    exact Subgroup.index_mul_card _
  have hs := card_stabilizer_le_idx q hqN hord (D := D) y
  refine Nat.le_of_mul_le_mul_right ?_ (idx_pos q hqN hord y)
  calc ((pl q hqN hord y).ord (jSub K N a)).toNat * idx q hqN hord y
      = (MulAction.orbit ↥D.Γ y).ncard * Nat.card ↥(MulAction.stabilizer ↥D.Γ y) := by
        rw [hEq, hos]
    _ ≤ (MulAction.orbit ↥D.Γ y).ncard * idx q hqN hord y := Nat.mul_le_mul_left _ hs

private theorem card_filter_le (hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order)
    [DecidableEq (Place K ↥(modularFunctionFieldC K N))]
    (htame : ((Nat.card ↥D.Γ : ℕ) : K) ≠ 0)
    (hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥D.Γ)
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : 0 < w.ord (jSub K N a)) :
    (Finset.univ.filter fun y : Roots data x₀ => pl q hqN hord y = w).card
      ≤ (w.ord (jSub K N a)).toNat := by
  classical
  haveI : DecidableEq (↥(modularFunctionFieldC K N) →ₐ[K] LaurentSeries K) := Classical.decEq _
  rcases (Finset.univ.filter fun y : Roots data x₀ => pl q hqN hord y = w).eq_empty_or_nonempty
    with h0 | ⟨y₀, hy₀⟩
  · rw [h0, Finset.card_empty]
    exact Nat.zero_le _
  have hw₀ : pl q hqN hord y₀ = w := (Finset.mem_filter.mp hy₀).2
  have hkey : w.ord (jSub K N a) * (idx q hqN hord y₀ : ℤ) = Nat.card ↥D.Γ := by
    rw [← hw₀, ord_pl_mul_idx_eq, hm]
  have he : ((w.ord (jSub K N a)).toNat : K) ≠ 0 := by
    intro he0
    apply htame
    have h1 : (((w.ord (jSub K N a)).toNat : ℕ) : ℤ) = w.ord (jSub K N a) :=
      Int.toNat_of_nonneg hw.le
    have h2 : (w.ord (jSub K N a)).toNat * idx q hqN hord y₀ = Nat.card ↥D.Γ := by
      have h : ((((w.ord (jSub K N a)).toNat * idx q hqN hord y₀ : ℕ)) : ℤ)
          = (Nat.card ↥D.Γ : ℤ) := by
        rw [Nat.cast_mul, h1]
        exact hkey
      exact_mod_cast h
    rw [← h2, Nat.cast_mul, he0, zero_mul]
  have hSx : ∀ ι ∈ (Finset.univ.filter fun y : Roots data x₀ => pl q hqN hord y = w).image
      (emb q hqN hord), ι (jSub K N a) = x₀ - algebraMap K (LaurentSeries K) a := by
    intro ι hι
    obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hι
    exact emb_jSub q hqN hord y
  have hSw : ∀ ι ∈ (Finset.univ.filter fun y : Roots data x₀ => pl q hqN hord y = w).image
      (emb q hqN hord), ∀ z : ↥(modularFunctionFieldC K N),
        z ∈ w.toValuationSubring ↔ 0 ≤ (ι z).order := by
    intro ι hι z
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hι
    rw [← (Finset.mem_filter.mp hy).2]
    exact mem_pl_iff q hqN hord y z
  have h := SsfrobR4a.card_le_ord_of_cast_ne_zero w (jSub K N a) hw he
    (x₀ - algebraMap K (LaurentSeries K) a) _ hSx hSw
  rw [Finset.card_image_of_injective _ (emb_injective q hqN hord (data := data))] at h
  exact (Int.le_toNat hw.le).mpr h

omit [IsAlgClosed K] in

private theorem order_pos_of_deck (htame : ((Nat.card ↥D.Γ : ℕ) : K) ≠ 0)
    (hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥D.Γ) :
    0 < (x₀ - algebraMap K (LaurentSeries K) a).order := by
  rw [hm]
  have hne : Nat.card ↥D.Γ ≠ 0 := fun h0 => htame (by rw [h0, Nat.cast_zero])
  exact_mod_cast Nat.pos_of_ne_zero hne

private theorem psi (htame : ((Nat.card ↥D.Γ : ℕ) : K) ≠ 0)
    (hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥D.Γ)
    (hcard : (rootFinset data x₀).card = dedekindPsi N)
    (T : Finset (Place K ↥(modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jSub K N a)) :
    (∀ w ∈ T, ∃ y : Roots data x₀, pl q hqN (order_pos_of_deck htame hm) y = w) ∧
    (∀ y y' : Roots data x₀,
      pl q hqN (order_pos_of_deck htame hm) y = pl q hqN (order_pos_of_deck htame hm) y'
        ↔ ∃ g : ↥D.Γ, g • y = y') ∧
    (∀ y : Roots data x₀, ((MulAction.orbit ↥D.Γ y).ncard : ℤ)
        = (pl q hqN (order_pos_of_deck htame hm) y).ord (jSub K N a)) := by
  classical
  have hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order := order_pos_of_deck htame hm
  have hS : ∀ y : Roots data x₀, pl q hqN hord y ∈ T :=
    fun y => (hT _).mpr (pl_ord_pos q hqN hord y)
  have hsumZ := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN K
    (isSeparable_jqNModC_of_good K N q hqN) a T hT
  have hsum : ∑ w ∈ T, (w.ord (jSub K N a)).toNat = Fintype.card (Roots data x₀) := by
    rw [card_roots, hcard]
    have h : ((∑ w ∈ T, (w.ord (jSub K N a)).toNat : ℕ) : ℤ) = (dedekindPsi N : ℤ) := by
      rw [Nat.cast_sum, ← hsumZ]
      exact Finset.sum_congr rfl fun w hw => Int.toNat_of_nonneg ((hT w).mp hw).le
    exact_mod_cast h
  have hle := fun w (hw : w ∈ T) => card_filter_le q hqN hord (data := data) htame hm w ((hT w).mp hw)
  have hinv : ∀ (g : ↥D.Γ) (y : Roots data x₀), pl q hqN hord (g • y) = pl q hqN hord y :=
    fun g y => (pl_smul q hqN hord g y).1
  have horb := fun y : Roots data x₀ => toNat_ord_le_ncard_orbit q hqN hord hm y
  have hpos : ∀ w ∈ T, 0 < (w.ord (jSub K N a)).toNat := fun w hw => by
    have h := (hT w).mp hw
    omega
  refine ⟨?_, ?_, ?_⟩
  · exact SsfrobCount.exists_apply_eq_of_sum_eq_card (pl q hqN hord) T hS
      (fun w => (w.ord (jSub K N a)).toNat) hsum hle hpos
  · intro y y'
    constructor
    · intro h
      exact SsfrobCount.exists_smul_eq_of_apply_eq (pl q hqN hord) hinv T hS
        (fun w => (w.ord (jSub K N a)).toNat) hsum hle horb h
    · rintro ⟨g, rfl⟩
      exact (hinv g y).symm
  · intro y
    rw [SsfrobCount.ncard_orbit_eq (pl q hqN hord) hinv T hS
      (fun w => (w.ord (jSub K N a)).toNat) hsum hle horb y]
    exact Int.toNat_of_nonneg (pl_ord_pos q hqN hord y).le

open scoped Classical in

private theorem _root_.SsfrobPsi.orbitLift_bijective (htame : ((Nat.card ↥D.Γ : ℕ) : K) ≠ 0)
    (hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥D.Γ)
    (hcard : (rootFinset data x₀).card = dedekindPsi N)
    (T : Finset (Place K ↥(modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jSub K N a)) :
    Function.Bijective (SsfrobCount.orbitLift
      (pl q hqN (order_pos_of_deck htame hm) (data := data))
      (fun (g : ↥D.Γ) (y : Roots data x₀) => (pl_smul q hqN (order_pos_of_deck htame hm) g y).1) T
      (fun (y : Roots data x₀) => (hT _).mpr (pl_ord_pos q hqN (order_pos_of_deck htame hm) y))) := by
  have hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order := order_pos_of_deck htame hm
  have hS : ∀ y : Roots data x₀, pl q hqN hord y ∈ T :=
    fun y => (hT _).mpr (pl_ord_pos q hqN hord y)
  have hsumZ := ModularCurve.sum_ord_jGeomGen_sub_eq_dedekindPsi q N hqN K
    (isSeparable_jqNModC_of_good K N q hqN) a T hT
  have hsum : ∑ w ∈ T, (w.ord (jSub K N a)).toNat = Fintype.card (Roots data x₀) := by
    rw [card_roots, hcard]
    have h : ((∑ w ∈ T, (w.ord (jSub K N a)).toNat : ℕ) : ℤ) = (dedekindPsi N : ℤ) := by
      rw [Nat.cast_sum, ← hsumZ]
      exact Finset.sum_congr rfl fun w hw => Int.toNat_of_nonneg ((hT w).mp hw).le
    exact_mod_cast h
  have hle := fun w (hw : w ∈ T) => card_filter_le q hqN hord (data := data) htame hm w ((hT w).mp hw)
  have hinv : ∀ (g : ↥D.Γ) (y : Roots data x₀), pl q hqN hord (g • y) = pl q hqN hord y :=
    fun g y => (pl_smul q hqN hord g y).1
  have horb := fun y : Roots data x₀ => toNat_ord_le_ncard_orbit q hqN hord hm y
  have hpos : ∀ w ∈ T, 0 < (w.ord (jSub K N a)).toNat := fun w hw => by
    have h := (hT w).mp hw
    omega
  exact SsfrobCount.orbitLift_bijective (pl q hqN hord) hinv T hS
    (fun w => (w.ord (jSub K N a)).toNat) hsum hle horb hpos

p2m_export "SsfrobPsi" "orbitLift_bijective"

private theorem psi_family (W : WeierstrassCurve (PowerSeries K)) [W.IsElliptic] (D : Deck (genFibre W).j)
    (htame : ((Nat.card ↥D.Γ : ℕ) : K) ≠ 0)
    (hm : ((genFibre W).j - algebraMap K (LaurentSeries K) a).order = Nat.card ↥D.Γ)
    (hcard : (rootFinset data (genFibre W).j).card = dedekindPsi N)
    (T : Finset (Place K ↥(modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jSub K N a)) :
    (∀ w ∈ T, ∃ y : Roots data (genFibre W).j, pl q hqN (order_pos_of_deck htame hm) y = w) ∧
    (∀ y y' : Roots data (genFibre W).j,
      pl q hqN (order_pos_of_deck htame hm) y = pl q hqN (order_pos_of_deck htame hm) y'
        ↔ ∃ g : ↥D.Γ, g • y = y') ∧
    (∀ y : Roots data (genFibre W).j, ((MulAction.orbit ↥D.Γ y).ncard : ℤ)
        = (pl q hqN (order_pos_of_deck htame hm) y).ord (jSub K N a)) :=
  psi q hqN htame hm hcard T hT

omit [IsAlgClosed K] in
private theorem order_pos_of_eq_one (h1 : (x₀ - algebraMap K (LaurentSeries K) a).order = 1) :
    0 < (x₀ - algebraMap K (LaurentSeries K) a).order := by
  rw [h1]
  exact one_pos

private theorem psi_generic (h1 : (x₀ - algebraMap K (LaurentSeries K) a).order = 1)
    (hcard : (rootFinset data x₀).card = dedekindPsi N)
    (T : Finset (Place K ↥(modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jSub K N a)) :
    (∀ w ∈ T, ∃ y : Roots data x₀, pl q hqN (order_pos_of_eq_one h1) y = w) ∧
    (∀ y y' : Roots data x₀,
      pl q hqN (order_pos_of_eq_one h1) y = pl q hqN (order_pos_of_eq_one h1) y' → y = y') ∧
    (∀ y : Roots data x₀,
      (pl q hqN (order_pos_of_eq_one h1) y).ord (jSub K N a) = 1) := by
  have hΓ : Nat.card ↥(Deck.trivial x₀).Γ = 1 := Subgroup.card_bot
  have htame : ((Nat.card ↥(Deck.trivial x₀).Γ : ℕ) : K) ≠ 0 := by
    rw [hΓ, Nat.cast_one]
    exact one_ne_zero
  have hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥(Deck.trivial x₀).Γ := by
    rw [hΓ, Nat.cast_one]
    exact h1
  have hg1 : ∀ g : ↥(Deck.trivial x₀).Γ, g = 1 := fun g => Subtype.ext (Subgroup.mem_bot.mp g.2)
  have horbit : ∀ y : Roots data x₀,
      MulAction.orbit ↥(Deck.trivial x₀).Γ y = {y} := by
    intro y
    ext z
    constructor
    · rintro ⟨g, rfl⟩
      show g • y ∈ ({y} : Set (Roots data x₀))
      rw [Set.mem_singleton_iff, hg1 g, one_smul]
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact MulAction.mem_orbit_self y
  obtain ⟨hsurj, hinj, hcnt⟩ := psi q hqN htame hm hcard T hT
  refine ⟨hsurj, fun y y' h => ?_, fun y => ?_⟩
  · obtain ⟨g, hg⟩ := (hinj y y').mp h
    rw [← hg, hg1 g, one_smul]
  · have h := hcnt y
    rw [horbit y, Set.ncard_singleton, Nat.cast_one] at h
    exact h.symm

omit [IsAlgClosed K] in

private theorem order_j_genFibre_famNe_sub {a : K} [(SsfrobFam.famNe K a).IsElliptic]
    (ha : a ≠ 0) (ha' : a ≠ 1728) :
    ((genFibre (SsfrobFam.famNe K a)).j - algebraMap K (LaurentSeries K) a).order = 1 :=
  SsfrobFam.order_j_sub_algebraMap a ha ha'

private theorem psi_famNe {a : K} [(SsfrobFam.famNe K a).IsElliptic] (ha : a ≠ 0) (ha' : a ≠ 1728)
    (hcard : (rootFinset data (genFibre (SsfrobFam.famNe K a)).j).card = dedekindPsi N)
    (T : Finset (Place K ↥(modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jSub K N a)) :
    (∀ w ∈ T, ∃ y : Roots data (genFibre (SsfrobFam.famNe K a)).j,
      pl q hqN (order_pos_of_eq_one (order_j_genFibre_famNe_sub ha ha')) y = w) ∧
    (∀ y y' : Roots data (genFibre (SsfrobFam.famNe K a)).j,
      pl q hqN (order_pos_of_eq_one (order_j_genFibre_famNe_sub ha ha')) y
        = pl q hqN (order_pos_of_eq_one (order_j_genFibre_famNe_sub ha ha')) y' → y = y') ∧
    (∀ y : Roots data (genFibre (SsfrobFam.famNe K a)).j,
      (pl q hqN (order_pos_of_eq_one (order_j_genFibre_famNe_sub ha ha')) y).ord (jSub K N a)
        = 1) :=
  psi_generic q hqN (order_j_genFibre_famNe_sub ha ha') hcard T hT

end Assembly
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck"

section Elliptic

variable {K : Type*} [Field K]

private def deck1728 (K : Type*) [Field K] [IsAlgClosed K] [(fam1728 K).IsElliptic] :
    Deck (genFibre (fam1728 K)).j :=
  ⟨rootsOfUnity 2 K, qTwist_j_genFibre_fam1728⟩

private def deck0 (K : Type*) [Field K] [(fam0 K).IsElliptic] : Deck (genFibre (fam0 K)).j :=
  ⟨rootsOfUnity 3 K, qTwist_j_genFibre_fam0⟩

private theorem deck1728_Γ (K : Type*) [Field K] [IsAlgClosed K] [(fam1728 K).IsElliptic] :
    (deck1728 K).Γ = rootsOfUnity 2 K :=
  rfl

private theorem deck0_Γ (K : Type*) [Field K] [(fam0 K).IsElliptic] : (deck0 K).Γ = rootsOfUnity 3 K :=
  rfl

private theorem order_pos_fam1728 (h6 : (6 : K) ≠ 0) [(fam1728 K).IsElliptic] :
    0 < ((genFibre (fam1728 K)).j - algebraMap K (LaurentSeries K) 1728).order := by
  rw [order_j_genFibre_fam1728_sub h6]
  norm_num

private theorem order_pos_fam0 (h6 : (6 : K) ≠ 0) [(fam0 K).IsElliptic] :
    0 < ((genFibre (fam0 K)).j - algebraMap K (LaurentSeries K) 0).order := by
  rw [order_j_genFibre_fam0_sub h6]
  norm_num

private theorem psi_fam1728 (q : ℕ) {N : ℕ} [NeZero N] [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (hqN : ¬ q ∣ N) {data : ModularPolynomialData N} (h6 : (6 : K) ≠ 0) [(fam1728 K).IsElliptic]
    (hcard : (rootFinset data (genFibre (fam1728 K)).j).card = dedekindPsi N)
    (T : Finset (Place K ↥(modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jSub K N 1728)) :
    (∀ w ∈ T, ∃ y : Roots data (genFibre (fam1728 K)).j,
      pl q hqN (order_pos_fam1728 h6) y = w) ∧
    (∀ y y' : Roots data (genFibre (fam1728 K)).j,
      pl q hqN (order_pos_fam1728 h6) y = pl q hqN (order_pos_fam1728 h6) y'
        ↔ ∃ g : ↥(deck1728 K).Γ, g • y = y') ∧
    (∀ y : Roots data (genFibre (fam1728 K)).j,
      ((MulAction.orbit ↥(deck1728 K).Γ y).ncard : ℤ)
        = (pl q hqN (order_pos_fam1728 h6) y).ord (jSub K N 1728)) := by
  have hcardΓ : Nat.card ↥(deck1728 K).Γ = 2 :=
    natCard_rootsOfUnity_two (two_ne_zero_of_six_ne_zero h6)
  have htame : ((Nat.card ↥(deck1728 K).Γ : ℕ) : K) ≠ 0 := by
    rw [hcardΓ, Nat.cast_ofNat]
    exact two_ne_zero_of_six_ne_zero h6
  have hm : ((genFibre (fam1728 K)).j - algebraMap K (LaurentSeries K) 1728).order
      = Nat.card ↥(deck1728 K).Γ := by
    rw [hcardΓ, Nat.cast_ofNat]
    exact order_j_genFibre_fam1728_sub h6
  exact psi_family q hqN (fam1728 K) (deck1728 K) htame hm hcard T hT

private theorem psi_fam0 (q : ℕ) {N : ℕ} [NeZero N] [Fact q.Prime] [CharP K q] [IsAlgClosed K]
    (hqN : ¬ q ∣ N) {data : ModularPolynomialData N} (h6 : (6 : K) ≠ 0) [(fam0 K).IsElliptic]
    (hcard : (rootFinset data (genFibre (fam0 K)).j).card = dedekindPsi N)
    (T : Finset (Place K ↥(modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (jSub K N 0)) :
    (∀ w ∈ T, ∃ y : Roots data (genFibre (fam0 K)).j, pl q hqN (order_pos_fam0 h6) y = w) ∧
    (∀ y y' : Roots data (genFibre (fam0 K)).j,
      pl q hqN (order_pos_fam0 h6) y = pl q hqN (order_pos_fam0 h6) y'
        ↔ ∃ g : ↥(deck0 K).Γ, g • y = y') ∧
    (∀ y : Roots data (genFibre (fam0 K)).j,
      ((MulAction.orbit ↥(deck0 K).Γ y).ncard : ℤ)
        = (pl q hqN (order_pos_fam0 h6) y).ord (jSub K N 0)) := by
  have hcardΓ : Nat.card ↥(deck0 K).Γ = 3 :=
    natCard_rootsOfUnity_three (three_ne_zero_of_six_ne_zero h6)
  have htame : ((Nat.card ↥(deck0 K).Γ : ℕ) : K) ≠ 0 := by
    rw [hcardΓ, Nat.cast_ofNat]
    exact three_ne_zero_of_six_ne_zero h6
  have hm : ((genFibre (fam0 K)).j - algebraMap K (LaurentSeries K) 0).order
      = Nat.card ↥(deck0 K).Γ := by
    rw [hcardΓ, Nat.cast_ofNat]
    exact order_j_genFibre_fam0_sub h6
  exact psi_family q hqN (fam0 K) (deck0 K) htame hm hcard T hT

end Elliptic
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck"

section Row

variable {N : ℕ} [NeZero N] {K : Type*} [Field K] {data : ModularPolynomialData N}
  {x₀ : LaurentSeries K}

private theorem separable_phiAt (q : ℕ) [Fact q.Prime] [CharP K q] (hqN : ¬ q ∣ N)
    (hx : Transcendental K x₀) : (phiAt data x₀).Separable := by
  have hsep : (SsfrobWlocSkin.wlocPhi K N data).Separable := by
    rw [← SsfrobWlocSkin.minpoly_wloc_eq q N K hqN data]
    exact isSeparable_jqNModC_of_good K N q hqN
  have hmap : (SsfrobWlocSkin.wlocPhi K N data).map
      (SsfrobWlocSkin.baseHom K hx : ↥(SsfrobWlocSkin.wlocJAdj K) →+* LaurentSeries K)
        = phiAt data x₀ := by
    rw [phiAt, Polynomial.map_map]
    congr 1
    refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
    simp only [RingHom.coe_comp, Function.comp_apply, Polynomial.coe_eval₂RingHom,
      Polynomial.eval₂_X, RingHom.coe_coe]
    exact SsfrobWlocSkin.baseHom_gen K hx
  rw [← hmap]
  exact hsep.map

private theorem card_rootFinset_of_card_roots (q : ℕ) [Fact q.Prime] [CharP K q] (hqN : ¬ q ∣ N)
    (hx : Transcendental K x₀) (h : Multiset.card (phiAt data x₀).roots = dedekindPsi N) :
    (rootFinset data x₀).card = dedekindPsi N := by
  classical
  rw [← h]
  exact Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots (separable_phiAt q hqN hx))

end Row
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck"

private theorem psi_row (q N : ℕ) [NeZero N] (K : Type*) [Field K] [Fact q.Prime]
    [CharP K q] [IsAlgClosed K] (hqN : ¬ q ∣ N) (data : ModularPolynomialData N) (a : K)
    (x₀ : LaurentSeries K) (Γ : Subgroup Kˣ)
    (hΓ : ∀ u ∈ Γ, ModularCurve.qTwist u x₀ = x₀)
    (htame : ((Nat.card ↥Γ : ℕ) : K) ≠ 0)
    (hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥Γ)
    [DecidableEq (LaurentSeries K)]
    (hcard : ((data.Φ.map
        (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).roots.toFinset).card
      = dedekindPsi N)
    (T : Finset (AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (ModularCurve.jGeomGen K N
        - algebraMap K ↥(ModularCurve.modularFunctionFieldC K N) a)) :
    ∃ f : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
          → AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N),
      (∀ w ∈ T, ∃ y, f y = w) ∧
      (∀ y y', f y = f y' ↔ ∃ u ∈ Γ, ModularCurve.qTwist u y.1 = y'.1) ∧
      (∀ y, (Set.ncard {y' : {z : LaurentSeries K //
              (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
            | ∃ u ∈ Γ, ModularCurve.qTwist u y.1 = y'.1} : ℤ)
          = (f y).ord (ModularCurve.jGeomGen K N
              - algebraMap K ↥(ModularCurve.modularFunctionFieldC K N) a)) := by
  have hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order :=
    order_pos_of_deck (D := Deck.ofSubgroup Γ hΓ) htame hm
  have hfin : rootFinset data x₀
      = (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).roots.toFinset :=
    congrArg (fun i : DecidableEq (LaurentSeries K) => @Multiset.toFinset (LaurentSeries K) i
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).roots)
      (Subsingleton.elim _ _)
  have hcard' : (rootFinset data x₀).card = dedekindPsi N := by
    rw [hfin]
    exact hcard
  obtain ⟨h1, h2, h3⟩ := psi q hqN (D := Deck.ofSubgroup Γ hΓ) htame hm hcard' T hT
  let e : {z : LaurentSeries K //
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
        ≃ Roots data x₀ :=
    Equiv.subtypeEquivRight fun y => (mem_rootFinset_iff data x₀ y).symm
  refine ⟨fun y => pl q hqN hord (e y), fun w hw => ?_, fun y y' => ?_, fun y => ?_⟩
  · obtain ⟨z, hz⟩ := h1 w hw
    refine ⟨e.symm z, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hz
  · constructor
    · intro h
      obtain ⟨g, hg⟩ := (h2 (e y) (e y')).mp h
      exact ⟨(g : Kˣ), g.2, congrArg Subtype.val hg⟩
    · rintro ⟨u, hu, huy⟩
      exact (h2 (e y) (e y')).mpr ⟨⟨u, hu⟩, Subtype.ext huy⟩
  · have hset : {y' : {z : LaurentSeries K //
          (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
        | ∃ u ∈ Γ, ModularCurve.qTwist u y.1 = y'.1}
          = e ⁻¹' (MulAction.orbit ↥(Deck.ofSubgroup Γ hΓ).Γ (e y)) := by
      ext y'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨u, hu, huy⟩
        exact ⟨⟨u, hu⟩, Subtype.ext huy⟩
      · rintro ⟨g, hg⟩
        exact ⟨(g : Kˣ), g.2, congrArg Subtype.val hg⟩
    rw [hset, Set.ncard_preimage_of_injective_subset_range e.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)]
    exact h3 (e y)

end SsfrobPsi
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi"

section FilingHead

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi"

theorem solution (q N : ℕ) [NeZero N] (K : Type*) [Field K] [Fact q.Prime]
    [CharP K q] [IsAlgClosed K] (hqN : ¬ q ∣ N) (data : ModularPolynomialData N) (a : K)
    (x₀ : LaurentSeries K) (Γ : Subgroup Kˣ)
    (hΓ : ∀ u ∈ Γ, ModularCurve.qTwist u x₀ = x₀)
    (htame : ((Nat.card ↥Γ : ℕ) : K) ≠ 0)
    (hm : (x₀ - algebraMap K (LaurentSeries K) a).order = Nat.card ↥Γ)
    [DecidableEq (LaurentSeries K)]
    (hcard : ((data.Φ.map
        (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).roots.toFinset).card
      = dedekindPsi N)
    (T : Finset (AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N)))
    (hT : ∀ w, w ∈ T ↔ 0 < w.ord (ModularCurve.jGeomGen K N
        - algebraMap K ↥(ModularCurve.modularFunctionFieldC K N) a)) :
    ∃ f : {z : LaurentSeries K //
            (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
          → AlgebraicCurve.Place K ↥(ModularCurve.modularFunctionFieldC K N),
      (∀ y, ∃ ι : ↥(ModularCurve.modularFunctionFieldC K N) →ₐ[K] LaurentSeries K,
        ι (ModularCurve.jGeomGen K N) = x₀ ∧ ι (ModularCurve.jNGeomGen K N) = y.1 ∧
        ∀ x, x ∈ (f y).toValuationSubring ↔ 0 ≤ (ι x).order) ∧
      (∀ w ∈ T, ∃ y, f y = w) ∧
      (∀ y y', f y = f y' ↔ ∃ u ∈ Γ, ModularCurve.qTwist u y.1 = y'.1) ∧
      (∀ y, (Set.ncard {y' : {z : LaurentSeries K //
              (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
            | ∃ u ∈ Γ, ModularCurve.qTwist u y.1 = y'.1} : ℤ)
          = (f y).ord (ModularCurve.jGeomGen K N
              - algebraMap K ↥(ModularCurve.modularFunctionFieldC K N) a)) := by
  have hord : 0 < (x₀ - algebraMap K (LaurentSeries K) a).order :=
    order_pos_of_deck (D := Deck.ofSubgroup Γ hΓ) htame hm
  have hfin : rootFinset data x₀
      = (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).roots.toFinset :=
    congrArg (fun i : DecidableEq (LaurentSeries K) => @Multiset.toFinset (LaurentSeries K) i
        (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).roots)
      (Subsingleton.elim _ _)
  have hcard' : (rootFinset data x₀).card = dedekindPsi N := by
    rw [hfin]
    exact hcard
  obtain ⟨h1, h2, h3⟩ := psi q hqN (D := Deck.ofSubgroup Γ hΓ) htame hm hcard' T hT
  let e : {z : LaurentSeries K //
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
        ≃ Roots data x₀ :=
    Equiv.subtypeEquivRight fun y => (mem_rootFinset_iff data x₀ y).symm
  refine ⟨fun y => pl q hqN hord (e y), fun y => ?_, fun w hw => ?_, fun y y' => ?_, fun y => ?_⟩
  · exact ⟨emb q hqN hord (e y), emb_jGeomGen q hqN hord (e y), emb_jNGeomGen q hqN hord (e y),
      fun x => mem_pl_iff q hqN hord (e y) x⟩
  · obtain ⟨z, hz⟩ := h1 w hw
    refine ⟨e.symm z, ?_⟩
    simp only [Equiv.apply_symm_apply]
    exact hz
  · constructor
    · intro h
      obtain ⟨g, hg⟩ := (h2 (e y) (e y')).mp h
      exact ⟨(g : Kˣ), g.2, congrArg Subtype.val hg⟩
    · rintro ⟨u, hu, huy⟩
      exact (h2 (e y) (e y')).mpr ⟨⟨u, hu⟩, Subtype.ext huy⟩
  · have hset : {y' : {z : LaurentSeries K //
          (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K)) x₀)).IsRoot z}
        | ∃ u ∈ Γ, ModularCurve.qTwist u y.1 = y'.1}
          = e ⁻¹' (MulAction.orbit ↥(Deck.ofSubgroup Γ hΓ).Γ (e y)) := by
      ext y'
      simp only [Set.mem_setOf_eq, Set.mem_preimage, MulAction.mem_orbit_iff]
      constructor
      · rintro ⟨u, hu, huy⟩
        exact ⟨⟨u, hu⟩, Subtype.ext huy⟩
      · rintro ⟨g, hg⟩
        exact ⟨(g : Kˣ), g.2, congrArg Subtype.val hg⟩
    rw [hset, Set.ncard_preimage_of_injective_subset_range e.injective
      (by rw [Equiv.range_eq_univ]; exact Set.subset_univ _)]
    exact h3 (e y)

end FilingHead
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi"

end
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi"

end Brick_ASSEMBLY_SRC_v5
p2m_reactivate "P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobEll4a P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam.genFibre P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.ModularCurve.EllFam P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobDeck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi.Deck P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ.SsfrobPsi"

end S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ
end P2MW
export P2MW.S_ModularCurve_exists_map_roots_places_of_card_roots_eq_dedekindPsi_univ (solution)
