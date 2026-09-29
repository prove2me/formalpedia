-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.placeFullC_eq_congr_spPlace_of_finChart_centrePin
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/8a0f45fe-9340-5025-8ed9-f376185c1e37

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_IgusaScheme_piFin_image_spans_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_finChart_centrePin
p2m_attr_erase "instance" "instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_finChart_centrePin.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_finChart_centrePin.ModularCurve.CharPModel AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme"

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar coeff_jq_neg_one ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldFullC modularFunctionFieldC_le_full jqModC modularFunctionFieldC jqModC_mem CharPModel.FibreModel IgusaScheme.jChartFin IgusaScheme.coe_jChartFin IgusaScheme CharPModel.FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff IgusaScheme.piFin_image_spans_chartAlg"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar constantsHom affineBaseFin FibreModel FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff"
namespace PInfAux
p2m_open "ModularCurve.CharPModel ModularCurve"

section ValSub

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem algebraMap_not_mem_nonunits (O : ValuationSubring F) (hO : ∀ a : K, algebraMap K F a ∈ O)
    {a : K} (ha : a ≠ 0) : algebraMap K F a ∉ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, not_or]
  refine ⟨by simpa using ha, ?_⟩
  rw [not_not, ← map_inv₀]
  exact hO _

theorem mem_of_sub_algebraMap_mem_nonunits (O : ValuationSubring F) (hO : ∀ a : K, algebraMap K F a ∈ O)
    {x : F} {c : K} (h : x - algebraMap K F c ∈ O.nonunits) : x ∈ O := by
  have hx : x = (x - algebraMap K F c) + algebraMap K F c := by ring
  rw [hx]
  exact add_mem (O.nonunits_subset h) (hO c)

theorem mem_nonunits_iff_eq_zero_of_sub_algebraMap_mem (O : ValuationSubring F)
    (hO : ∀ a : K, algebraMap K F a ∈ O) {x : F} {c : K}
    (h : x - algebraMap K F c ∈ O.nonunits) : (x ∈ O.nonunits ↔ c = 0) := by
  constructor
  · intro hx
    by_contra hc
    apply algebraMap_not_mem_nonunits O hO hc
    have hc' : algebraMap K F c = x - (x - algebraMap K F c) := by ring
    rw [hc']
    exact sub_mem hx h
  · rintro rfl
    simpa using h

variable {F' : Type*} [Field F']

theorem mem_nonunits_comap_iff (O : ValuationSubring F) (f : F' ≃+* F) (x : F') :
    x ∈ (O.comap (f : F' →+* F)).nonunits ↔ f x ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or,
    ValuationSubring.mem_comap]
  simp [map_inv₀]

end ValSub

section Span

variable {k L : Type*} [Field k] [Field L] [Algebra k L]

theorem sum_mem_nonunits_iff_of_forall_sub_algebraMap_mem (O₁ O₂ : ValuationSubring L)
    (hO₁ : ∀ a : k, algebraMap k L a ∈ O₁) (hO₂ : ∀ a : k, algebraMap k L a ∈ O₂)
    {n : ℕ} (c : Fin n → k) (s : Fin n → L) (d : Fin n → k)
    (h₁ : ∀ i, s i - algebraMap k L (d i) ∈ O₁.nonunits) (h₂ : ∀ i, s i - algebraMap k L (d i) ∈ O₂.nonunits) :
    (∑ i, algebraMap k L (c i) * s i) ∈ O₁.nonunits ↔ (∑ i, algebraMap k L (c i) * s i) ∈ O₂.nonunits := by

  have key : ∀ (O : ValuationSubring L), (∀ a : k, algebraMap k L a ∈ O) →
      (∀ i, s i - algebraMap k L (d i) ∈ O.nonunits) →
      (∑ i, algebraMap k L (c i) * s i) - algebraMap k L (∑ i, c i * d i) ∈ O.nonunits := by
    intro O hO h
    have hrw : (∑ i, algebraMap k L (c i) * s i) - algebraMap k L (∑ i, c i * d i) =
        ∑ i, algebraMap k L (c i) * (s i - algebraMap k L (d i)) := by
      simp only [map_sum, map_mul, mul_sub, Finset.sum_sub_distrib]
    rw [hrw]
    refine NonUnitalSubring.sum_mem _ fun i _ => ?_

    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    obtain ⟨hmem, hmax⟩ := (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal (A := O)).mp (h i)
    refine ⟨mul_mem (hO _) hmem, ?_⟩
    have : (⟨algebraMap k L (c i) * (s i - algebraMap k L (d i)), mul_mem (hO _) hmem⟩ : O) =
        ⟨algebraMap k L (c i), hO _⟩ * ⟨s i - algebraMap k L (d i), hmem⟩ := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ hmax
  rw [mem_nonunits_iff_eq_zero_of_sub_algebraMap_mem O₁ hO₁ (key O₁ hO₁ h₁),
    mem_nonunits_iff_eq_zero_of_sub_algebraMap_mem O₂ hO₂ (key O₂ hO₂ h₂)]

end Span

end ModularCurve.CharPModel.PInfAux

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar coeff_jq_neg_one ModularPolynomialData modularFunctionFieldFull algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_coeff laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldFullC modularFunctionFieldC_le_full jqModC modularFunctionFieldC jqModC_mem CharPModel.FibreModel IgusaScheme.jChartFin IgusaScheme.coe_jChartFin IgusaScheme CharPModel.FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff IgusaScheme.piFin_image_spans_chartAlg"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar constantsHom affineBaseFin FibreModel FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff"
namespace PInfAux
p2m_open "ModularCurve.CharPModel ModularCurve"

section ChartRingFin

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k ℓ] {red : ↥A →+* k}

theorem affineBaseFin_le_BFin (fm : FibreModel N A ℓ k red) : affineBaseFin N A ≤ fm.BFin := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | hx)
  · exact fm.constFin_mem a
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact fm.jBar_mem

theorem piFin_mem_adjoin_of_mem_affineBaseFin (fm : FibreModel N A ℓ k red)
    {x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)} (hx : x ∈ affineBaseFin N A) :
    (fm.piFin ⟨x, affineBaseFin_le_BFin fm hx⟩ : modularFunctionFieldC k N) ∈
      Algebra.adjoin k ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)} :
        Set (modularFunctionFieldC k N)) := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | hx
    · rw [fm.piFin_const a]
      exact Subalgebra.algebraMap_mem _ _
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [fm.piFin_j]
      exact Algebra.subset_adjoin (Set.mem_singleton _)
  | zero =>
    rw [show (⟨0, affineBaseFin_le_BFin fm (Subring.zero_mem _)⟩ : fm.BFin) = 0 from rfl, map_zero]
    exact zero_mem _
  | one =>
    rw [show (⟨1, affineBaseFin_le_BFin fm (Subring.one_mem _)⟩ : fm.BFin) = 1 from rfl, map_one]
    exact one_mem _
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, affineBaseFin_le_BFin fm (Subring.add_mem _ hx hy)⟩ : fm.BFin) =
      ⟨x, affineBaseFin_le_BFin fm hx⟩ + ⟨y, affineBaseFin_le_BFin fm hy⟩ from rfl, map_add]
    exact add_mem ihx ihy
  | neg x hx ih =>
    rw [show (⟨-x, affineBaseFin_le_BFin fm (Subring.neg_mem _ hx)⟩ : fm.BFin) =
      -⟨x, affineBaseFin_le_BFin fm hx⟩ from rfl, map_neg]
    exact neg_mem ih
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, affineBaseFin_le_BFin fm (Subring.mul_mem _ hx hy)⟩ : fm.BFin) =
      ⟨x, affineBaseFin_le_BFin fm hx⟩ * ⟨y, affineBaseFin_le_BFin fm hy⟩ from rfl, map_mul]
    exact mul_mem ihx ihy

theorem piFin_mem_chartRing (fm : FibreModel N A ℓ k red) (b : fm.BFin) :
    (fm.piFin b : modularFunctionFieldC k N) ∈
      AlgebraicCurve.CurveModel.chartRing k ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)} :
        Set (modularFunctionFieldC k N)) := by
  rw [AlgebraicCurve.CurveModel.mem_chartRing_iff]
  obtain ⟨P, hPm, hPev⟩ := fm.integralFin b
  set R := Algebra.adjoin k ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)} :
        Set (modularFunctionFieldC k N)) with hR
  let ι : affineBaseFin N A →+* fm.BFin := Subring.inclusion (affineBaseFin_le_BFin fm)
  have hθmem : ∀ x : affineBaseFin N A, (fm.piFin.comp ι) x ∈ R := fun x =>
    piFin_mem_adjoin_of_mem_affineBaseFin fm x.2
  let θ : affineBaseFin N A →+* R := (fm.piFin.comp ι).codRestrict R hθmem
  refine ⟨P.map θ, hPm.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap R (modularFunctionFieldC k N)).comp θ = fm.piFin.comp ι := by
    ext x; rfl
  rw [hcomp, ← Polynomial.hom_eval₂]
  have h0 : Polynomial.eval₂ ι b P = 0 := by
    apply Subtype.ext
    have h := Polynomial.hom_eval₂ P ι fm.BFin.subtype b
    have hsub : fm.BFin.subtype.comp ι = (affineBaseFin N A).subtype := by ext; rfl
    rw [hsub] at h
    exact h.trans hPev
  rw [h0, map_zero]

end ChartRingFin

theorem jBar_ne_algebraMap (N : ℕ) [NeZero N] (a : AlgebraicClosure ℚ) :
    jBar N ≠ algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) a := by
  intro h
  have h' := congrArg (fun x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N) =>
    (x : LaurentSeries (AlgebraicClosure ℚ)).coeff (-1)) h
  simp only [jBar, coeffEmb_coeff, coeff_jq_neg_one, map_one] at h'
  rw [show ((algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) a :
      laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) : LaurentSeries (AlgebraicClosure ℚ)) =
      algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) a from rfl,
    algebraMap_laurentSeries_eq_single] at h'
  simp at h'

end ModularCurve.CharPModel.PInfAux

open ModularCurve.CharPModel.PInfAux in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ p → ModularPolynomialData d)
    (hsep : (((dataAll p (dvd_refl p)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (hCF : modularFunctionFieldC (ResidueField ↥A) p = modularFunctionFieldFullC (ResidueField ↥A) p)
    (fm : FibreModel p A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A)) (cc : fm.CuspChart)
    (hfin : ∀ b : chartAlgFin p ℓ,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BFin)
    (hinf : ∀ b : chartAlgInf p ℓ,
        (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (b : ↥(modularFunctionFieldFull p)).2⟩ :
          laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ fm.BInf)
    (w : AlgebraicCurve.Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (v : AlgebraicCurve.Place (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p))
    (α : ↥(chartAlgFin p ℓ) →+* ↥A)
    (hgen : ∀ b : ↥(chartAlgFin p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ w.toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ((A.subtype.comp α) b) ∈
            w.toValuationSubring.nonunits)
    (hsp : ∀ b : ↥(chartAlgFin p ℓ),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
            v.toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piFin ⟨_, hfin b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (((IsLocalRing.residue ↥A).comp α) b) ∈
            v.toValuationSubring.nonunits) :
    v =
      AlgebraicCurve.Place.congrRingEquiv
        (e := (IntermediateField.equivOfEq hCF).toRingEquiv)
        (he := fun a => (IntermediateField.equivOfEq hCF).commutes a)
        (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep w)
:= by
  classical

  have hjc : (⟨coeffEmb (AlgebraicClosure ℚ)
        ((ModularCurve.IgusaScheme.jChartFin p ℓ : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.IgusaScheme.jChartFin p ℓ : ↥(modularFunctionFieldFull p)).2⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) = jBar p := by
    apply Subtype.ext
    simp [jBar, ModularCurve.IgusaScheme.coe_jChartFin]
  have ha₀ : 0 < w.ord (jBar p - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p))
      ((α (ModularCurve.IgusaScheme.jChartFin p ℓ) : ↥A) : AlgebraicClosure ℚ)) := by
    have hpin := (hgen (ModularCurve.IgusaScheme.jChartFin p ℓ)).2
    rw [hjc] at hpin
    have hne := sub_ne_zero.mpr (jBar_ne_algebraMap p ((α (ModularCurve.IgusaScheme.jChartFin p ℓ) : ↥A) :
      AlgebraicClosure ℚ))
    obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hpin
    exact (w.mem_maximalIdeal_iff_ord_pos hne hmem).mp hmax

  have hred : Function.Surjective (residue ↥A) := Ideal.Quotient.mk_surjective
  have he : ∀ a : ResidueField ↥A, (IntermediateField.equivOfEq hCF).toRingEquiv (algebraMap (ResidueField ↥A) _ a) = algebraMap (ResidueField ↥A) _ a :=
    fun a => (IntermediateField.equivOfEq hCF).commutes a
  have he_incl : ∀ x : ↥(modularFunctionFieldC (ResidueField ↥A) p),
      (IntermediateField.equivOfEq hCF).toRingEquiv x = IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) x := fun x => rfl

  set v' : AlgebraicCurve.Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) p) :=
    AlgebraicCurve.Place.congrRingEquiv (IntermediateField.equivOfEq hCF).toRingEquiv.symm
      (AlgebraicCurve.Place.symm_algebraMap_comm (IntermediateField.equivOfEq hCF).toRingEquiv he) v with hv'_def
  have hv'mem : ∀ x, x ∈ v'.toValuationSubring ↔ (IntermediateField.equivOfEq hCF).toRingEquiv x ∈ v.toValuationSubring := fun x => by
    rw [hv'_def, AlgebraicCurve.Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
    simp
  have hv'nu : ∀ x, x ∈ v'.toValuationSubring.nonunits ↔ (IntermediateField.equivOfEq hCF).toRingEquiv x ∈ v.toValuationSubring.nonunits := fun x => by
    rw [hv'_def, AlgebraicCurve.Place.congrRingEquiv_toValuationSubring,
      RingEquiv.symm_symm,
      mem_nonunits_comap_iff]
  set spw := fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep w with hspw_def

  let B : ↥(chartAlgFin p ℓ) → fm.BFin := fun b =>
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull p)).2⟩, hfin b⟩

  have hspw : ∀ b : ↥(chartAlgFin p ℓ), (fm.piFin (B b) : ↥(modularFunctionFieldC (ResidueField ↥A) p)) -
      algebraMap (ResidueField ↥A) _ (residue ↥A (α b)) ∈ spw.toValuationSubring.nonunits := by
    intro b
    let d : fm.BFin := B b - ⟨constantsHom p A (α b), fm.constFin_mem (α b)⟩
    have hd : (fm.piFin d : ↥(modularFunctionFieldC (ResidueField ↥A) p)) =
        fm.piFin (B b) - algebraMap (ResidueField ↥A) _ (residue ↥A (α b)) := by
      rw [map_sub, fm.piFin_const]
    rw [← hd, hspw_def]
    refine (fm.piFin_mem_spPlace_nonunits_iff Ideal.Quotient.mk_surjective dataAll hsep w _ ha₀ d).mpr
      ⟨0, zero_mem _, ?_⟩
    have : ((d : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : _) -
        algebraMap (AlgebraicClosure ℚ) _ ((0 : ↥A) : AlgebraicClosure ℚ) =
        (B b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
          algebraMap (AlgebraicClosure ℚ) _ ((A.subtype.comp α) b) := by
      simp [d, B, constantsHom]
    rw [this]
    exact (hgen b).2

  have hv' : ∀ b : ↥(chartAlgFin p ℓ), (fm.piFin (B b) : ↥(modularFunctionFieldC (ResidueField ↥A) p)) ∈
      v'.toValuationSubring ∧ (fm.piFin (B b) : ↥(modularFunctionFieldC (ResidueField ↥A) p)) -
      algebraMap (ResidueField ↥A) _ (residue ↥A (α b)) ∈ v'.toValuationSubring.nonunits := by
    intro b
    refine ⟨(hv'mem _).mpr ?_, (hv'nu _).mpr ?_⟩
    · rw [he_incl]; exact (hsp b).1
    · rw [map_sub, he, he_incl]; exact (hsp b).2

  have hB : B (ModularCurve.IgusaScheme.jChartFin p ℓ) = ⟨jBar p, fm.jBar_mem⟩ := Subtype.ext hjc
  have hj₁ : ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) p⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) p))) ∈ v'.toValuationSubring := by
    rw [← fm.piFin_j, ← hB]
    exact (hv' _).1
  have hj₂ : ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) p⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) p))) ∈ spw.toValuationSubring := by
    rw [← fm.piFin_j, ← hB]
    exact mem_of_sub_algebraMap_mem_nonunits spw.toValuationSubring spw.algebraMap_mem' (hspw _)

  have hagree : ∀ b : fm.BFin,
      ((fm.piFin b : ↥(modularFunctionFieldC (ResidueField ↥A) p)) ∈ v'.toValuationSubring.nonunits ↔
        (fm.piFin b : ↥(modularFunctionFieldC (ResidueField ↥A) p)) ∈ spw.toValuationSubring.nonunits) := by
    intro b
    obtain ⟨n, c, bb, hsum⟩ := ModularCurve.IgusaScheme.piFin_image_spans_chartAlg p ℓ hℓp A fm hfin
      (fm.piFin b) (piFin_mem_chartRing fm b)
    rw [hsum]
    exact sum_mem_nonunits_iff_of_forall_sub_algebraMap_mem v'.toValuationSubring spw.toValuationSubring
      v'.algebraMap_mem' spw.algebraMap_mem' c (fun i => fm.piFin (B (bb i))) (fun i => residue ↥A (α (bb i)))
      (fun i => (hv' (bb i)).2) (fun i => hspw (bb i))

  have hv'eq : v' = spw :=
    ModularCurve.CharPModel.FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff p ℓ A (ResidueField ↥A)
      (residue ↥A) fm Ideal.Quotient.mk_surjective dataAll hsep v' spw hj₁ hj₂ hagree

  rw [← hv'eq, hv'_def]
  exact ((AlgebraicCurve.Place.congrEquiv _ he).apply_symm_apply v).symm

end
end S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_finChart_centrePin
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_finChart_centrePin (solution)
