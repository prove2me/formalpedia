-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/0be420c3-c83f-5ed4-a9d2-6567ea5c2174

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
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_infChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_IgusaScheme_piInf_image_spans_chartAlg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal
p2m_attr_erase "instance" "ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal.ModularCurve ModularCurve.CharPModel P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal.ModularCurve.CharPModel AlgebraicCurve IsLocalRing ModularCurve.IgusaScheme"

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldFullC modularFunctionFieldC_le_full jqModC modularFunctionFieldC jqModC_mem CharPModel.FibreModel IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme.jInvChartInf IgusaScheme.coe_jInvChartInf IgusaScheme CharPModel.FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff IgusaScheme.piInf_image_spans_chartAlg"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar constantsHom affineBaseInf FibreModel FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff"
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
p2m_export "ModularCurve" "modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldFullC modularFunctionFieldC_le_full jqModC modularFunctionFieldC jqModC_mem CharPModel.FibreModel IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme.jInvChartInf IgusaScheme.coe_jInvChartInf IgusaScheme CharPModel.FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff IgusaScheme.piInf_image_spans_chartAlg"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar constantsHom affineBaseInf FibreModel FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff"
namespace PInfAux
p2m_open "ModularCurve.CharPModel ModularCurve"

section ValSub2

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mul_mem_nonunits_of_mem (O : ValuationSubring F) {x y : F} (hx : x ∈ O) (hy : y ∈ O.nonunits) :
    x * y ∈ O.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal] at hy ⊢
  obtain ⟨hmem, hmax⟩ := hy
  refine ⟨mul_mem hx hmem, ?_⟩
  have : (⟨x * y, mul_mem hx hmem⟩ : O) = ⟨x, hx⟩ * ⟨y, hmem⟩ := rfl
  rw [this]
  exact Ideal.mul_mem_left _ _ hmax

theorem mem_nonunits_of_ord_pos (w : AlgebraicCurve.Place K F) {x : F} (h : 0 < w.ord x) :
    x ∈ w.toValuationSubring.nonunits := by
  have hx : x ≠ 0 := by rintro rfl; simp [AlgebraicCurve.Place.ord_zero] at h
  have hmem : x ∈ w.toValuationSubring := w.mem_of_ord_nonneg hx h.le
  exact ValuationSubring.coe_mem_nonunits_iff.mpr ((w.mem_maximalIdeal_iff_ord_pos hx hmem).mpr h)
    |> fun h' => (by simpa using h')

theorem ord_sub_algebraMap_le_zero_of_inv_sub_mem_nonunits (w : AlgebraicCurve.Place K F)
    (A : ValuationSubring K) {j : F} (hj : j ≠ 0) {c : A} (hc : c ∈ IsLocalRing.maximalIdeal A)
    (hpin : j⁻¹ - algebraMap K F c ∈ w.toValuationSubring.nonunits) (a : A) :
    w.ord (j - algebraMap K F a) ≤ 0 := by
  by_contra hle
  have hlt : 0 < w.ord (j - algebraMap K F a) := not_le.mp hle
  set O := w.toValuationSubring with hO_def
  have hO : ∀ x : K, algebraMap K F x ∈ O := w.algebraMap_mem'
  have hja : j - algebraMap K F a ∈ O.nonunits := mem_nonunits_of_ord_pos w hlt
  have hjmem : j ∈ O := by
    have : j = (j - algebraMap K F a) + algebraMap K F a := by ring
    rw [this]; exact add_mem (O.nonunits_subset hja) (hO _)

  have hkey : algebraMap K F (1 - (c : K) * a) ∈ O.nonunits := by
    have hrw : algebraMap K F (1 - (c : K) * a) =
        j * (j⁻¹ - algebraMap K F c) + algebraMap K F c * (j - algebraMap K F a) := by
      rw [map_sub, map_one, map_mul, mul_sub, mul_inv_cancel₀ hj]; ring
    rw [hrw]
    exact add_mem (mul_mem_nonunits_of_mem O hjmem hpin) (mul_mem_nonunits_of_mem O (hO _) hja)
  have h1 : (1 : K) - (c : K) * a = 0 := by
    by_contra hne
    exact algebraMap_not_mem_nonunits O hO hne hkey

  apply (IsLocalRing.mem_maximalIdeal _).mp hc
  refine IsUnit.of_mul_eq_one a (Subtype.ext ?_)
  have : (c : K) * a = 1 := by linear_combination -h1
  simpa using this

end ValSub2

end ModularCurve.CharPModel.PInfAux

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldBar jq ModularPolynomialData modularFunctionFieldFull coeffEmb laurentBaseChange coeffEmb_mem_laurentBaseChange modularFunctionFieldFullC modularFunctionFieldC_le_full jqModC modularFunctionFieldC jqModC_mem CharPModel.FibreModel IgusaScheme.coe_jFull IgusaScheme.jFull_ne_zero IgusaScheme.jInvChartInf IgusaScheme.coe_jInvChartInf IgusaScheme CharPModel.FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff IgusaScheme.piInf_image_spans_chartAlg"
namespace CharPModel
p2m_export "ModularCurve.CharPModel" "jBar constantsHom affineBaseInf FibreModel FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff"
namespace PInfAux
p2m_open "ModularCurve.CharPModel ModularCurve"

section ChartRing

variable {N : ℕ} [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k ℓ] {red : ↥A →+* k}

theorem affineBaseInf_le_BInf (fm : FibreModel N A ℓ k red) : affineBaseInf N A ≤ fm.BInf := by
  refine Subring.closure_le.mpr ?_
  rintro x (⟨a, rfl⟩ | hx)
  · exact fm.constInf_mem a
  · rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact fm.jInvBar_mem

theorem piInf_mem_adjoin_of_mem_affineBaseInf (fm : FibreModel N A ℓ k red)
    {x : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)} (hx : x ∈ affineBaseInf N A) :
    (fm.piInf ⟨x, affineBaseInf_le_BInf fm hx⟩ : modularFunctionFieldC k N) ∈
      Algebra.adjoin k ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹} :
        Set (modularFunctionFieldC k N)) := by
  induction hx using Subring.closure_induction with
  | mem x hx =>
    rcases hx with ⟨a, rfl⟩ | hx
    · rw [fm.piInf_const a]
      exact Subalgebra.algebraMap_mem _ _
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      rw [fm.piInf_jInv]
      exact Algebra.subset_adjoin (Set.mem_singleton _)
  | zero =>
    rw [show (⟨0, affineBaseInf_le_BInf fm (Subring.zero_mem _)⟩ : fm.BInf) = 0 from rfl, map_zero]
    exact zero_mem _
  | one =>
    rw [show (⟨1, affineBaseInf_le_BInf fm (Subring.one_mem _)⟩ : fm.BInf) = 1 from rfl, map_one]
    exact one_mem _
  | add x y hx hy ihx ihy =>
    rw [show (⟨x + y, affineBaseInf_le_BInf fm (Subring.add_mem _ hx hy)⟩ : fm.BInf) =
      ⟨x, affineBaseInf_le_BInf fm hx⟩ + ⟨y, affineBaseInf_le_BInf fm hy⟩ from rfl, map_add]
    exact add_mem ihx ihy
  | neg x hx ih =>
    rw [show (⟨-x, affineBaseInf_le_BInf fm (Subring.neg_mem _ hx)⟩ : fm.BInf) =
      -⟨x, affineBaseInf_le_BInf fm hx⟩ from rfl, map_neg]
    exact neg_mem ih
  | mul x y hx hy ihx ihy =>
    rw [show (⟨x * y, affineBaseInf_le_BInf fm (Subring.mul_mem _ hx hy)⟩ : fm.BInf) =
      ⟨x, affineBaseInf_le_BInf fm hx⟩ * ⟨y, affineBaseInf_le_BInf fm hy⟩ from rfl, map_mul]
    exact mul_mem ihx ihy

theorem piInf_mem_chartRing (fm : FibreModel N A ℓ k red) (b : fm.BInf) :
    (fm.piInf b : modularFunctionFieldC k N) ∈
      AlgebraicCurve.CurveModel.chartRing k ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹} :
        Set (modularFunctionFieldC k N)) := by
  rw [AlgebraicCurve.CurveModel.mem_chartRing_iff]
  obtain ⟨P, hPm, hPev⟩ := fm.integralInf b
  set R := Algebra.adjoin k ({(⟨jqModC k, jqModC_mem k N⟩ : modularFunctionFieldC k N)⁻¹} :
        Set (modularFunctionFieldC k N)) with hR
  let ι : affineBaseInf N A →+* fm.BInf := Subring.inclusion (affineBaseInf_le_BInf fm)
  have hθmem : ∀ x : affineBaseInf N A, (fm.piInf.comp ι) x ∈ R := fun x =>
    piInf_mem_adjoin_of_mem_affineBaseInf fm x.2
  let θ : affineBaseInf N A →+* R := (fm.piInf.comp ι).codRestrict R hθmem
  refine ⟨P.map θ, hPm.map θ, ?_⟩
  rw [Polynomial.eval₂_map]
  have hcomp : (algebraMap R (modularFunctionFieldC k N)).comp θ = fm.piInf.comp ι := by
    ext x; rfl
  rw [hcomp, ← Polynomial.hom_eval₂]
  have h0 : Polynomial.eval₂ ι b P = 0 := by
    apply Subtype.ext
    have h := Polynomial.hom_eval₂ P ι fm.BInf.subtype b
    have hsub : fm.BInf.subtype.comp ι = (affineBaseInf N A).subtype := by ext; rfl
    rw [hsub] at h
    exact h.trans hPev
  rw [h0, map_zero]

end ChartRing

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
    (α : ↥(chartAlgInf p ℓ) →+* ↥A)
    (hpole : α (ModularCurve.IgusaScheme.jInvChartInf p ℓ) ∈ IsLocalRing.maximalIdeal ↥A)
    (hgen : ∀ b : ↥(chartAlgInf p ℓ),
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ∈ w.toValuationSubring ∧
          (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (b : ↥(modularFunctionFieldFull p)).2⟩ : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
              algebraMap (AlgebraicClosure ℚ) (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) ((A.subtype.comp α) b) ∈
            w.toValuationSubring.nonunits)
    (hsp : ∀ b : ↥(chartAlgInf p ℓ),
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) ∈
            v.toValuationSubring ∧
          (IntermediateField.inclusion (modularFunctionFieldC_le_full (ResidueField ↥A) p) (fm.piInf ⟨_, hinf b⟩) : ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) -
              algebraMap (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (((IsLocalRing.residue ↥A).comp α) b) ∈
            v.toValuationSubring.nonunits) :
    v =
      AlgebraicCurve.Place.congrRingEquiv
        (e := (IntermediateField.equivOfEq hCF).toRingEquiv)
        (he := fun a => (IntermediateField.equivOfEq hCF).commutes a)
        (fm.spPlace Ideal.Quotient.mk_surjective dataAll hsep w)
:= by
  classical

  have hjq : (jq : LaurentSeries ℚ) ≠ 0 := by
    have h := ModularCurve.IgusaScheme.jFull_ne_zero p
    rwa [Ne, ← Subtype.coe_inj, ModularCurve.IgusaScheme.coe_jFull] at h
  have hjBar : jBar p ≠ 0 := by
    intro h
    have h' := congrArg Subtype.val h
    exact (map_ne_zero (coeffEmb (AlgebraicClosure ℚ))).mpr hjq h'
  have hjinv : (⟨coeffEmb (AlgebraicClosure ℚ)
        ((ModularCurve.IgusaScheme.jInvChartInf p ℓ : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
        (ModularCurve.IgusaScheme.jInvChartInf p ℓ : ↥(modularFunctionFieldFull p)).2⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) = (jBar p)⁻¹ := by
    apply Subtype.ext
    simp [jBar, ModularCurve.IgusaScheme.coe_jInvChartInf, map_inv₀]
  have hordpole : ∀ a : ↥A, w.ord (jBar p - algebraMap (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) (a : AlgebraicClosure ℚ)) ≤ 0 := by
    intro a
    have hpin := (hgen (ModularCurve.IgusaScheme.jInvChartInf p ℓ)).2
    rw [hjinv] at hpin
    exact ord_sub_algebraMap_le_zero_of_inv_sub_mem_nonunits w A hjBar hpole hpin a

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

  let B : ↥(chartAlgInf p ℓ) → fm.BInf := fun b =>
    ⟨⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull p)) : LaurentSeries ℚ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (b : ↥(modularFunctionFieldFull p)).2⟩, hinf b⟩

  have hspw : ∀ b : ↥(chartAlgInf p ℓ), (fm.piInf (B b) : ↥(modularFunctionFieldC (ResidueField ↥A) p)) -
      algebraMap (ResidueField ↥A) _ (residue ↥A (α b)) ∈ spw.toValuationSubring.nonunits := by
    intro b
    let d : fm.BInf := B b - ⟨constantsHom p A (α b), fm.constInf_mem (α b)⟩
    have hd : (fm.piInf d : ↥(modularFunctionFieldC (ResidueField ↥A) p)) =
        fm.piInf (B b) - algebraMap (ResidueField ↥A) _ (residue ↥A (α b)) := by
      rw [map_sub, fm.piInf_const]
    rw [← hd, hspw_def]
    refine (fm.piInf_mem_spPlace_nonunits_iff Ideal.Quotient.mk_surjective dataAll hsep w hordpole d).mpr
      ⟨0, zero_mem _, ?_⟩
    have : ((d : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) : _) -
        algebraMap (AlgebraicClosure ℚ) _ ((0 : ↥A) : AlgebraicClosure ℚ) =
        (B b : laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull p)) -
          algebraMap (AlgebraicClosure ℚ) _ ((A.subtype.comp α) b) := by
      simp [d, B, constantsHom]
    rw [this]
    exact (hgen b).2

  have hv' : ∀ b : ↥(chartAlgInf p ℓ), (fm.piInf (B b) : ↥(modularFunctionFieldC (ResidueField ↥A) p)) ∈
      v'.toValuationSubring ∧ (fm.piInf (B b) : ↥(modularFunctionFieldC (ResidueField ↥A) p)) -
      algebraMap (ResidueField ↥A) _ (residue ↥A (α b)) ∈ v'.toValuationSubring.nonunits := by
    intro b
    refine ⟨(hv'mem _).mpr ?_, (hv'nu _).mpr ?_⟩
    · rw [he_incl]; exact (hsp b).1
    · rw [map_sub, he, he_incl]; exact (hsp b).2

  have hj₁ : ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) p⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) p)))⁻¹ ∈ v'.toValuationSubring := by
    have hB : B (ModularCurve.IgusaScheme.jInvChartInf p ℓ) = ⟨(jBar p)⁻¹, fm.jInvBar_mem⟩ := Subtype.ext hjinv
    rw [← fm.piInf_jInv, ← hB]
    exact (hv' _).1
  have hj₂ : ((⟨jqModC (ResidueField ↥A), jqModC_mem (ResidueField ↥A) p⟩ :
      ↥(modularFunctionFieldC (ResidueField ↥A) p)))⁻¹ ∈ spw.toValuationSubring :=
    fm.jLineInv_mem_spPlace Ideal.Quotient.mk_surjective dataAll hsep w hordpole

  have hagree : ∀ b : fm.BInf,
      ((fm.piInf b : ↥(modularFunctionFieldC (ResidueField ↥A) p)) ∈ v'.toValuationSubring.nonunits ↔
        (fm.piInf b : ↥(modularFunctionFieldC (ResidueField ↥A) p)) ∈ spw.toValuationSubring.nonunits) := by
    intro b
    obtain ⟨n, c, bb, hsum⟩ := ModularCurve.IgusaScheme.piInf_image_spans_chartAlg p ℓ hℓp A fm hinf
      (fm.piInf b) (piInf_mem_chartRing fm b)
    rw [hsum]
    exact sum_mem_nonunits_iff_of_forall_sub_algebraMap_mem v'.toValuationSubring spw.toValuationSubring
      v'.algebraMap_mem' spw.algebraMap_mem' c (fun i => fm.piInf (B (bb i))) (fun i => residue ↥A (α (bb i)))
      (fun i => (hv' (bb i)).2) (fun i => hspw (bb i))

  have hv'eq : v' = spw :=
    ModularCurve.CharPModel.FibreModel.place_eq_of_forall_infChart_mem_nonunits_iff p ℓ A (ResidueField ↥A)
      (residue ↥A) fm Ideal.Quotient.mk_surjective dataAll hsep v' spw hj₁ hj₂ hagree

  rw [← hv'eq, hv'_def]
  exact ((AlgebraicCurve.Place.congrEquiv _ he).apply_symm_apply v).symm

end
end S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_placeFullC_eq_congr_spPlace_of_infChart_centrePin_of_mem_maximalIdeal (solution)
