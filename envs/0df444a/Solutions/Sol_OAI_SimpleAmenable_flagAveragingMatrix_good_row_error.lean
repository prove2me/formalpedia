-- Prove2me | solution 1 for OAI.SimpleAmenable.flagAveragingMatrix_good_row_error
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:48:20.532798+00:00
-- url     : https://prove2.me/submissions/6ef3cbea-5d3c-41f7-a92f-ef9da096213f

import Mathlib
import Definitions.Def_OAIQ65Sa014

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_QuadraticRectangleCounts
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section QuadraticRectangleCounts
open Classical

theorem cutRectangle_card_floor (S : Finset CutRing) (x y a b : ℝ) (hb : 0<b)
    (hS : ∀u∈S,u∈cutRectangle x y a b) :
    S.card≤(⌊b*(x+a)⌋+1-⌊b*x⌋).toNat := by
  have hinj : Set.InjOn (fun u : CutRing => ⌊b*ordinary u⌋) (↑S) := by
    intro u hu w hw he
    exact conjugateStrip_floor_inj y b hb (hS u hu).2 (hS w hw).2 he
  rw [← Int.card_Icc,← Finset.card_image_of_injOn hinj]
  apply Finset.card_le_card
  intro t ht
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ht
  exact Finset.mem_Icc.mpr
    ⟨Int.floor_mono (mul_le_mul_of_nonneg_left (hS u hu).1.1 hb.le),
      Int.floor_mono (mul_le_mul_of_nonneg_left (hS u hu).1.2 hb.le)⟩

theorem cutRectangle_card_bound (S : Finset CutRing) (x y a b : ℝ)
    (ha : 0≤a) (hb : 0<b) (hS : ∀u∈S,u∈cutRectangle x y a b) :
    (S.card:ℝ)<a*b+2 := by
  have hc := cutRectangle_card_floor S x y a b hb hS
  have hle : ⌊b*x⌋≤⌊b*(x+a)⌋ := Int.floor_mono (by nlinarith)
  have hnon : 0≤⌊b*(x+a)⌋+1-⌊b*x⌋ := by omega
  have hc' : (S.card:ℤ)≤⌊b*(x+a)⌋+1-⌊b*x⌋ := by
    rw [← Int.toNat_of_nonneg hnon]
    exact_mod_cast hc
  have hc'' : (S.card:ℝ)≤(⌊b*(x+a)⌋:ℝ)+1-(⌊b*x⌋:ℝ) := by exact_mod_cast hc'
  have h₁ := Int.floor_le (b*(x+a))
  have h₂ := Int.lt_floor_add_one (b*x)
  nlinarith

end QuadraticRectangleCounts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_QuadraticTiles
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section QuadraticTiles
open Classical Module MeasureTheory
open scoped QuadraticAlgebra

theorem cutTau_sub_one_isUnit : IsUnit (cutTau-1) := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  norm_num [cutTau,QuadraticAlgebra.norm_def]

theorem balanced_cutUnit {L : ℝ} (hL : 1≤L) :
    ∃u : CutRing,IsUnit u ∧ |ordinary u| ≤ 2/L ∧ |conjugate u| ≤ L := by
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hL Real.one_lt_goldenRatio
  let u : CutRing := (cutTau-1)^k
  have hp : 0<Real.goldenRatio^k := pow_pos Real.goldenRatio_pos _
  have ho : ordinary u=(Real.goldenRatio^k)⁻¹ := by
    simp only [u,map_pow,map_sub,ordinary_cutTau,map_one]
    rw [← inv_pow]
    congr 1
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hc : |conjugate u|=Real.goldenRatio^k := by
    simp only [u,map_pow,map_sub,conjugate_cutTau,map_one,abs_pow]
    congr 1
    rw [abs_of_neg (by linarith [Real.goldenConj_neg] : Real.goldenConj-1<0)]
    linarith [Real.goldenRatio_add_goldenConj]
  refine ⟨u,cutTau_sub_one_isUnit.pow k,?_,by simpa only [hc] using hk⟩
  rw [ho,abs_of_pos (inv_pos.mpr hp)]
  have hL₀ : 0<L := lt_of_lt_of_le zero_lt_one hL
  apply (le_div_iff₀ hL₀).mpr
  have hh : L<2*Real.goldenRatio^k := by
    rw [pow_succ] at hk'
    nlinarith [Real.goldenRatio_lt_two]
  have he := mul_le_mul_of_nonneg_left hh.le (inv_nonneg.mpr hp.le)
  have hh' : (Real.goldenRatio^k)⁻¹*(2*Real.goldenRatio^k)=2 := by field_simp
  rw [hh'] at he
  exact he

theorem quadraticScaledBasis_volume {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    volume.real (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht))=
      Real.sqrt 5/(d^2*s*t) := by
  rw [ZSpan.volume_real_fundamentalDomain]
  have he : Matrix.of (quadraticScaledBasis hu hd hs ht)=
      (quadraticScaledMatrix u d s t).transpose := by
    ext i j
    exact quadraticScaledBasis_apply hu hd hs ht i j
  rw [he,Matrix.det_transpose,quadraticScaledMatrix_det,abs_div,abs_mul,cutUnit_abs_norm hu,
    one_mul,abs_of_pos (by positivity : 0<d^2*s*t)]
  congr 1
  rw [abs_of_neg (by linarith [Real.goldenRatio_pos,Real.goldenConj_neg])]
  linarith [Real.goldenRatio_sub_goldenConj]

theorem quadraticScaledTile_bound {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t)
    (x : Fin 2 → ℝ) (hx : x∈ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) :
    |x 0| ≤ 3*|ordinary u|/(d*s) ∧ |x 1| ≤ 2*|conjugate u|/(d*t) := by
  let b := quadraticScaledBasis hu hd hs ht
  have hcoeff := (ZSpan.mem_fundamentalDomain b).mp hx
  have hx' : x=(b.repr x 0) • b 0+(b.repr x 1) • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  have hg : |Real.goldenRatio| ≤ 2 := by
    rw [abs_of_pos Real.goldenRatio_pos]; exact Real.goldenRatio_lt_two.le
  have hg' : |Real.goldenConj| ≤ 1 := by
    rw [abs_of_neg Real.goldenConj_neg]; linarith [Real.neg_one_lt_goldenConj]
  have hc (i : Fin 2) : |b.repr x i|≤1 := by
    rw [abs_of_nonneg (hcoeff i).1]; exact (hcoeff i).2.le
  have hcalc (a q c₀ c₁ R k : ℝ) (hR : 0<R) (hq : |q|≤k)
      (hc₀ : |c₀|≤1) (hc₁ : |c₁|≤1) :
      |c₀*(a/R)+c₁*(a*q/R)| ≤ (1+k)*|a|/R := by
    calc
      _ ≤ |c₀*(a/R)|+|c₁*(a*q/R)| := abs_add_le _ _
      _ = |c₀| *(|a|/R)+|c₁| *(|a| *|q|/R) := by
        simp only [abs_mul,abs_div,abs_of_pos hR]
      _ ≤ 1*(|a|/R)+1*(|a| *k/R) := by gcongr
      _ = _ := by ring
  rw [congrFun hx' 0,congrFun hx' 1]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change |(b.repr x 0)*b 0 0+(b.repr x 1)*b 1 0| ≤ _ ∧
    |(b.repr x 0)*b 0 1+(b.repr x 1)*b 1 1| ≤ _
  simp only [b,quadraticScaledBasis_apply,quadraticScaledMatrix,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · simpa only [show (1:ℝ)+2=3 by norm_num] using
      hcalc (ordinary u) Real.goldenRatio (b.repr x 0) (b.repr x 1) (d*s) 2 (mul_pos hd hs) hg (hc 0) (hc 1)
  · simpa only [show (1:ℝ)+1=2 by norm_num] using
      hcalc (conjugate u) Real.goldenConj (b.repr x 0) (b.repr x 1) (d*t) 1 (mul_pos hd ht) hg' (hc 0) (hc 1)

end QuadraticTiles

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_LatticeRiemann
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section LatticeRiemann
open Classical MeasureTheory

theorem fundamentalDomain_riemann_error
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasureSpace E] [BorelSpace E] [Measure.IsAddLeftInvariant (volume : Measure E)]
    (L : AddSubgroup E) [Countable L]
    {F : Set E} (hF : IsAddFundamentalDomain L F volume)
    (hFfin : volume F<⊤) {δ : ℝ} (hδ : ∀x∈F,‖x‖≤δ)
    {f : E → ℝ} (hf : Integrable f) {A : NNReal} (hlip : LipschitzWith A f)
    (T : Finset L) (hT : ∀z : L,z∉T → ∀x∈F,f ((z:E)+x)=0) :
    |volume.real F*(∑z∈T,f (z:E))-∫x,f x| ≤
      (T.card:ℝ)*((A:ℝ)*δ*volume.real F) := by
  have hint (z : L) : Integrable (fun x : E => f ((z:E)+x)) :=
    (measurePreserving_add_left volume (z:E)).integrable_comp_of_integrable hf
  have hdecomp : (∫x,f x)=∑z∈T,∫x in F,f ((z:E)+x) := by
    rw [hF.integral_eq_tsum'' f hf]
    apply tsum_eq_sum
    intro z hz
    apply integral_eq_zero_of_ae
    exact (ae_restrict_mem₀ hF.nullMeasurableSet).mono (fun x hx => hT z hz x hx)
  rw [hdecomp,Finset.mul_sum,← Finset.sum_sub_distrib]
  have he (z : L) : volume.real F*f (z:E)-(∫x in F,f ((z:E)+x))=
      ∫x in F,f (z:E)-f ((z:E)+x) := by
    rw [integral_sub (integrableOn_const (C := f (z:E)) hFfin.ne) (hint z).integrableOn,
      setIntegral_const,smul_eq_mul]
  simp_rw [he]
  calc
    _ ≤ ∑z∈T,|∫x in F,f (z:E)-f ((z:E)+x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑_z∈T,(A:ℝ)*δ*volume.real F := by
      apply Finset.sum_le_sum
      intro z _
      rw [← Real.norm_eq_abs]
      apply norm_setIntegral_le_of_norm_le_const hFfin
      intro x hx
      calc
        _ ≤ (A:ℝ)*‖(z:E)-((z:E)+x)‖ := hlip.norm_sub_le _ _
        _ = (A:ℝ)*‖x‖ := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hδ x hx) A.coe_nonneg
    _ = _ := by simp

end LatticeRiemann

section PairedQuadraticTiles
open Classical Module MeasureTheory

theorem balanced_cutUnit_pos {L : ℝ} (hL : 0<L) :
    ∃u : CutRing,IsUnit u ∧ |ordinary u| ≤ 2/L ∧ |conjugate u| ≤ 2*L := by
  by_cases hh : 1≤L
  · obtain ⟨u,hu,ho,hc⟩ := balanced_cutUnit hh
    exact ⟨u,hu,ho,hc.trans (by linarith)⟩
  · have hLi : 1≤L⁻¹ := (one_le_inv₀ hL).mpr (le_of_not_ge hh)
    obtain ⟨u,hu,ho,hc⟩ := balanced_cutUnit hLi
    obtain ⟨U,rfl⟩ := hu
    have heo : |ordinary (↑(U⁻¹):CutRing)| * |ordinary (↑U:CutRing)|=1 := by
      rw [← abs_mul,← map_mul]; simp
    have hec : |conjugate (↑(U⁻¹):CutRing)| * |conjugate (↑U:CutRing)|=1 := by
      rw [← abs_mul,← map_mul]; simp
    have hn := cutUnit_abs_norm U.isUnit
    rw [abs_mul] at hn
    have ho₀ : 0 < |ordinary (↑U:CutRing)| := by
      exact lt_of_le_of_ne (abs_nonneg _) (by intro hh; rw [← hh,zero_mul] at hn; norm_num at hn)
    have hc₀ : 0 < |conjugate (↑U:CutRing)| := by
      exact lt_of_le_of_ne (abs_nonneg _) (by intro hh; rw [← hh,mul_zero] at hn; norm_num at hn)
    refine ⟨(↑(U⁻¹):CutRing),(U⁻¹).isUnit,?_,?_⟩
    · have he : |ordinary (↑(U⁻¹):CutRing)|=|conjugate (↑U:CutRing)| := by nlinarith
      rw [he]
      exact hc.trans (by rw [div_eq_mul_inv]; have := inv_pos.mpr hL; linarith)
    · have he : |conjugate (↑(U⁻¹):CutRing)|=|ordinary (↑U:CutRing)| := by nlinarith
      rw [he]
      simpa only [div_inv_eq_mul] using ho

theorem quadraticSmallTile {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    ∃u : CutRing,∃hu : IsUnit u,∀x∈ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht),
      ‖x‖ ≤ 6/(d*Real.sqrt (s*t)) := by
  let L := Real.sqrt (t/s)
  have hL : 0<L := Real.sqrt_pos.2 (div_pos ht hs)
  obtain ⟨u,hu,ho,hc⟩ := balanced_cutUnit_pos hL
  have hsq : L^2=t/s := Real.sq_sqrt (div_nonneg ht.le hs.le)
  have hsq' : L^2*s=t := (eq_div_iff hs.ne').mp hsq
  have hmul : L*s=Real.sqrt (s*t) := by
    have he : (L*s)^2=s*t := by nlinarith
    nlinarith [Real.sq_sqrt (mul_pos hs ht).le,Real.sqrt_nonneg (s*t),mul_pos hL hs]
  have hdiv : L/t=(Real.sqrt (s*t))⁻¹ := by
    rw [← hmul]
    apply (div_eq_iff ht.ne').mpr
    field_simp
    nlinarith [hsq']
  refine ⟨u,hu,fun x hx => ?_⟩
  have hb := quadraticScaledTile_bound hu hd hs ht x hx
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  fin_cases i
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ 3*|ordinary u|/(d*s) := hb.1
      _ ≤ 3*(2/L)/(d*s) := by gcongr
      _ = 6/(d*Real.sqrt (s*t)) := by rw [← hmul]; field_simp; ring
  · rw [Real.norm_eq_abs]
    calc
      _ ≤ 2*|conjugate u|/(d*t) := hb.2
      _ ≤ 2*(2*L)/(d*t) := by gcongr
      _ = 4/(d*Real.sqrt (s*t)) := by
        calc
          _ = (4/d)*(L/t) := by ring
          _ = _ := by rw [hdiv]; ring
      _ ≤ _ := by gcongr; norm_num

theorem pairedQuadraticDomain {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    ZSpan.fundamentalDomain (pairedQuadraticBasis hu hd hs ht)=
      (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) ×ˢ
      (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) := by
  ext x
  simp only [ZSpan.mem_fundamentalDomain,pairedQuadraticBasis,Sum.forall,
    Basis.prod_repr_inl,Basis.prod_repr_inr,Set.mem_prod]

theorem pairedQuadratic_volume {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) :
    volume.real (ZSpan.fundamentalDomain (pairedQuadraticBasis hu hd hs ht))=
      5/(d^4*s^2*t^2) := by
  rw [pairedQuadraticDomain,Measure.real_def]
  change ((volume.prod volume) ((ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) ×ˢ
    (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)))).toReal = _
  rw [Measure.prod_prod,ENNReal.toReal_mul,← Measure.real_def,
    quadraticScaledBasis_volume hu hd hs ht]
  have hh : (Real.sqrt 5)^2=5 := Real.sq_sqrt (by norm_num)
  rw [← sq]
  field_simp
  nlinarith

end PairedQuadraticTiles

section PairedLatticeRiemann
open Classical Module MeasureTheory

theorem pairedQuadraticBox_rectangles {d s t R : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) (z : CutRing×CutRing) (hz : z∈pairedQuadraticBox d s t R q) :
    z.1∈cutRectangle ((-R-q.1 0)*(d*s)) ((-R-q.1 1)*(d*t)) (2*R*(d*s)) (2*R*(d*t)) ∧
    z.2∈cutRectangle ((-R-q.2 0)*(d*s)) ((-R-q.2 1)*(d*t)) (2*R*(d*s)) (2*R*(d*t)) := by
  have hnorm := norm_prod_le_iff.mp hz
  have hr : 0≤R := (norm_nonneg _).trans hz
  have hb (u : CutRing) (p : Fin 2 → ℝ) (hh : ‖p+quadraticScaledEmbedding d s t u‖≤R) :
      u∈cutRectangle ((-R-p 0)*(d*s)) ((-R-p 1)*(d*t)) (2*R*(d*s)) (2*R*(d*t)) := by
    have hj := (pi_norm_le_iff_of_nonneg hr).mp hh
    have h₀ := abs_le.mp (hj 0)
    have h₁ := abs_le.mp (hj 1)
    change -R≤p 0+ordinary u/(d*s) ∧ p 0+ordinary u/(d*s)≤R at h₀
    change -R≤p 1+conjugate u/(d*t) ∧ p 1+conjugate u/(d*t)≤R at h₁
    have ho : (-R-p 0)≤ordinary u/(d*s) ∧ ordinary u/(d*s)≤R-p 0 := by constructor <;> linarith
    have hc : (-R-p 1) ≤ conjugate u/(d*t) ∧ conjugate u/(d*t)≤R-p 1 := by constructor <;> linarith
    rw [le_div_iff₀ (mul_pos hd hs),div_le_iff₀ (mul_pos hd hs)] at ho
    rw [le_div_iff₀ (mul_pos hd ht),div_le_iff₀ (mul_pos hd ht)] at hc
    exact ⟨⟨ho.1,by nlinarith [ho.2]⟩,⟨hc.1,by nlinarith [hc.2]⟩⟩
  exact ⟨hb z.1 q.1 hnorm.1,hb z.2 q.2 hnorm.2⟩

theorem pairedQuadraticBox_finite {d s t R : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) (hR : 0<R)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) : (pairedQuadraticBox d s t R q).Finite := by
  have h₁ := cutRectangle_finite ((-R-q.1 0)*(d*s)) ((-R-q.1 1)*(d*t))
    (2*R*(d*s)) (2*R*(d*t)) (by positivity)
  have h₂ := cutRectangle_finite ((-R-q.2 0)*(d*s)) ((-R-q.2 1)*(d*t))
    (2*R*(d*s)) (2*R*(d*t)) (by positivity)
  exact (h₁.prod h₂).subset (fun z hz => pairedQuadraticBox_rectangles hd hs ht q z hz)

theorem pairedQuadraticBox_card {d s t R : ℝ} (hd : 0<d) (hs : 0 < s) (ht : 0<t) (hR : 0<R)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) (S : Finset (CutRing×CutRing))
    (hS : ∀z∈S,z∈pairedQuadraticBox d s t R q) :
    (S.card:ℝ) ≤ (4*R^2*d^2*s*t+2)^2 := by
  let S₁ := S.image Prod.fst
  let S₂ := S.image Prod.snd
  have hsub : S⊆S₁×ˢS₂ := by
    intro z hz
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨z,hz,rfl⟩,
      Finset.mem_image.mpr ⟨z,hz,rfl⟩⟩
  have hc₁ : (S₁.card:ℝ)<4*R^2*d^2*s*t+2 := by
    have hh := cutRectangle_card_bound S₁ ((-R-q.1 0)*(d*s)) ((-R-q.1 1)*(d*t))
      (2*R*(d*s)) (2*R*(d*t)) (by positivity) (by positivity) (by
        intro u hu
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
        exact (pairedQuadraticBox_rectangles hd hs ht q z (hS z hz)).1)
    nlinarith
  have hc₂ : (S₂.card:ℝ)<4*R^2*d^2*s*t+2 := by
    have hh := cutRectangle_card_bound S₂ ((-R-q.2 0)*(d*s)) ((-R-q.2 1)*(d*t))
      (2*R*(d*s)) (2*R*(d*t)) (by positivity) (by positivity) (by
        intro u hu
        obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hu
        exact (pairedQuadraticBox_rectangles hd hs ht q z (hS z hz)).2)
    nlinarith
  have hcard : (S.card:ℝ)≤(S₁.card:ℝ)*(S₂.card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans_eq (Finset.card_product S₁ S₂)
  exact hcard.trans (by nlinarith [Nat.cast_nonneg (α:=ℝ) S₁.card,Nat.cast_nonneg (α:=ℝ) S₂.card])

end PairedLatticeRiemann

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_UniformLatticeRiemann
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.SimpleAmenable.instCountableCutRing _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformLatticeRiemann
open Classical Module MeasureTheory

theorem pairedQuadratic_riemann_uniform {d s t K : ℝ} (hd : 1≤d)
    (hs : 0 < s) (ht : 0<t) (hst : 36≤ s*t) (hK : 0≤K)
    {f : ((Fin 2 → ℝ)×(Fin 2 → ℝ)) → ℝ} (hf : Integrable f)
    {A : NNReal} (hLip : LipschitzWith A f) (hzero : ∀x,K< ‖x‖ → f x=0)
    (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) :
    ∃S : Finset (CutRing×CutRing),
      (∀z,z∉S → f (q+pairedQuadraticEmbedding d s t z)=0) ∧
      |(5/(d^4*s^2*t^2))*(∑z∈S,f (q+pairedQuadraticEmbedding d s t z))-∫x,f x| ≤
        (5*(4*(K+1)^2+2)^2*(A:ℝ))*(6/(d*Real.sqrt (s*t))) := by
  let : (volume : Measure ((Fin 2 → ℝ)×(Fin 2 → ℝ))).IsAddLeftInvariant :=
    ⟨fun q => ((measurePreserving_add_left volume q.1).prod
      (measurePreserving_add_left volume q.2)).map_eq⟩
  have hd₀ : 0<d := lt_of_lt_of_le zero_lt_one hd
  let δ := 6/(d*Real.sqrt (s*t))
  have hroot : 6≤Real.sqrt (s*t) := by
    have hh := Real.sq_sqrt (mul_pos hs ht).le
    nlinarith [Real.sqrt_nonneg (s*t)]
  have hδ₀ : 0<δ := by dsimp [δ]; positivity
  have hδ₁ : δ≤1 := by
    apply (div_le_one (mul_pos hd₀ (Real.sqrt_pos.mpr (mul_pos hs ht)))).mpr
    nlinarith
  obtain ⟨u,hu,hcell⟩ := quadraticSmallTile hd₀ hs ht
  let b := pairedQuadraticBasis hu hd₀ hs ht
  let F := ZSpan.fundamentalDomain b
  let L := Submodule.span ℤ (Set.range b)
  let e := pairedLatticeEquiv hu hd₀ hs ht
  let S := (pairedQuadraticBox_finite hd₀ hs ht (show 0<K+δ by linarith) q).toFinset
  let : Countable CutRing := (QuadraticAlgebra.equivProd (1 : ℤ) 1).injective.countable
  let : Countable L.toAddSubgroup := e.symm.injective.countable
  let T : Finset L := S.image e
  have hF : IsAddFundamentalDomain L.toAddSubgroup F volume := ZSpan.isAddFundamentalDomain b volume
  have hFfinite : volume F<⊤ := (ZSpan.fundamentalDomain_isBounded b).measure_lt_top
  have hcell' : ∀x∈F,‖x‖≤δ := by
    intro x hx
    change x∈ZSpan.fundamentalDomain (pairedQuadraticBasis hu hd₀ hs ht) at hx
    rw [pairedQuadraticDomain] at hx
    exact norm_prod_le_iff.mpr ⟨hcell x.1 hx.1,hcell x.2 hx.2⟩
  have houtside (z : CutRing×CutRing) (hz : z∉S) : K+δ< ‖q+pairedQuadraticEmbedding d s t z‖ := by
    have hn : ¬z∈pairedQuadraticBox d s t (K+δ) q := by
      simpa only [S,Set.Finite.mem_toFinset] using hz
    exact lt_of_not_ge hn
  have hsupport : ∀z,z∉S → f (q+pairedQuadraticEmbedding d s t z)=0 := by
    intro z hz
    exact hzero _ (by linarith [houtside z hz])
  have hT : ∀z : L,z∉T → ∀x∈F,f (q+((z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))+x))=0 := by
    intro z hz x hx
    have hz' : e.symm z∉S := by
      intro hh
      apply hz
      exact Finset.mem_image.mpr ⟨e.symm z,hh,e.apply_symm_apply z⟩
    have hbig := houtside (e.symm z) hz'
    have he : pairedQuadraticEmbedding d s t (e.symm z)=(z:((Fin 2 → ℝ)×(Fin 2 → ℝ))) := by
      change (e (e.symm z) : ((Fin 2 → ℝ)×(Fin 2 → ℝ)))=_
      rw [e.apply_symm_apply]
    rw [he] at hbig
    apply hzero
    have hnorm : ‖q+(z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))‖ ≤
        ‖q+((z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))+x)‖+‖x‖ := by
      have hh := norm_sub_le (q+((z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))+x)) x
      simpa only [← add_assoc,add_sub_cancel_right] using hh
    have hh := hcell' x hx
    linarith
  have hft : Integrable (fun x => f (q+x)) :=
    (measurePreserving_add_left volume q).integrable_comp_of_integrable hf
  have hlipt : LipschitzWith A (fun x => f (q+x)) := by
    simpa only [mul_one,Function.comp_def] using hLip.comp (isometry_add_left q).lipschitz
  have herr := fundamentalDomain_riemann_error L.toAddSubgroup hF hFfinite hcell' hft hlipt T hT
  have hsum : (∑z∈T,f (q+(z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))))=
      ∑z∈S,f (q+pairedQuadraticEmbedding d s t z) := by
    rw [Finset.sum_image (fun z _ w _ hh => e.injective hh)]
    rfl
  have hvol : volume.real F=5/(d^4*s^2*t^2) := pairedQuadratic_volume hu hd₀ hs ht
  change |volume.real F*(∑z∈T,f (q+(z:((Fin 2 → ℝ)×(Fin 2 → ℝ)))))-∫x,f (q+x)| ≤
    (T.card:ℝ)*((A:ℝ)*δ*volume.real F) at herr
  rw [hsum,integral_add_left_eq_self,hvol] at herr
  have hcard : T.card=S.card := Finset.card_image_of_injective _ e.injective
  rw [hcard] at herr
  have hSbox : ∀z∈S,z∈pairedQuadraticBox d s t (K+δ) q := by simp only [S,Set.Finite.mem_toFinset]; tauto
  have hcardbound := pairedQuadraticBox_card hd₀ hs ht (show 0<K+δ by linarith) q S hSbox
  have hH : 1≤d^2*s*t := by
    have hh : 1≤d^2 := by nlinarith
    have hst₁ : 1≤ s*t := by linarith
    nlinarith
  have hinside : 4*(K+δ)^2*d^2*s*t+2 ≤ (4*(K+1)^2+2)*(d^2*s*t) := by
    have he : (K+δ)^2≤(K+1)^2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_right he (show 0≤d^2*s*t by positivity)
    nlinarith
  have hcard₁ : (S.card:ℝ) ≤ ((4*(K+1)^2+2)*(d^2*s*t))^2 :=
    hcardbound.trans (by gcongr)
  have hcv : (S.card:ℝ)*(5/(d^4*s^2*t^2)) ≤ 5*(4*(K+1)^2+2)^2 := by
    calc
      _ ≤ ((4*(K+1)^2+2)*(d^2*s*t))^2*(5/(d^4*s^2*t^2)) := by gcongr
      _ = _ := by field_simp
  refine ⟨S,hsupport,herr.trans ?_⟩
  calc
    _ = ((S.card:ℝ)*(5/(d^4*s^2*t^2)))*((A:ℝ)*δ) := by ring
    _ ≤ (5*(4*(K+1)^2+2)^2)*((A:ℝ)*δ) := mul_le_mul_of_nonneg_right hcv (by positivity)
    _ = _ := by ring

end UniformLatticeRiemann

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_WindowRectangles
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section CellLineIntersections

theorem linear_form_dist_bound (A B : ℝ) (x y : ℝ × ℝ) :
    |(A*x.1+B*x.2)-(A*y.1+B*y.2)| ≤ (|A|+|B|)*dist x y := by
  have hx : |x.1-y.1| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_left _ _
  have hy : |x.2-y.2| ≤ dist x y := by
    rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
    exact le_max_right _ _
  calc
    _ = |A*(x.1-y.1)+B*(x.2-y.2)| := by congr 1; ring
    _ ≤ |A*(x.1-y.1)|+|B*(x.2-y.2)| := abs_add_le _ _
    _ ≤ |A| *dist x y+|B| *dist x y := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hx (abs_nonneg _))
        (mul_le_mul_of_nonneg_left hy (abs_nonneg _))
    _ = _ := by ring

end CellLineIntersections

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FinePatchAtlas
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.instFGCutRing _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FarGridActions

theorem cutForm_dist_bound (a : ℕ) (j : Fin 4) (x y : ℝ × ℝ) :
    |cutForm a j x-cutForm a j y| ≤ (1+|ordinary (cutTau^a)|)*dist x y := by
  have hc : 0 ≤ |ordinary (cutTau^a)| *dist x y := mul_nonneg (abs_nonneg _) dist_nonneg
  have hslope : ordinary (cutTau^a)=Real.goldenRatio^a := by simp
  fin_cases j
  · have h := linear_form_dist_bound 1 0 x y
    simp only [one_mul,zero_mul,add_zero,abs_one,abs_zero] at h
    change |x.1-y.1| ≤ _
    nlinarith
  · have h := linear_form_dist_bound 0 1 x y
    simp only [one_mul,zero_mul,zero_add,abs_one,abs_zero] at h
    change |x.2-y.2| ≤ _
    nlinarith
  · have h := linear_form_dist_bound (-Real.goldenRatio^a) 1 x y
    change |(x.2-Real.goldenRatio^a*x.1)-(y.2-Real.goldenRatio^a*y.1)| ≤ _
    simpa only [one_mul,neg_mul,sub_eq_add_neg,abs_neg,abs_one,hslope,add_comm] using h
  · have h := linear_form_dist_bound 1 (-Real.goldenRatio^a) x y
    change |(x.1-Real.goldenRatio^a*x.2)-(y.1-Real.goldenRatio^a*y.2)| ≤ _
    simpa only [one_mul,neg_mul,sub_eq_add_neg,abs_neg,abs_one,hslope] using h

end FarGridActions

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagGerms
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagGerms
open Classical

theorem flagMem_halfPlane {a : ℕ} {v : ℝ×ℝ} (j : Fin 4) (c : CutRing)
    (z : SquareFlag a v) :
    flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
      (if cutForm a j z.val=ordinary c then cutForm a j v<0
        else cutForm a j z.val<ordinary c) := by
  let U : polygonAlgebra a := ⟨halfPlane a j c,halfPlane_mem a j c⟩
  have hg : flagValue (fun p => decide (p∈U.val))
      (polygon_hasSquareArrangement U.property) z =
      decide (if cutForm a j z.val=ordinary c then cutForm a j v<0
        else cutForm a j z.val<ordinary c) := by
    apply flagValue_eq
    refine ⟨arrangementNeighborhood a {(j,c)} z.val,
      arrangementNeighborhood_open a {(j,c)} z.val,
      self_mem_arrangementNeighborhood a {(j,c)} z.val, fun p hp hpv => ?_⟩
    exact planeSign_neighborhood (p:=⟨p.val,p.property.2.2⟩) hp hpv (Finset.mem_singleton_self _)
  change flagValue _ _ z=true ↔ _
  rw [hg]
  simp

end FlagGerms

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSeparatingLevels
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagSeparatingLevels
open Classical

theorem flagSeparates_ordinary_bound {a : ℕ} {v : ℝ×ℝ} {j : Fin 4} {c : CutRing}
    {z w : SquareFlag a v} (h : FlagSeparates j c z w) :
    ordinary c ∈ Set.Icc (min (cutForm a j z.val) (cutForm a j w.val))
      (max (cutForm a j z.val) (cutForm a j w.val)) := by
  unfold FlagSeparates at h
  simp only [flagMem_halfPlane] at h
  constructor
  · by_contra hn
    have hz : ordinary c < cutForm a j z.val := lt_of_lt_of_le (lt_of_not_ge hn) (min_le_left _ _)
    have hw : ordinary c < cutForm a j w.val := lt_of_lt_of_le (lt_of_not_ge hn) (min_le_right _ _)
    simp [ne_of_gt hz,ne_of_gt hw,not_lt_of_ge hz.le,not_lt_of_ge hw.le] at h
  · by_contra hn
    have hz : cutForm a j z.val < ordinary c := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hn)
    have hw : cutForm a j w.val < ordinary c := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hn)
    simp [ne_of_lt hz,ne_of_lt hw,hz,hw] at h

end FlagSeparatingLevels

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSites
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagSites
open Classical

theorem scaledOrdinary_injective {D : ℕ} (hD : 0<D) :
    Function.Injective (scaledOrdinary D) := by
  intro u w h
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  apply Prod.ext
  · exact ordinary_injective ((div_left_inj' hD').mp (congrArg Prod.fst h))
  · exact ordinary_injective ((div_left_inj' hD').mp (congrArg Prod.snd h))

end FlagSites

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_TentMatrixPositivity
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement

section FlagSeparatorMatrices
open Classical MeasureTheory

theorem flagChamber_eq_iff {a : ℕ} {v : ℝ×ℝ} (t : Fin 4 → ℝ)
    (z w : SquareFlag a v) : flagChamber t z=flagChamber t w ↔
    ∀j c,|conjugate c|≤t j →
      (flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ z ↔
       flagMem ⟨halfPlane a j c,halfPlane_mem a j c⟩ w) := by
  constructor
  · intro he j c hc
    have h := congrFun he (j,c)
    simpa only [flagChamber,hc,ite_true,decide_eq_decide] using h
  · intro h
    funext l
    simp only [flagChamber]
    split_ifs with hl
    · exact propext (h l.1 l.2 hl) ▸ rfl
    · rfl

theorem measurableSet_flagChamber_eq {a : ℕ} {v : ℝ×ℝ} (z w : SquareFlag a v) :
    MeasurableSet {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w} := by
  have he : {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w}=
      ⋂l : Fin 4 × CutRing, {t | flagChamber t z l=flagChamber t w l} := by
    ext t
    simp only [Set.mem_ofPred_eq,Set.mem_iInter]
    exact funext_iff
  rw [he]
  apply MeasurableSet.iInter
  intro l
  by_cases hz : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ z <;>
    by_cases hw : flagMem ⟨halfPlane a l.1 l.2,halfPlane_mem a l.1 l.2⟩ w
  · simp only [flagChamber,hz,hw,decide_true,Set.ofPred_true]
    exact MeasurableSet.univ
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simpa [flagChamber,hz,hw] using
      (measurableSet_lt (measurable_pi_apply l.1) (measurable_const (a := |conjugate l.2|)) :
        MeasurableSet {t : Fin 4 → ℝ | t l.1 < |conjugate l.2|})
  · simp only [flagChamber,hz,hw,decide_false,ite_self,Set.ofPred_true]
    exact MeasurableSet.univ

theorem separatorMatrix_eq_measure {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) (z w : SquareFlag a v) :
    separatorMatrix μ z w=μ.real {t|flagChamber t z=flagChamber t w} :=
  integral_indicator_one (measurableSet_flagChamber_eq z w)

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_UniformThresholdCDF
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.PrimitiveGerm.instFiniteIndex _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section UniformThresholdCDF
open Classical MeasureTheory ProbabilityTheory

theorem unit_product_sub_bound {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    (hf : ∀i∈S,0 ≤ f i ∧ f i ≤ 1) (hg : ∀i∈S,0 ≤ g i ∧ g i ≤ 1) :
    |(∏i∈S,f i)-(∏i∈S,g i)| ≤ ∑i∈S,|f i-g i| := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hfS (j) (hj : j∈S) := hf j (Finset.mem_insert_of_mem hj)
    have hgS (j) (hj : j∈S) := hg j (Finset.mem_insert_of_mem hj)
    have hfi := hf i (Finset.mem_insert_self _ _)
    have hgi := hg i (Finset.mem_insert_self _ _)
    have hp₀ : 0 ≤ ∏j∈S,g j := Finset.prod_nonneg (fun j hj => (hgS j hj).1)
    have hp₁ : (∏j∈S,g j) ≤ 1 := Finset.prod_le_one (fun j hj => (hgS j hj).1) (fun j hj => (hgS j hj).2)
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    calc
      _ = |f i*((∏j∈S,f j)-(∏j∈S,g j))+(f i-g i)*(∏j∈S,g j)| := by congr 1; ring
      _ ≤ |f i*((∏j∈S,f j)-(∏j∈S,g j))|+|(f i-g i)*(∏j∈S,g j)| := abs_add_le _ _
      _ ≤ |(∏j∈S,f j)-(∏j∈S,g j)|+|f i-g i| := by
        rw [abs_mul,abs_mul,abs_of_nonneg hfi.1,abs_of_nonneg hp₀]
        exact add_le_add (mul_le_of_le_one_left (abs_nonneg _) hfi.2)
          (mul_le_of_le_one_right (abs_nonneg _) hp₁)
      _ ≤ _ := by linarith [ih hfS hgS]

end UniformThresholdCDF

section SeparatorCovariance
open Classical MeasureTheory ProbabilityTheory

theorem uniformInterval_isProbability {lo hi : ℝ} (h : lo < hi) :
    IsProbabilityMeasure (cond volume (Set.Icc lo hi)) :=
  cond_isProbabilityMeasure_of_finite
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr h))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)

theorem separatorMatrix_product {a : ℕ} {v : ℝ×ℝ}
    {s κ : ℝ} (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v) :
    separatorMatrix (thresholdLaw s κ) z w = ∏j,directionNoCutProbability s κ j z w := by
  have h : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have := uniformInterval_isProbability h
  have he : {t : Fin 4 → ℝ | flagChamber t z=flagChamber t w}=
      Set.univ.pi (fun j => directionNoCut j z w) := by
    ext t
    rw [Set.mem_ofPred_eq,flagChamber_eq_iff]
    simp only [Set.mem_pi,Set.mem_univ,forall_true_left,directionNoCut,Set.mem_ofPred_eq,
      FlagSeparates,not_not]
  rw [separatorMatrix_eq_measure,measureReal_def,he]
  change (Measure.pi (fun _ : Fin 4 => cond volume (Set.Icc (κ/s) (2*κ/s)))
    (Set.univ.pi (fun j => directionNoCut j z w))).toReal = _
  rw [Measure.pi_pi,ENNReal.toReal_prod]
  rfl

end SeparatorCovariance

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_GoodRowSeparators
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section GoodRowSeparators
open Classical MeasureTheory ProbabilityTheory

theorem flagSeparates_near_row {a : ℕ} {v : ℝ×ℝ} {j : Fin 4} {c : CutRing}
    {z w : SquareFlag a v} (h : FlagSeparates j c z w) :
    |cutForm a j z.val-ordinary c| ≤ (1+|ordinary (cutTau^a)|)*dist z.val w.val := by
  have hc := flagSeparates_ordinary_bound h
  have hb := abs_le.mp (cutForm_dist_bound a j z.val w.val)
  rcases le_total (cutForm a j z.val) (cutForm a j w.val) with hh|hh
  · rw [min_eq_left hh,max_eq_right hh] at hc
    exact abs_le.mpr ⟨by linarith [hc.1,hc.2],by linarith [hc.1,hc.2]⟩
  · rw [min_eq_right hh,max_eq_left hh] at hc
    exact abs_le.mpr ⟨by linarith [hc.1,hc.2],by linarith [hc.1,hc.2]⟩

theorem directionNoCutProbability_eq_one {a : ℕ} {v : ℝ×ℝ} {s κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (j : Fin 4) (z w : SquareFlag a v)
    (h : ∀c, |conjugate c| ≤ 2*κ/s → ¬ FlagSeparates j c z w) :
    directionNoCutProbability s κ j z w=1 := by
  have hi : κ/s < 2*κ/s := (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have hinter : Set.Icc (κ/s) (2*κ/s) ∩ directionNoCut j z w = Set.Icc (κ/s) (2*κ/s) := by
    apply Set.inter_eq_left.mpr
    intro t ht c hc
    exact h c (hc.trans ht.2)
  have he : cond volume (Set.Icc (κ/s) (2*κ/s)) (directionNoCut j z w)=1 := by
    calc
      _ = cond volume (Set.Icc (κ/s) (2*κ/s)) (Set.Icc (κ/s) (2*κ/s)) := by
        rw [cond_apply measurableSet_Icc,cond_apply measurableSet_Icc,hinter,Set.inter_self]
      _ = 1 := cond_apply_self
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hi))
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  exact congrArg ENNReal.toReal he

theorem separatorMatrix_eq_one_on_good_row {a : ℕ} {v : ℝ×ℝ} {s κ : ℝ}
    (hs : 0 < s) (hκ : 0 < κ) (z w : SquareFlag a v) (hw : dist z.val w.val ≤ s)
    (hz : ∀j c, |conjugate c| ≤ 2*κ/s →
      (1+|ordinary (cutTau^a)|)*s < |cutForm a j z.val-ordinary c|) :
    separatorMatrix (thresholdLaw s κ) z w=1 := by
  rw [separatorMatrix_product hs hκ]
  suffices ∀j,directionNoCutProbability s κ j z w=1 by simp [this]
  intro j
  apply directionNoCutProbability_eq_one hs hκ
  intro c hc hsep
  have hb := (flagSeparates_near_row hsep).trans
    (mul_le_mul_of_nonneg_left hw (by positivity))
  exact (not_le_of_gt (hz j c hc)) hb

end GoodRowSeparators

section NormalizedTentMass
open Classical MeasureTheory

theorem unitTent_bounds (x : ℝ) : 0 ≤ unitTent x ∧ unitTent x ≤ 1 := by
  constructor
  · exact le_max_right _ _
  · exact max_le (by linarith [abs_nonneg x]) zero_le_one

theorem unitTent_lipschitz : LipschitzWith 1 unitTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq,NNReal.coe_one,one_mul]
  calc
    _ ≤ |(1-|x|)-(1-|y|)| := abs_max_sub_max_le_abs _ _ 0
    _ = abs (abs x - abs y) := by rw [show (1-|x|)-(1-|y|)=-(abs x - abs y) by ring,abs_neg]
    _ ≤ |x-y| := abs_abs_sub_abs_le_abs_sub x y

theorem unitTent_zero {x : ℝ} (hx : 1 ≤ |x|) : unitTent x=0 :=
  max_eq_right (by linarith)

theorem unitTent_integral : ∫x,unitTent x=1 := by
  have hsupp : Function.support unitTent ⊆ Set.Ioc (-1) 1 := by
    intro x hx
    have hh : |x| < 1 := lt_of_not_ge (fun h => hx (unitTent_zero h))
    exact ⟨(abs_lt.mp hh).1,(abs_lt.mp hh).2.le⟩
  rw [← intervalIntegral.integral_eq_integral_of_support_subset hsupp]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (unitTent_lipschitz.continuous.intervalIntegrable (-1) 0)
    (unitTent_lipschitz.continuous.intervalIntegrable 0 1)]
  have hneg : Set.EqOn unitTent (fun x => 1+x) (Set.uIcc (-1) 0) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [unitTent,abs_of_nonpos hx.2,sub_neg_eq_add]
    exact max_eq_left (by linarith [hx.1])
  have hpos : Set.EqOn unitTent (fun x => 1-x) (Set.uIcc 0 1) := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    simp only [unitTent,abs_of_nonneg hx.1]
    exact max_eq_left (by linarith [hx.2])
  rw [intervalIntegral.integral_congr hneg,intervalIntegral.integral_congr hpos,
    intervalIntegral.integral_add (f:=fun _ : ℝ => (1:ℝ)) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _),
    intervalIntegral.integral_sub (f:=fun _ : ℝ => (1:ℝ)) (g:=fun x : ℝ => x) (continuous_const.intervalIntegrable _ _)
      (continuous_id.intervalIntegrable _ _)]
  norm_num [intervalIntegral.integral_const,integral_id]

theorem doubleUnitTent_bounds (x : Fin 2 → ℝ) : 0 ≤ doubleUnitTent x ∧ doubleUnitTent x ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (unitTent_bounds (x i)).1),
    Finset.prod_le_one (fun i _ => (unitTent_bounds (x i)).1) (fun i _ => (unitTent_bounds (x i)).2)⟩

theorem doubleUnitTent_lipschitz : LipschitzWith 2 doubleUnitTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hp := unit_product_sub_bound Finset.univ (fun i => unitTent (x i)) (fun i => unitTent (y i))
    (fun i _ => unitTent_bounds (x i)) (fun i _ => unitTent_bounds (y i))
  calc
    _ ≤ ∑i : Fin 2,|unitTent (x i)-unitTent (y i)| := hp
    _ ≤ ∑i : Fin 2,dist x y := by
      apply Finset.sum_le_sum
      intro i _
      have hh := unitTent_lipschitz.dist_le_mul (x i) (y i)
      rw [Real.dist_eq,NNReal.coe_one,one_mul] at hh
      exact hh.trans (dist_le_pi_dist x y i)
    _ = _ := by simp

theorem doubleUnitTent_zero {x : Fin 2 → ℝ} (hx : 1 < ‖x‖) : doubleUnitTent x=0 := by
  have hh : ∃i,1 < |x i| := by
    by_contra hn
    push Not at hn
    have he : ‖x‖ ≤ (1:ℝ) := by
      rw [← dist_zero_right]
      exact (dist_pi_le_iff zero_le_one).mpr (fun i => by simpa [Real.dist_eq] using hn i)
    exact (not_le_of_gt hx) he
  obtain ⟨i,hi⟩ := hh
  exact Finset.prod_eq_zero (Finset.mem_univ i) (unitTent_zero hi.le)

theorem doubleUnitTent_integral : ∫x,doubleUnitTent x=1 := by
  unfold doubleUnitTent
  rw [integral_fintype_prod_volume_eq_prod]
  simp [unitTent_integral]

theorem unit_mul_sub_bound {a b c d : ℝ} (ha : a∈Set.Icc (0:ℝ) 1) (hb : b∈Set.Icc (0:ℝ) 1)
    (hc : c∈Set.Icc (0:ℝ) 1) (hd : d∈Set.Icc (0:ℝ) 1) :
    |a*b-c*d| ≤ |a-c|+|b-d| := by
  have h := unit_product_sub_bound (Finset.univ : Finset (Fin 2)) ![a,b] ![c,d]
    (by intro i _; fin_cases i <;> assumption) (by intro i _; fin_cases i <;> assumption)
  simpa [Fin.prod_univ_two,Fin.sum_univ_two] using h

theorem pairedUnitTent_lipschitz : LipschitzWith 4 pairedUnitTent := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have hh := unit_mul_sub_bound (doubleUnitTent_bounds x.1) (doubleUnitTent_bounds x.2)
    (doubleUnitTent_bounds y.1) (doubleUnitTent_bounds y.2)
  have h₁ := doubleUnitTent_lipschitz.dist_le_mul x.1 y.1
  have h₂ := doubleUnitTent_lipschitz.dist_le_mul x.2 y.2
  rw [Real.dist_eq] at h₁ h₂
  change |pairedUnitTent x-pairedUnitTent y| ≤ _ at hh
  have hd₁ : dist x.1 y.1 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hd₂ : dist x.2 y.2 ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _
  norm_num at h₁ h₂ ⊢
  linarith

theorem pairedUnitTent_zero {x : (Fin 2 → ℝ)×(Fin 2 → ℝ)} (hx : 1 < ‖x‖) :
    pairedUnitTent x=0 := by
  rw [Prod.norm_def,lt_max_iff] at hx
  rcases hx with hh|hh
  · simp [pairedUnitTent,doubleUnitTent_zero hh]
  · simp [pairedUnitTent,doubleUnitTent_zero hh]

theorem pairedUnitTent_integrable : Integrable pairedUnitTent := by
  apply pairedUnitTent_lipschitz.continuous.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (isCompact_closedBall (0 : (Fin 2 → ℝ)×(Fin 2 → ℝ)) 1)
  intro x hx
  exact pairedUnitTent_zero (lt_of_not_ge (by simpa only [Metric.mem_closedBall,dist_zero_right] using hx))

theorem pairedUnitTent_integral : ∫x,pairedUnitTent x=1 := by
  change (∫x : (Fin 2 → ℝ)×(Fin 2 → ℝ),doubleUnitTent x.1*doubleUnitTent x.2 ∂
    (volume.prod volume))=1
  rw [integral_prod_mul,doubleUnitTent_integral,mul_one]

theorem pairedQuadratic_tent_mass {d s t : ℝ} (hd : 1 ≤ d) (hs : 0 < s) (ht : 0 < t)
    (hst : 36 ≤ s*t) (q : (Fin 2 → ℝ)×(Fin 2 → ℝ)) :
    ∃S : Finset (CutRing×CutRing),
      (∀z,z∉S → pairedUnitTent (q+pairedQuadraticEmbedding d s t z)=0) ∧
      |(5/(d^4*s^2*t^2))*(∑z∈S,pairedUnitTent (q+pairedQuadraticEmbedding d s t z))-1| ≤
        38880/(d*Real.sqrt (s*t)) := by
  obtain ⟨S,hS,hh⟩ := pairedQuadratic_riemann_uniform hd hs ht hst (show 0 ≤ (1:ℝ) by norm_num)
    pairedUnitTent_integrable pairedUnitTent_lipschitz (fun x hx => pairedUnitTent_zero hx) q
  refine ⟨S,hS,?_⟩
  rw [pairedUnitTent_integral] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  norm_num
  ring

end NormalizedTentMass

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagAveragingMatrices
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagAveragingMatrices
open Classical MeasureTheory

theorem planeTent_nonneg (s : ℝ) (x y : ℝ×ℝ) : 0 ≤ planeTent s x y :=
  mul_nonneg (le_max_right _ _) (le_max_right _ _)

end FlagAveragingMatrices

section AveragingRowBounds
open Classical MeasureTheory

theorem tentFactor_ne_zero {s d : ℝ} (hs : 0 < s) :
    max (1-|d/s|) 0 ≠ 0 ↔ |d| < s := by
  rw [ne_eq,max_eq_right_iff,not_le,abs_div,abs_of_pos hs]
  have he : 0 < 1-|d|/s ↔ |d|/s < 1 := by constructor <;> intro h <;> linarith
  rw [he,div_lt_iff₀ hs,one_mul]

theorem planeTent_ne_zero {s : ℝ} (hs : 0 < s) (x y : ℝ×ℝ) :
    planeTent s x y ≠ 0 ↔ |x.1-y.1| < s ∧ |x.2-y.2| < s := by
  rw [planeTent,mul_ne_zero_iff,tentFactor_ne_zero hs,tentFactor_ne_zero hs]

end AveragingRowBounds

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagTentMass
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagTentMass
open Classical

theorem latticeRowTent_eq (D : ℕ) (s t : ℝ) (x y : ℝ×ℝ) (u : CutRing×CutRing) :
    latticeRowTent D s t x y u=
      pairedUnitTent (tentRowOffset s t x y+pairedQuadraticEmbedding D s t u) := by
  simp only [latticeRowTent,planeTent,scaledOrdinary,scaledConjugate,pairedUnitTent,
    doubleUnitTent,Fin.prod_univ_two,unitTent,tentRowOffset,pairedQuadraticEmbedding,
    LinearMap.prodMap_apply,quadraticScaledEmbedding,LinearMap.coe_mk,AddHom.coe_mk,
    Prod.fst_add,Prod.snd_add,Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  have h (a b d c : ℝ) : |(a-b/d)/c|=|-a/c+b/(d*c)| := by
    have he : -a/c+b/(d*c) = -((a-b/d)/c) := by rw [div_mul_eq_div_div]; ring
    rw [he,abs_neg]
  rw [h,h,h,h]
  ring

theorem squareBoundary_of_interior {v x : ℝ×ℝ}
    (hx : 0<x.1 ∧ x.1<1 ∧ 0<x.2 ∧ x.2<1) : SquareBoundary v x := by
  exact ⟨⟨hx.1.le,hx.2.1.le⟩,⟨hx.2.2.1.le,hx.2.2.2.le⟩,
    (fun h => (ne_of_gt hx.1 h).elim),(fun h => (ne_of_lt hx.2.1 h).elim),
    (fun h => (ne_of_gt hx.2.2.1 h).elim),(fun h => (ne_of_lt hx.2.2.2 h).elim)⟩

@[simp] theorem flagSiteFromNumerator_numerator {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) :
    flagSiteNumerator (flagSiteFromNumerator hv k u hu)=u :=
  scaledOrdinary_injective hD (flagSiteNumerator_spec _)

theorem flagSiteFromNumerator_conjugate {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) :
    flagSiteConjugate (flagSiteFromNumerator hv k u hu)=scaledConjugate D u := by
  simp [flagSiteConjugate,flagSiteFromNumerator_numerator hD]

theorem latticeRowTent_interior {a m D : ℕ} {v : ℝ×ℝ} {s t : ℝ} (hs : 0 < s)
    (z : FlagSite a m D v)
    (hi : s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s)
    (u : CutRing×CutRing)
    (hu : latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u≠0) :
    SquareBoundary v (scaledOrdinary D u) := by
  have hh := (planeTent_ne_zero hs _ _).mp (mul_ne_zero_iff.mp hu).1
  have hx := abs_lt.mp hh.1
  have hy := abs_lt.mp hh.2
  apply squareBoundary_of_interior
  exact ⟨by linarith [hi.1],by linarith [hi.2.1],by linarith [hi.2.2.1],by linarith [hi.2.2.2]⟩

theorem flagRowTent_lattice_sum {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {s t : ℝ} (hs : 0 < s) (ht : 0<t) (z : FlagSite a m D v)
    (hi : s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s)
    (S : Finset (CutRing×CutRing))
    (hS : ∀u,u∉S → latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u=0) :
    ∃T : Finset (FlagSite a m D v),
      (∀w,w∉T → flagRowTent s t z w=0) ∧
      (∑w∈T,flagRowTent s t z w)=
        ∑u∈S,latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u := by
  let R := |(flagSiteConjugate z).1|+|(flagSiteConjugate z).2|+t
  have hR : 0<R := by dsimp [R]; positivity
  let T := (flagSiteBox_finite (a:=a) (m:=m) (v:=v) hD hR).toFinset
  have hn (w : FlagSite a m D v) (hw : flagRowTent s t z w≠0) :
      z.val.1=w.val.1 ∧ latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z)
        (flagSiteNumerator w)≠0 := by
    have he : z.val.1=w.val.1 := by
      by_contra hh
      exact hw (by simp [flagRowTent,hh])
    refine ⟨he,?_⟩
    simpa only [flagRowTent,ite_eq_left he,latticeRowTent,flagSiteNumerator_spec,
      flagSiteOrdinary,flagSiteConjugate] using hw
  have hT (w : FlagSite a m D v) (hw : flagRowTent s t z w≠0) : w∈T := by
    have hh := (planeTent_ne_zero ht _ _).mp (mul_ne_zero_iff.mp (hn w hw).2).2
    have hx : |(flagSiteConjugate w).1| < |(flagSiteConjugate z).1|+t := by
      have h := abs_add_le ((flagSiteConjugate w).1-(flagSiteConjugate z).1) (flagSiteConjugate z).1
      rw [sub_add_cancel,abs_sub_comm] at h
      have hh₁ : |(flagSiteConjugate z).1-(flagSiteConjugate w).1| < t := hh.1
      linarith
    have hy : |(flagSiteConjugate w).2| < |(flagSiteConjugate z).2|+t := by
      have h := abs_add_le ((flagSiteConjugate w).2-(flagSiteConjugate z).2) (flagSiteConjugate z).2
      rw [sub_add_cancel,abs_sub_comm] at h
      have hh₂ : |(flagSiteConjugate z).2-(flagSiteConjugate w).2| < t := hh.2
      linarith
    apply (Set.Finite.mem_toFinset _).mpr
    exact ⟨by dsimp [R]; linarith [abs_nonneg (flagSiteConjugate z).2],
      by dsimp [R]; linarith [abs_nonneg (flagSiteConjugate z).1]⟩
  refine ⟨T,fun w hw => by by_contra hh; exact hw (hT w hh),?_⟩
  apply Finset.sum_bij_ne_zero (fun w _ _ => flagSiteNumerator w)
  · intro w hw hnz
    exact by_contra (fun hh => (hn w hnz).2 (hS _ hh))
  · intro w hw hnw w' hw' hnw' he
    apply Subtype.ext
    apply Prod.ext
    · exact (hn w hnw).1.symm.trans (hn w' hnw').1
    · apply Subtype.ext
      rw [← flagSiteNumerator_spec w,← flagSiteNumerator_spec w',he]
  · intro u hu hnu
    let w := flagSiteFromNumerator z.val.2.property.1 z.val.1 u (latticeRowTent_interior hs z hi u hnu)
    have he : flagRowTent s t z w=latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u := by
      rw [flagRowTent,ite_eq_left (show z.val.1=w.val.1 from rfl)]
      change planeTent s _ (scaledOrdinary D u)*planeTent t _ (flagSiteConjugate (flagSiteFromNumerator _ _ _ _)) = _
      rw [flagSiteFromNumerator_conjugate hD]
      rfl
    have hw : flagRowTent s t z w≠0 := by rwa [he]
    exact ⟨w,hT w hw,hw,flagSiteFromNumerator_numerator hD _ _ _ _⟩
  · intro w hw hnw
    simp only [flagRowTent,ite_eq_left (hn w hnw).1,latticeRowTent,
      flagSiteNumerator_spec,flagSiteOrdinary,flagSiteConjugate]

theorem flagRowTent_mass {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {s t : ℝ} (hs : 0 < s) (ht : 0<t) (hst : 36 ≤ s*t) (z : FlagSite a m D v)
    (hi : s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s) :
    ∃T : Finset (FlagSite a m D v),
      (∀w,w∉T → flagRowTent s t z w=0) ∧
      |(5/((D:ℝ)^4*s^2*t^2))*(∑w∈T,flagRowTent s t z w)-1| ≤
        38880/((D:ℝ)*Real.sqrt (s*t)) := by
  obtain ⟨S,hS,hh⟩ := pairedQuadratic_tent_mass (d:=D) (by exact_mod_cast hD) hs ht hst
    (tentRowOffset s t (flagSiteOrdinary z) (flagSiteConjugate z))
  simp only [← latticeRowTent_eq] at hS hh
  obtain ⟨T,hT,he⟩ := flagRowTent_lattice_sum hD hs ht z hi S hS
  exact ⟨T,hT,by rwa [he]⟩

end FlagTentMass

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_WeightedAveragingError
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section WeightedAveragingError
open Classical

theorem weighted_average_error {ι : Type*} (T : Finset ι) (k h : ι → ℝ) (h₀ E H δ : ℝ)
    (hk : ∀i∈T,0≤k i) (hE : 0≤E) (hH : |h₀|≤H)
    (hmass : |(∑i∈T,k i)-1|≤δ)
    (hnear : ∀i∈T,k i≠0 → |h i-h₀|≤E) :
    |(∑i∈T,k i*h i)-h₀| ≤ E*(1+δ)+H*δ := by
  have hδ : 0≤δ := (abs_nonneg _).trans hmass
  have hH₀ : 0≤H := (abs_nonneg _).trans hH
  have he : (∑i∈T,k i*h i)-h₀=
      (∑i∈T,k i*(h i-h₀))+h₀*((∑i∈T,k i)-1) := by
    simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul]
    ring
  have hb : |∑i∈T,k i*(h i-h₀)| ≤ E*(∑i∈T,k i) := by
    calc
      _ ≤ ∑i∈T,|k i*(h i-h₀)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑i∈T,k i*E := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul,abs_of_nonneg (hk i hi)]
        by_cases hh : k i=0
        · simp [hh]
        · exact mul_le_mul_of_nonneg_left (hnear i hi hh) (hk i hi)
      _ = _ := by rw [← Finset.sum_mul,mul_comm]
  rw [he]
  calc
    _ ≤ |∑i∈T,k i*(h i-h₀)|+|h₀*((∑i∈T,k i)-1)| := abs_add_le _ _
    _ ≤ E*(∑i∈T,k i)+H*δ := add_le_add hb (by rw [abs_mul]; exact mul_le_mul hH hmass (abs_nonneg _) hH₀)
    _ ≤ _ := by nlinarith [(abs_le.mp hmass).2]

end WeightedAveragingError

section GoodRowAveraging
open Classical

theorem flagGoodRow_interior {a m D : ℕ} {v : ℝ×ℝ} {s κ : ℝ} (hs : 0 < s)
    (hκ : 1 ≤ 2*κ/s) (z : FlagSite a m D v) (hz : flagGoodRow s κ z) :
    s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s := by
  have hzero : |conjugate (0:CutRing)| ≤ 2*κ/s := by simpa only [map_zero,abs_zero] using zero_le_one.trans hκ
  have hone : |conjugate (1:CutRing)| ≤ 2*κ/s := by simpa only [map_one,abs_one] using hκ
  have hx₀ := hz 0 0 hzero
  have hx₁ := hz 0 1 hone
  have hy₀ := hz 1 0 hzero
  have hy₁ := hz 1 1 hone
  have hx := z.val.2.property.2.1
  have hy := z.val.2.property.2.2.1
  simp [cutForm,map_zero,map_one,sub_zero,abs_of_nonneg hx.1,abs_of_nonneg hy.1,
    abs_of_nonpos (sub_nonpos.mpr hx.2),abs_of_nonpos (sub_nonpos.mpr hy.2)] at hx₀ hx₁ hy₀ hy₁
  change s<z.val.2.val.1 ∧ z.val.2.val.1<1-s ∧ s<z.val.2.val.2 ∧ z.val.2.val.2<1-s
  have hL : s ≤ (1+|ordinary (cutTau^a)|)*s := by nlinarith [abs_nonneg (ordinary (cutTau^a))]
  simp only [map_pow,ordinary_cutTau,abs_pow] at hL
  exact ⟨by linarith,by linarith,by linarith,by linarith⟩

theorem flagRowTent_nonneg {a m D : ℕ} {v : ℝ×ℝ} (s t : ℝ) (z w : FlagSite a m D v) :
    0 ≤ flagRowTent s t z w := by
  unfold flagRowTent
  split_ifs
  · exact mul_nonneg (planeTent_nonneg _ _ _) (planeTent_nonneg _ _ _)
  · exact le_rfl

theorem flagRowTent_ne_zero_iff {a m D : ℕ} {v : ℝ×ℝ} (s t : ℝ) (z w : FlagSite a m D v) :
    flagRowTent s t z w≠0 ↔ z.val.1=w.val.1 ∧
      planeTent s (flagSiteOrdinary z) (flagSiteOrdinary w)≠0 ∧
      planeTent t (flagSiteConjugate z) (flagSiteConjugate w)≠0 := by
  by_cases ht : z.val.1=w.val.1 <;> simp [flagRowTent,ht]

theorem flagRowTent_separator_one {a m D : ℕ} {v : ℝ×ℝ} {s κ : ℝ} (hs : 0 < s)
    (hκ : 0<κ) (t : ℝ) (z w : FlagSite a m D v)
    (hz : flagGoodRow s κ z) (hw : flagRowTent s t z w≠0) :
    separatorMatrix (thresholdLaw s κ) z.val.2 w.val.2=1 := by
  apply separatorMatrix_eq_one_on_good_row hs hκ _ _ _ hz
  have hh := (planeTent_ne_zero hs _ _).mp ((flagRowTent_ne_zero_iff s t z w).mp hw).2.1
  rw [Prod.dist_eq,Real.dist_eq,Real.dist_eq]
  exact max_le hh.1.le hh.2.le

theorem flagNormalization {D : ℕ} {N r η : ℝ} (hN : 0<N) :
    5/((D:ℝ)^4*(r/N)^2*(N*η)^2) = (((D:ℝ)^4/5)*(r*η)^2)⁻¹ := by
  have hd : (D:ℝ)^4*(r/N)^2*(N*η)^2=(D:ℝ)^4*(r*η)^2 := by field_simp
  rw [hd]
  ring

theorem flagAveragingMatrix_eq_rowTent {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v) :
    flagAveragingMatrix χ ρ N r η κ z w=
      (χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)/(ρ*(r*η)^2))*
        flagRowTent (r/N) (N*η) z w*separatorMatrix (thresholdLaw (r/N) κ) z.val.2 w.val.2 := by
  dsimp only [flagAveragingMatrix,flagRowTent,Matrix.of,Equiv.refl,DFunLike.coe,
    EquivLike.toFunLike,Equiv.instEquivLike,EquivLike.coe,Matrix,id]
  split_ifs <;> ring

theorem flagAveragingMatrix_good_action {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (h : FlagSite a m D v → ℝ) {N r η κ : ℝ}
    (hN : 0<N) (hr : 0 < r) (hκ : 0<κ) (z : FlagSite a m D v)
    (hz : flagGoodRow (r/N) κ z)
    (hχ : ∀w,flagRowTent (r/N) (N*η) z w≠0 → h w≠0 →
      χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1) (w : FlagSite a m D v) :
    flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=
      (5/((D:ℝ)^4*(r/N)^2*(N*η)^2))*flagRowTent (r/N) (N*η) z w*h w := by
  rw [flagAveragingMatrix_eq_rowTent,flagNormalization hN]
  by_cases hhw : h w=0
  · simp [hhw]
  by_cases hkw : flagRowTent (r/N) (N*η) z w=0
  · simp [hkw]
  rw [(hχ w hkw hhw).1,(hχ w hkw hhw).2,flagRowTent_separator_one (div_pos hr hN) hκ _ z w hz hkw]
  ring

theorem flagAveragingMatrix_good_row_error_oai {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (h : FlagSite a m D v → ℝ) {N r η κ E H : ℝ}
    (hN : 0<N) (hr : 0 < r) (hη : 0<η) (hκ : 0<κ)
    (hscale : 36 ≤ r*η) (hline : 1 ≤ 2*κ/(r/N))
    (hE : 0 ≤ E) (z : FlagSite a m D v) (hz : flagGoodRow (r/N) κ z)
    (hH : |h z| ≤ H)
    (hχ : ∀w,flagRowTent (r/N) (N*η) z w≠0 → h w≠0 →
      χ (scaledSiteConjugate N z)=1 ∧ χ (scaledSiteConjugate N w)=1)
    (hnear : ∀w,flagRowTent (r/N) (N*η) z w≠0 → |h w-h z| ≤ E) :
    ∃T : Finset (FlagSite a m D v),
      (∀w,w∉T → flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w=0) ∧
      |(∑w∈T,flagAveragingMatrix χ ((D:ℝ)^4/5) N r η κ z w*h w)-h z| ≤
        E*(1+38880/((D:ℝ)*Real.sqrt (r*η)))+H*(38880/((D:ℝ)*Real.sqrt (r*η))) := by
  have hst : (r/N)*(N*η)=r*η := by field_simp
  obtain ⟨T,hT,hmass⟩ := flagRowTent_mass hD (div_pos hr hN) (mul_pos hN hη)
    (by rwa [hst]) z (flagGoodRow_interior (div_pos hr hN) hline z hz)
  let c := 5/((D:ℝ)^4*(r/N)^2*(N*η)^2)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hact := flagAveragingMatrix_good_action χ h hN hr hκ z hz hχ
  refine ⟨T,fun w hw => ?_,?_⟩
  · rw [hact w,hT w hw,mul_zero,zero_mul]
  · simp_rw [hact]
    have hh := weighted_average_error T (fun w => c*flagRowTent (r/N) (N*η) z w) h (h z) E H
      (38880/((D:ℝ)*Real.sqrt (r*η)))
      (fun w _ => mul_nonneg hc (flagRowTent_nonneg _ _ _ _)) hE hH
      (by simpa only [← Finset.mul_sum,hst] using hmass)
      (fun w _ hn => hnear w (fun he => hn (by simp [he])))
    exact hh

end GoodRowAveraging

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.flagAveragingMatrix_good_row_error_oai := @OAI.SimpleAmenable.flagAveragingMatrix_good_row_error_oai
