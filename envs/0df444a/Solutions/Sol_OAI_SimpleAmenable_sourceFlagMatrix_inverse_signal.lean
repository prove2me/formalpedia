-- Prove2me | solution 1 for OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:52:54.928391+00:00
-- url     : https://prove2.me/submissions/0f73c443-b16e-4477-acc5-1e5abdc55e00

import Mathlib
import Definitions.Def_OAIQ65Sa014
import Theorems.Thm_OAI_SimpleAmenable_polygon_signal_approx_identity

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_Arithmetic_DyadicArithmetic
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
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
section SourceDyadicArithmetic
open Classical Filter
open scoped Topology

theorem sourceDyadicN_one_le (n : ℕ) : 1 ≤ sourceDyadicN n := by
  unfold sourceDyadicN
  exact one_le_pow₀ (by norm_num)

theorem sourceDyadicIndices_card (n : ℕ) : (sourceDyadicIndices n).card=n+1 := by
  simp only [sourceDyadicIndices,Nat.card_Icc]
  omega

theorem sourceDyadic_log (n : ℕ) : Real.log (sourceDyadicN n)=(4*Real.log 2)*(n:ℝ) := by
  rw [sourceDyadicN,Real.log_pow]
  push_cast
  ring

theorem sourceDyadic_fine_eventually (R : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠn : ℕ in atTop,∀i∈sourceDyadicIndices n,R ≤ κ/((2:ℝ)^i/sourceDyadicN n) := by
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ) < 4 by norm_num)).const_mul_atTop hκ
  filter_upwards [ht.eventually_ge_atTop R] with n hn i hi
  have hi' : i ≤ 2*n := (Finset.mem_Icc.mp hi).2
  have hp : (2:ℝ)^i ≤ (2:ℝ)^(2*n) := pow_le_pow_right₀ (by norm_num) hi'
  have he : κ/((2:ℝ)^(2*n)/sourceDyadicN n)=κ*(4:ℝ)^n := by
    unfold sourceDyadicN
    have hN : (2:ℝ)^(4*n)=((2:ℝ)^(2*n))^2 := by rw [← pow_mul]; congr 1; omega
    have h4 : (4:ℝ)^n=(2:ℝ)^(2*n) := by rw [pow_mul]; norm_num
    rw [hN,h4]
    field_simp
  calc
    R ≤ κ*(4:ℝ)^n := hn
    _ = κ/((2:ℝ)^(2*n)/sourceDyadicN n) := he.symm
    _ ≤ _ := by
      apply div_le_div_of_nonneg_left hκ.le (div_pos (by positivity) (sourceDyadicN_pos n))
      exact div_le_div_of_nonneg_right hp (sourceDyadicN_pos n).le

end SourceDyadicArithmetic

end SimpleAmenable
end
end

end OAI
end

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
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSites
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

theorem flagSiteNumerator_action {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteNumerator (flagSiteAction hD g z)=flagShiftNumerator D (flagSiteNumerator z)
      (flagChart g z.val).shift (flagShiftPeriod (flagChart g z.val).shift z.val.2) := by
  apply scaledOrdinary_injective hD
  rw [flagSiteNumerator_spec,scaledOrdinary_shift hD,flagSiteNumerator_spec]
  change (flagTranslate _ z.val.2).val=_
  simp only [flagTranslate_val,flagFract_eq,flagShiftPeriod]
  rfl

theorem flagSiteConjugate_action {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteConjugate (flagSiteAction hD g z)=flagSiteConjugate z+
      (conjugate (flagChart g z.val).shift.1,conjugate (flagChart g z.val).shift.2)-
      (((flagShiftPeriod (flagChart g z.val).shift z.val.2).1:ℝ),
       ((flagShiftPeriod (flagChart g z.val).shift z.val.2).2:ℝ)) := by
  have hD' : (D:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hD
  unfold flagSiteConjugate
  rw [flagSiteNumerator_action hD]
  apply Prod.ext <;>
    simp only [scaledConjugate,flagShiftNumerator,Prod.fst_sub,Prod.snd_sub,
      Prod.fst_add,Prod.snd_add,map_sub,map_add,map_mul,map_natCast,map_intCast] <;>
    field_simp

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
section TentMatrixPositivity
open Classical MeasureTheory

theorem integral_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (A : Ω → Matrix ι ι ℝ) (hA : ∀ᵐ ω∂μ,(A ω).PosSemidef)
    (hi : ∀i j,Integrable (fun ω => A ω i j) μ) :
    Matrix.PosSemidef (fun i j => ∫ω,A ω i j ∂μ) := by
  refine ⟨?_,fun x => ?_⟩
  · ext i j
    change star (∫ω,A ω j i ∂μ)=∫ω,A ω i j ∂μ
    simp only [star_trivial]
    apply integral_congr_ae
    filter_upwards [hA] with ω hω
    have he := congrFun (congrFun hω.isHermitian i) j
    simpa using he
  · have hi' (i j : ι) : Integrable (fun ω => x i*A ω i j*x j) μ :=
      ((hi i j).const_mul _).mul_const _
    have he : (∫ω,x.sum (fun i xi => x.sum (fun j xj => star xi*A ω i j*xj)) ∂μ)=
        x.sum (fun i xi => x.sum (fun j xj => star xi*(∫ω,A ω i j ∂μ)*xj)) := by
      simp only [star_trivial,Finsupp.sum]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi' i j))]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum _ (fun j _ => hi' i j)]
      simp only [integral_mul_const,integral_const_mul]
    rw [← he]
    apply integral_nonneg_of_ae
    filter_upwards [hA] with ω hω
    exact hω.2 x

theorem intervalMark_mul (x y : ℝ) :
    (fun t => intervalMark x t*intervalMark y t)=
      (Set.Icc (max x y) (min (x+1) (y+1))).indicator (fun _ => (1:ℝ)) := by
  funext t
  have hm : t∈Set.Icc (max x y) (min (x+1) (y+1)) ↔
      t∈Set.Icc x (x+1) ∧ t∈Set.Icc y (y+1) := by
    simp only [Set.mem_Icc,max_le_iff,le_min_iff]
    tauto
  by_cases hx : t∈Set.Icc x (x+1) <;> by_cases hy : t∈Set.Icc y (y+1) <;>
    simp [intervalMark,Set.indicator,hm,hx,hy]

theorem intervalMark_mul_integrable (x y : ℝ) :
    Integrable (fun t => intervalMark x t*intervalMark y t) := by
  rw [intervalMark_mul]
  exact (integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top))

theorem tent_eq_intervalMark_integral (x y : ℝ) :
    max (1-|x-y|) 0=∫t,intervalMark x t*intervalMark y t := by
  rw [intervalMark_mul,integral_indicator_const 1 measurableSet_Icc]
  simp only [smul_eq_mul,mul_one,Real.volume_real_Icc]
  congr 1
  rcases le_total x y with h|h
  · rw [max_eq_right h,min_eq_left (by linarith),abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · rw [max_eq_left h,min_eq_right (by linarith),abs_of_nonneg (sub_nonneg.mpr h)]
    ring

theorem real_rankOne_posSemidef {ι : Type*} (a : ι → ℝ) :
    Matrix.PosSemidef (fun i j => a i*a j) := by
  refine ⟨?_,fun x => ?_⟩
  · ext i j
    change a j*a i=a i*a j
    exact mul_comm _ _
  · calc
      0≤(x.sum (fun i xi => xi*a i))^2 := sq_nonneg _
      _=x.sum (fun i xi => x.sum (fun j xj => star xi*(a i*a j)*xj)) := by
        simp only [pow_two,Finsupp.sum,Finset.sum_mul,Finset.mul_sum,star_trivial]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring

theorem tentMatrix_posSemidef {ι : Type*} (x : ι → ℝ) :
    Matrix.PosSemidef (fun i j => max (1-|x i-x j|) 0) := by
  have hp (t : ℝ) : Matrix.PosSemidef (fun i j => intervalMark (x i) t*intervalMark (x j) t) :=
    real_rankOne_posSemidef _
  have h := integral_posSemidef volume
    (fun t i j => intervalMark (x i) t*intervalMark (x j) t)
    (Filter.Eventually.of_forall hp) (fun i j => intervalMark_mul_integrable (x i) (x j))
  simpa only [← tent_eq_intervalMark_integral] using h

theorem planeTentMatrix_posSemidef {ι : Type*} (x : ι → ℝ×ℝ) (s : ℝ) :
    Matrix.PosSemidef (fun i j => max (1-|(x i).1/s-(x j).1/s|) 0 *
      max (1-|(x i).2/s-(x j).2/s|) 0) := by
  exact (tentMatrix_posSemidef (fun i => (x i).1/s)).hadamard
    (tentMatrix_posSemidef (fun i => (x i).2/s))

end TentMatrixPositivity

section FlagSeparatorMatrices
open Classical MeasureTheory

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

theorem equalityMatrix_posSemidef {ι κ : Type*} (f : ι → κ) :
    Matrix.PosSemidef (fun i j => if f i=f j then (1:ℝ) else 0) := by
  have h := (Matrix.PosSemidef.one (n := κ) (R := ℝ)).submatrix f
  have he : (1 : Matrix κ κ ℝ).submatrix f f=(fun i j => if f i=f j then 1 else 0) := by
    funext i j
    exact Matrix.one_apply (α := ℝ) (n := κ) (i := f i) (j := f j)
  rw [he] at h
  exact h

theorem separatorMatrix_integrand_integrable {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ] (z w : SquareFlag a v) :
    Integrable (fun t => if flagChamber t z=flagChamber t w then (1:ℝ) else 0) μ := by
  exact (integrable_indicator_iff (measurableSet_flagChamber_eq z w)).mpr integrableOn_const

theorem separatorMatrix_posSemidef {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsFiniteMeasure μ] :
    Matrix.PosSemidef (separatorMatrix (a:=a) (v:=v) μ) := by
  apply integral_posSemidef
  · exact Filter.Eventually.of_forall fun t => equalityMatrix_posSemidef (flagChamber t)
  · exact separatorMatrix_integrand_integrable μ

theorem thresholdLaw_isProbability {s κ : ℝ} (hs : 0 < s) (hκ : 0<κ) :
    IsProbabilityMeasure (thresholdLaw s κ) := by
  have hlt : κ/s<2*κ/s := by exact (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (κ/s) (2*κ/s))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hlt))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  unfold thresholdLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagArrangementControl
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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

section SquareAffineCharts
open Classical

theorem squareTranslationPeriod_germ {a : ℕ} {v : ℝ×ℝ}
    (u : CutRing×CutRing) (z : SquareFlag a v) :
    IsSquareGerm (squareTranslationPeriod u) z (flagShiftPeriod u z) := by
  let k := flagShiftPeriod u z
  let t := u-SquareStep.intPair k
  let b : ℝ×ℝ := (ordinary t.1,ordinary t.2)
  have hbase : (flagTranslate u z).val=z.val+b := by
    apply Prod.ext <;> simp only [flagTranslate_val,flagFract_eq,b,t,k,flagShiftPeriod,SquareStep.intPair,
      Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,map_sub,map_intCast] <;> ring
  let M : Set (ℝ×ℝ) := (fun p => p+b) ⁻¹' arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
  refine ⟨M,(arrangementNeighborhood_open _ _ _).preimage (continuous_id.add continuous_const),?_,fun p hp hpv => ?_⟩
  · change z.val+b ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val
    rw [← hbase]
    exact self_mem_arrangementNeighborhood _ _ _
  · let q : GenericPlane a := GenericPlane.shift t ⟨p.val,p.property.2.2⟩
    have hqv : q.val ∈ planeSector a (flagTranslate u z).val v := by
      rw [hbase]
      exact (planeSector_add_iff z.val v b p.val).mpr hpv
    have hpq : q.val ∈ arrangementNeighborhood a SquareStep.squareEdgeCuts (flagTranslate u z).val := hp
    have hqs := sector_enters_square (flagTranslate u z).property.2 hpq hqv
    have hx : 0 ≤ p.val.1+ordinary u.1-(k.1:ℝ) ∧ p.val.1+ordinary u.1-(k.1:ℝ) < 1 := by
      simpa only [q,GenericPlane.shift,t,SquareStep.intPair,Prod.fst_add,Prod.fst_sub,map_sub,map_intCast,← add_sub_assoc,Set.mem_Ico] using hqs.1
    have hy : 0 ≤ p.val.2+ordinary u.2-(k.2:ℝ) ∧ p.val.2+ordinary u.2-(k.2:ℝ) < 1 := by
      simpa only [q,GenericPlane.shift,t,SquareStep.intPair,Prod.snd_add,Prod.snd_sub,map_sub,map_intCast,← add_sub_assoc,Set.mem_Ico] using hqs.2
    apply Prod.ext
    · exact Int.floor_eq_iff.mpr ⟨by linarith [hx.1],by linarith [hx.2]⟩
    · exact Int.floor_eq_iff.mpr ⟨by linarith [hy.1],by linarith [hy.2]⟩

end SquareAffineCharts

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FlagSiteCounts
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
section FlagSiteCounts
open Classical

theorem flagSiteBox_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {R : ℝ} (hR : 0<R) (S : Finset (FlagSite a m D v))
    (hS : ∀z∈S,z∈flagSiteBox R) :
    (S.card:ℝ) ≤ m *(2*(D:ℝ)^2*R+2)^2 := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  let T := (cutRectangle_finite 0 (-(D:ℝ)*R) D (2*D*R) (by positivity)).toFinset
  have ht (u : CutRing) : u∈T ↔ u∈cutRectangle 0 (-(D:ℝ)*R) D (2*D*R) :=
    Set.Finite.mem_toFinset _
  have hc : T.card < (2*(D:ℝ)^2*R+2) := by
    have hh := cutRectangle_card_bound T 0 (-(D:ℝ)*R) D (2*D*R) hd.le (by positivity)
      (fun u hu => (ht u).mp hu)
    nlinarith
  have hn : S.card ≤ m *T.card^2 := by
    rw [← Finset.card_image_of_injective _ flagSite_key_injective]
    have hi : S.image (fun z => (z.val.1,flagSiteNumerator z)) ⊆
        (Finset.univ : Finset (Fin m)) ×ˢ (T ×ˢ T) := by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      have hh := flagSiteNumerator_box hD z (hS z hz)
      simp only [Finset.mem_product,Finset.mem_univ,true_and]
      exact ⟨(ht _).mpr hh.1,(ht _).mpr hh.2⟩
    simpa [Finset.card_product,pow_two] using Finset.card_le_card hi
  have hn' : (S.card:ℝ) ≤ m *(T.card:ℝ)^2 := by exact_mod_cast hn
  have hh : (T.card:ℝ)^2≤(2*(D:ℝ)^2*R+2)^2 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) T.card]
  exact hn'.trans (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _))

end FlagSiteCounts

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

theorem planeTent_posSemidef {ι : Type*} (s : ℝ) (x : ι → ℝ×ℝ) :
    Matrix.PosSemidef (fun i j => planeTent s (x i) (x j)) := by
  simpa only [planeTent,sub_div] using planeTentMatrix_posSemidef x s

theorem flagAveragingMatrix_posSemidef {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N)
    (hr : 0 < r) (hκ : 0 < κ) :
    (flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ N r η κ).PosSemidef := by
  classical
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  have hcut := (real_rankOne_posSemidef (fun z : FlagSite a m D v => χ (scaledSiteConjugate N z))).smul
    (show 0 ≤ (ρ*(r*η)^2)⁻¹ from inv_nonneg.mpr (mul_nonneg hρ.le (sq_nonneg _)))
  have hsep := (separatorMatrix_posSemidef (a:=a) (v:=v) (thresholdLaw (r/N) κ)).submatrix
    (fun z : FlagSite a m D v => z.val.2)
  have htrack := equalityMatrix_posSemidef (fun z : FlagSite a m D v => z.val.1)
  let M : Matrix (FlagSite a m D v) (FlagSite a m D v) ℝ :=
    Matrix.hadamard (Matrix.hadamard (Matrix.hadamard (Matrix.hadamard
      ((ρ*(r*η)^2)⁻¹ • (fun (z w : FlagSite a m D v) =>
        χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w)))
      (fun z w => planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)))
      (fun z w => planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w)))
      (Matrix.submatrix (separatorMatrix (a:=a) (v:=v) (thresholdLaw (r/N) κ))
        (fun z : FlagSite a m D v => z.val.2) (fun z : FlagSite a m D v => z.val.2)))
      (fun z w => @ite ℝ (z.val.1=w.val.1) (Classical.propDecidable _) 1 0)
  have h : M.PosSemidef :=
    (((hcut.hadamard (planeTent_posSemidef (r/N) flagSiteOrdinary)).hadamard
      (planeTent_posSemidef (N*η) flagSiteConjugate)).hadamard hsep).hadamard htrack
  have he : flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ρ N r η κ = M := by
    ext z w
    dsimp only [flagAveragingMatrix, M, Matrix.hadamard, Matrix.submatrix, Matrix.of, Equiv.refl, DFunLike.coe, EquivLike.toFunLike, Equiv.instEquivLike, EquivLike.coe, Matrix, id]
    simp only [Pi.smul_apply, smul_eq_mul]
    split_ifs <;> ring
  rw [he]
  exact h

theorem flagAveragingMatrix_cutoff_left {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : χ (scaledSiteConjugate N z)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hz]

theorem flagAveragingMatrix_cutoff_right {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hw : χ (scaledSiteConjugate N w)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hw]

end FlagAveragingMatrices

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

@[simp] theorem flagSiteFromNumerator_numerator {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) :
    flagSiteNumerator (flagSiteFromNumerator hv k u hu)=u :=
  scaledOrdinary_injective hD (flagSiteNumerator_spec _)

end FlagTentMass

section FiniteDifference

theorem finiteDifference_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : E → ℝ) (hθ : Differentiable ℝ θ) {L : NNReal}
    (hL : LipschitzWith L (fderiv ℝ θ)) (δ x y : E) :
    |(θ (x+δ)-θ x)-(θ (y+δ)-θ y)| ≤ (L:ℝ)*‖δ‖*‖x-y‖ := by
  let F : E → ℝ := fun x => θ (x+δ)-θ x
  have hf (x : E) : HasFDerivAt F (fderiv ℝ θ (x+δ)-fderiv ℝ θ x) x := by
    have hh := (hasFDerivAt_comp_add_right δ).mpr (hθ (x+δ)).hasFDerivAt
    exact hh.sub (hθ x).hasFDerivAt
  have hb (z : E) : ‖fderiv ℝ F z‖ ≤ (L:ℝ)*‖δ‖ := by
    rw [(hf z).fderiv]
    simpa only [add_sub_cancel_left] using hL.norm_sub_le (z+δ) z
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (f:=F) (s:=Set.univ) (fun z _ => (hf z).differentiableAt) (fun z _ => hb z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [F,Real.norm_eq_abs] using hh

theorem compactSignal_uniform_constants {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) :
    ∃L₀ L₁ : NNReal,LipschitzWith L₀ ψ ∧ ∀δ x y : E,
      |(ψ (x+δ)-ψ x)-(ψ (y+δ)-ψ y)| ≤ (L₁:ℝ)*‖δ‖*‖x-y‖ := by
  obtain ⟨L₀,hL₀⟩ := hψ.lipschitzWith_of_hasCompactSupport hs (by norm_num)
  have hd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  obtain ⟨L₁,hL₁⟩ := hd.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ) (by norm_num)
  exact ⟨L₀,L₁,hL₀,finiteDifference_lipschitz ψ (hψ.differentiable (by norm_num)) hL₁⟩

end FiniteDifference

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_PolygonGeometry_FullGroupAffineData
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.cellMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FullGroupAffineData
open Classical

theorem flagAffineData_chart {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (i : Fin m) (z : SquareFlag a v) (c : TableChart a m) (hc : c.Holds g.val)
    (hi : i=c.source) (hz : flagMem c.domain z) :
    flagAffineData g i z=(c.target,c.shift-SquareStep.intPair (flagShiftPeriod c.shift z)) := by
  obtain ⟨N,hN,hzN,hf⟩ := flagMem_iff c.domain z
  obtain ⟨M,hM,hzM,hp⟩ := squareTranslationPeriod_germ c.shift z
  apply flagValue_eq
  refine ⟨N∩M,hN.inter hM,⟨hzN,hzM⟩,fun p hpm hpv => ?_⟩
  rw [fullGroupAffineData_chart g i p c hc hi ((hf p hpm.1 hpv).mpr hz),hp p hpm.2 hpv]

theorem flagAffineData_selected {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (z : FlagTrackPoint a m v) :
    flagAffineData g z.1 z.2=((flagChart g z).target,
      (flagChart g z).shift-SquareStep.intPair (flagShiftPeriod (flagChart g z).shift z.2)) :=
  flagAffineData_chart g z.1 z.2 (flagChart g z) (flagChart_spec g z).1
    (flagChart_spec g z).2.1 (flagChart_spec g z).2.2

theorem flagAffineData_conjugate {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (z : FlagSite a m D v) :
    flagSiteConjugate (flagSiteAction hD g z)=flagSiteConjugate z+
      (conjugate (flagAffineData g z.val.1 z.val.2).2.1,
       conjugate (flagAffineData g z.val.1 z.val.2).2.2) := by
  rw [flagAffineData_selected,flagSiteConjugate_action hD]
  apply Prod.ext <;>
    simp only [SquareStep.intPair,Prod.fst_sub,Prod.snd_sub,Prod.fst_add,Prod.snd_add,
      map_sub,map_intCast] <;> ring

end FullGroupAffineData

section FlagAffineControl
open Classical

theorem squareArrangement_finite_range {a : ℕ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) : (Set.range f).Finite := by
  obtain ⟨S,hS⟩ := hf
  let p (k : Set.range f) : GenericSquare a := k.property.choose
  have hp (k : Set.range f) : f (p k)=k.val := k.property.choose_spec
  let q (k : Set.range f) : S → Bool := fun l => squareSign l.val (p k)
  have hq : Function.Injective q := by
    intro k j h
    apply Subtype.ext
    rw [← hp k,← hp j]
    exact hS (p k) (p j) (fun l hl => congrFun h ⟨l,hl⟩)
  have : Finite (Set.range f) := Finite.of_injective q hq
  exact Set.toFinite _

theorem flagValue_mem_range {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) (z : SquareFlag a v) : flagValue f hf z∈Set.range f := by
  obtain ⟨N,hN,hz,hf'⟩ := flagValue_spec f hf z
  obtain ⟨p,hp,hpv⟩ := squareSector_generic z hN hz
  exact ⟨p,hf' p hp hpv⟩

theorem flagValue_finite_range {a : ℕ} {v : ℝ×ℝ} {K : Type*} (f : GenericSquare a → K)
    (hf : HasSquareArrangement f) : (Set.range (flagValue (v:=v) f hf)).Finite :=
  (squareArrangement_finite_range f hf).subset (by rintro _ ⟨z,rfl⟩; exact flagValue_mem_range f hf z)

theorem flagAffineData_finite_range {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m) :
    (Set.range (fun z : FlagTrackPoint a m v => flagAffineData g z.1 z.2)).Finite := by
  have h (i : Fin m) : (Set.range (flagAffineData (v:=v) g i)).Finite :=
    flagValue_finite_range (fullGroupAffineData g i) (fullGroupAffineData_arrangement g i)
  apply (Set.finite_iUnion h).subset
  rintro _ ⟨z,rfl⟩
  exact Set.mem_iUnion.mpr ⟨z.1,⟨z.2,rfl⟩⟩

theorem flagAffineData_bounded {a m : ℕ} {v : ℝ×ℝ} (g : polygonFullGroup a m)
    (f : (CutRing×CutRing) → ℝ) :
    ∃C : ℝ,0 ≤ C ∧ ∀z : FlagTrackPoint a m v,|f (flagAffineData g z.1 z.2).2| ≤ C := by
  let S := (flagAffineData_finite_range (v:=v) g).toFinset
  refine ⟨∑d∈S,|f d.2|,Finset.sum_nonneg (fun _ _ => abs_nonneg _),fun z => ?_⟩
  apply Finset.single_le_sum (f:=fun d : Fin m × (CutRing×CutRing) => |f d.2|) (fun _ _ => abs_nonneg _)
  change flagAffineData g z.1 z.2∈(flagAffineData_finite_range (v:=v) g).toFinset
  exact (Set.Finite.mem_toFinset _).mpr ⟨z,rfl⟩

end FlagAffineControl

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FlagSignalEnergy
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section FlagSignalEnergy
open Classical

theorem flagSiteAction_displacement {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) :
    ∃Q : ℝ,0≤Q ∧ ∀z : FlagSite a m D v,
      |(flagSiteConjugate (flagSiteAction hD g z)).1-(flagSiteConjugate z).1|+
      |(flagSiteConjugate (flagSiteAction hD g z)).2-(flagSiteConjugate z).2| ≤ Q := by
  obtain ⟨Q,hQ,hb⟩ := flagAffineData_bounded (v:=v) g
    (fun u => |conjugate u.1|+|conjugate u.2|)
  refine ⟨Q,hQ,fun z => ?_⟩
  have hh := hb z.val
  rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))] at hh
  simpa only [flagAffineData_conjugate hD,Prod.fst_add,Prod.snd_add,add_sub_cancel_left] using hh

theorem flagSignalDifference_amplitude {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0≤L)
    (hLip : ∀x y,|θ x-θ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃ C : ℝ,0≤C ∧ ∀N : ℝ,0<N → ∀z : FlagSite a m D v,
      |flagSignalDifference hD g θ N z| ≤ C/N := by
  obtain ⟨Q,hQ,hdisp⟩ := flagSiteAction_displacement (v:=v) hD g⁻¹
  refine ⟨L*Q,mul_nonneg hL hQ,fun N hN z => ?_⟩
  have h := hLip (scaledSiteConjugate N (flagSiteAction hD g⁻¹ z)) (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,← sub_div,abs_div,abs_of_pos hN,← add_div] at h
  change |flagSignalDifference hD g θ N z| ≤ _ at h
  calc
    _ ≤ _ := h
    _ ≤ L*(Q/N) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (hdisp z) hN.le) hL
    _ = _ := (mul_div_assoc _ _ _).symm

theorem flagMeanSignal_outside {a m D : ℕ} {v : ℝ×ℝ}
    (θ : (ℝ×ℝ) → ℝ) {q K N : ℝ} (hN : 0<N)
    (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (z : FlagSite a m D v)
    (hz : z∉flagSiteBox (N*K)) : flagMeanSignal θ N z=q := by
  apply hcompact
  by_contra hh
  have hh' : ‖scaledSiteConjugate N z‖<K := lt_of_not_ge hh
  have h₁ := norm_fst_le (scaledSiteConjugate N z)
  have h₂ := norm_snd_le (scaledSiteConjugate N z)
  simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos hN] at h₁ h₂
  apply hz
  constructor
  · have h := (div_lt_iff₀ hN).mp (h₁.trans_lt hh'); nlinarith
  · have h := (div_lt_iff₀ hN).mp (h₂.trans_lt hh'); nlinarith

theorem flagSignalDifference_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) {q K N : ℝ} (hK : 0<K) (hN : 0<N)
    (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (z : FlagSite a m D v)
    (hz : z∉flagSignalSupport hD g hK hN) : flagSignalDifference hD g θ N z=0 := by
  have hpair : z∉flagSiteBox (N*K) ∧ flagSiteAction hD g⁻¹ z∉flagSiteBox (N*K) := by
    have hn : z∉(flagSiteBox_finite (v:=v) hD (mul_pos hN hK)).toFinset ∧
        z∉((flagSiteBox_finite (v:=v) hD (mul_pos hN hK)).toFinset.image (flagSiteAction hD g)) := by
      simpa only [flagSignalSupport,Finset.mem_union,not_or] using hz
    refine ⟨?_,?_⟩
    · simpa only [Set.Finite.mem_toFinset] using hn.1
    · intro hh
      apply hn.2
      apply Finset.mem_image.mpr
      refine ⟨flagSiteAction hD g⁻¹ z,(Set.Finite.mem_toFinset _).mpr hh,?_⟩
      rw [← flagSiteAction_mul,mul_inv_cancel,flagSiteAction_one]
  simp only [flagSignalDifference,flagMeanSignal_outside θ hN hcompact z hpair.1,
    flagMeanSignal_outside θ hN hcompact _ hpair.2,sub_self]

theorem flagSignalSupport_card {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) {K N : ℝ} (hK : 0<K) (hN : 0<N) (hN₁ : 1≤N) :
    ((flagSignalSupport (v:=v) hD g hK hN).card:ℝ) ≤
      2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*N^2 := by
  let S := (flagSiteBox_finite (a:=a) (m:=m) (v:=v) hD (mul_pos hN hK)).toFinset
  have hc : ((flagSignalSupport (v:=v) hD g hK hN).card:ℝ) ≤ 2*(S.card:ℝ) := by
    have hh := (Finset.card_union_le S (S.image (flagSiteAction hD g))).trans
      (Nat.add_le_add_left (Finset.card_image_le) S.card)
    change (S∪S.image (flagSiteAction hD g)).card ≤ S.card+S.card at hh
    have hh' : (((S∪S.image (flagSiteAction hD g)).card:ℝ)) ≤ (S.card:ℝ)+(S.card:ℝ) := by exact_mod_cast hh
    change ((S∪S.image (flagSiteAction hD g)).card:ℝ) ≤ 2*(S.card:ℝ)
    simpa only [← two_mul] using hh'
  have hb := flagSiteBox_card_bound hD (mul_pos hN hK) S
    (fun z hz => (Set.Finite.mem_toFinset _).mp hz)
  have hn : 2*(D:ℝ)^2*(N*K)+2 ≤ (2*(D:ℝ)^2*K+2)*N := by nlinarith
  calc
    _ ≤ 2*(S.card:ℝ) := hc
    _ ≤ 2*((m:ℝ)*(2*(D:ℝ)^2*(N*K)+2)^2) := by linarith
    _ ≤ 2*((m:ℝ)*((2*(D:ℝ)^2*K+2)*N)^2) := by gcongr
    _ = _ := by ring

theorem flagSignalDifference_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (θ : (ℝ×ℝ) → ℝ) {q K L : ℝ}
    (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → θ x=q) (hL : 0≤L)
    (hLip : ∀x y,|θ x-θ y| ≤ L*(|x.1-y.1|+|x.2-y.2|)) :
    ∃C : ℝ,0≤C ∧ ∀N : ℝ,1≤N → ∀T : Finset (FlagSite a m D v),
      ∑z∈T,(flagSignalDifference hD g θ N z)^2 ≤ C := by
  obtain ⟨B,hB,hamp⟩ := flagSignalDifference_amplitude (v:=v) hD g θ hL hLip
  refine ⟨2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*B^2,by positivity,fun N hN T => ?_⟩
  have hN₀ : 0<N := lt_of_lt_of_le zero_lt_one hN
  let S := flagSignalSupport (v:=v) hD g hK hN₀
  have hsub : ∑z∈T,(flagSignalDifference hD g θ N z)^2 ≤ ∑z∈S,(flagSignalDifference hD g θ N z)^2 := by
    calc
      _ = ∑z∈T∩S,(flagSignalDifference hD g θ N z)^2 := by
        symm
        apply Finset.sum_subset Finset.inter_subset_left
        intro z hz hnot
        have hzS : z∉S := by simpa only [Finset.mem_inter,hz,true_and] using hnot
        rw [flagSignalDifference_support hD g θ hK hN₀ hcompact z hzS]
        norm_num
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        (fun _ _ _ => sq_nonneg _)
  have hb (z : FlagSite a m D v) : (flagSignalDifference hD g θ N z)^2 ≤ (B/N)^2 :=
    by
      have hh := (sq_le_sq₀ (abs_nonneg _) (div_nonneg hB hN₀.le)).mpr (hamp N hN₀ z)
      simpa only [sq_abs] using hh
  calc
    _ ≤ ∑z∈S,(flagSignalDifference hD g θ N z)^2 := hsub
    _ ≤ ∑_z∈S,(B/N)^2 := Finset.sum_le_sum (fun z _ => hb z)
    _ = (S.card:ℝ)*(B/N)^2 := by simp
    _ ≤ (2*(m:ℝ)*(2*(D:ℝ)^2*K+2)^2*N^2)*(B/N)^2 :=
      mul_le_mul_of_nonneg_right (flagSignalSupport_card hD g hK hN₀ hN) (sq_nonneg _)
    _ = _ := by field_simp

end FlagSignalEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalGoodRows
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

section SignalActiveBox
open Classical

theorem flagAveragingMatrix_box_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {L N : ℝ} (hL : 0<L) (hN : 0<N)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) (ρ r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : z∉flagBoxFinset hD (mul_pos hN hL) ∨ w∉flagBoxFinset hD (mul_pos hN hL)) :
    flagAveragingMatrix χ ρ N r η κ z w=0 := by
  rcases hz with hz | hw
  · exact flagAveragingMatrix_cutoff_left χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc z (by simpa only [mem_flagBoxFinset] using hz))
  · exact flagAveragingMatrix_cutoff_right χ ρ N r η κ z w
      (flagMeanSignal_outside χ hN hχc w (by simpa only [mem_flagBoxFinset] using hw))

end SignalActiveBox

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonApproxIdentity
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

section FiniteResolvent
open Classical Matrix

theorem finiteL2Norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ finiteL2Norm x := norm_nonneg _

theorem finiteL2Norm_sq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    finiteL2Norm x^2=∑i,x i^2 := by
  simp [finiteL2Norm,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs]

theorem finiteL2Norm_add {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    finiteL2Norm (x+y) ≤ finiteL2Norm x+finiteL2Norm y := by
  simpa only [finiteL2Norm,WithLp.toLp_add] using norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

theorem finiteL2Norm_sub {ι : Type*} [Fintype ι] (x y : ι → ℝ) :
    finiteL2Norm (x-y) ≤ finiteL2Norm x+finiteL2Norm y := by
  simpa only [finiteL2Norm,WithLp.toLp_sub] using norm_sub_le (WithLp.toLp 2 x) (WithLp.toLp 2 y)

theorem finiteL2Norm_smul {ι : Type*} [Fintype ι] (c : ℝ) (x : ι → ℝ) :
    finiteL2Norm (c • x)=|c| * finiteL2Norm x := by
  simp only [finiteL2Norm,WithLp.toLp_smul,norm_smul,Real.norm_eq_abs]

theorem finiteL2Norm_one_add_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (x : ι → ℝ) :
    finiteL2Norm x ≤ finiteL2Norm ((1+B)*ᵥx) := by
  let y := (1+B)*ᵥx
  let S := ∑i,x i^2
  let T := ∑i,y i^2
  let P := ∑i,x i*y i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hT : 0 ≤ T := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hp : 0 ≤ ∑i,x i*(B*ᵥx) i := by
    simpa only [dotProduct,star_trivial] using hB.dotProduct_mulVec_nonneg x
  have he : P=S+(∑i,x i*(B*ᵥx) i) := by
    simp only [P,S,y,Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply,mul_add,Finset.sum_add_distrib,pow_two]
  have hSP : S ≤ P := by linarith
  have hP : 0 ≤ P := hS.trans hSP
  have hcs : P^2 ≤ S*T := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
  have hST : S ≤ T := by
    by_cases h : S=0
    · simpa only [h] using hT
    · have hS' : 0<S := lt_of_le_of_ne hS (Ne.symm h)
      have hsq := pow_le_pow_left₀ hS hSP 2
      nlinarith
  apply (sq_le_sq₀ (finiteL2Norm_nonneg _) (finiteL2Norm_nonneg _)).mp
  simpa only [finiteL2Norm_sq] using hST

theorem one_add_psd_isUnit_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) : IsUnit (1+B).det :=
  (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.one.add_posSemidef hB).isUnit

theorem finiteL2Norm_inverse_contraction {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (x : ι → ℝ) :
    finiteL2Norm ((1+B)⁻¹*ᵥx) ≤ finiteL2Norm x := by
  have hh := finiteL2Norm_one_add_le B hB ((1+B)⁻¹*ᵥx)
  rwa [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (one_add_psd_isUnit_det B hB),Matrix.one_mulVec] at hh

theorem finiteL2Norm_inverse_signal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (W : ℝ) (hW : 0 ≤ W) (h : ι → ℝ) :
    finiteL2Norm ((1+B)⁻¹*ᵥh) ≤
      (finiteL2Norm h+finiteL2Norm (B*ᵥh-W • h))/(1+W) := by
  let C := (1+B)⁻¹
  let e := B*ᵥh-W • h
  have hid : C*ᵥ((1+B)*ᵥh)=h := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (one_add_psd_isUnit_det B hB),Matrix.one_mulVec]
  have he : (1+B)*ᵥh=(1+W) • h+e := by
    ext i
    simp only [Matrix.add_mulVec,Matrix.one_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul,e,Pi.sub_apply]
    ring
  rw [he,Matrix.mulVec_add,Matrix.mulVec_smul] at hid
  have he' : (1+W) • (C*ᵥh)=h-C*ᵥe := by
    exact eq_sub_iff_add_eq.mpr hid
  have hb := finiteL2Norm_sub h (C*ᵥe)
  rw [← he',finiteL2Norm_smul,abs_of_pos (show 0<1+W by linarith)] at hb
  have hc := finiteL2Norm_inverse_contraction B hB e
  apply (le_div_iff₀ (show 0<1+W by linarith)).mpr
  change finiteL2Norm (C*ᵥh)*(1+W) ≤ finiteL2Norm h+finiteL2Norm e
  nlinarith

end FiniteResolvent

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CompactSignalEnergy
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section CompactSignalEnergy
open Classical

theorem compactSignal_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) (q : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀N : ℝ,1≤N → ∀T : Finset (FlagSite a m D v),
      ∑z∈T,(flagSignalDifference hD g (fun x => q+ψ x) N z)^2 ≤ C^2 := by
  obtain ⟨K,hK,hcompact⟩ := hs.exists_pos_le_norm
  obtain ⟨L₀,L₁,hL₀,hL₁⟩ := compactSignal_uniform_constants ψ hψ hs
  obtain ⟨C,hC,henergy⟩ := flagSignalDifference_energy (v:=v) hD g (fun x => q+ψ x) hK
    (by intro x hx; rw [hcompact x hx,add_zero]) L₀.coe_nonneg (by
      intro x y
      simp only [add_sub_add_left_eq_sub]
      have hh := hL₀.dist_le_mul x y
      rw [Real.dist_eq,dist_eq_norm,Prod.norm_def] at hh
      refine hh.trans (mul_le_mul_of_nonneg_left ?_ L₀.coe_nonneg)
      simp only [Prod.fst_sub,Prod.snd_sub,Real.norm_eq_abs]
      exact max_le (le_add_of_nonneg_right (abs_nonneg _)) (le_add_of_nonneg_left (abs_nonneg _)))
  refine ⟨Real.sqrt C,Real.sqrt_nonneg _,?_⟩
  simpa only [Real.sq_sqrt hC] using henergy

end CompactSignalEnergy

section SourceSignalScales
open Classical Filter
open scoped Topology

theorem sourceDyadicWeight_nonneg (n : ℕ) : 0 ≤ sourceDyadicWeight n :=
  Real.rpow_nonneg (Real.log_nonneg (sourceDyadicN_one_le n)) _

theorem sourceDyadicMass_nonneg (n : ℕ) : 0 ≤ sourceDyadicMass n :=
  mul_nonneg (sourceDyadicWeight_nonneg n) (Nat.cast_nonneg _)

theorem sourceDyadicMass_tendsto : Tendsto sourceDyadicMass atTop atTop := by
  let c := (4*Real.log 2)^(-3/4:ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have ht : Tendsto (fun n : ℕ => c*(n:ℝ)^(1/4:ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (show (0:ℝ)<1/4 by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))).const_mul_atTop hc
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn' : (0:ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hw : sourceDyadicWeight n=c*(n:ℝ)^(-3/4:ℝ) := by
    unfold sourceDyadicWeight
    rw [sourceDyadic_log,Real.mul_rpow (by positivity) (Nat.cast_nonneg n)]
  have he : (n:ℝ)*(n:ℝ)^(-3/4:ℝ)=(n:ℝ)^(1/4:ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (n:ℝ)]
    rw [← Real.rpow_add hn']
    norm_num
  calc
    _ = sourceDyadicWeight n*(n:ℝ) := by rw [hw,← he]; ring
    _ ≤ _ := by
      unfold sourceDyadicMass
      rw [sourceDyadicIndices_card,Nat.cast_add,Nat.cast_one]
      exact mul_le_mul_of_nonneg_left (by linarith) (sourceDyadicWeight_nonneg n)

theorem sourceDyadic_radius_eventually (A : ℝ) :
    ∀ᶠn : ℕ in atTop,A ≤ (2:ℝ)^n :=
  (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 by norm_num)).eventually_ge_atTop A

theorem sourceDyadic_scale_bounds {n i : ℕ} (hi : i∈sourceDyadicIndices n) :
    1 ≤ (2:ℝ)^i ∧ (2:ℝ)^i ≤ sourceDyadicN n ∧
      (2:ℝ)^i/sourceDyadicN n ≤ (1/4:ℝ)^n := by
  obtain ⟨hi₀,hi₁⟩ := Finset.mem_Icc.mp hi
  have hp := pow_le_pow_right₀ (show (1:ℝ)≤2 by norm_num) hi₁
  have hN : sourceDyadicN n=((2:ℝ)^(2*n))^2 := by
    unfold sourceDyadicN; rw [← pow_mul]; congr 1; omega
  have h4 : (4:ℝ)^n=(2:ℝ)^(2*n) := by rw [pow_mul]; norm_num
  refine ⟨one_le_pow₀ (by norm_num),?_,?_⟩
  · unfold sourceDyadicN
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  · calc
      _ ≤ (2:ℝ)^(2*n)/sourceDyadicN n := div_le_div_of_nonneg_right hp (sourceDyadicN_pos n).le
      _ = _ := by rw [hN,div_pow,one_pow,h4]; field_simp

end SourceSignalScales

section WeightedResolvent
open Classical Matrix

theorem finiteL2Norm_sum {ι α : Type*} [Fintype ι] (I : Finset α) (f : α → ι → ℝ) :
    finiteL2Norm (∑i∈I,f i) ≤ ∑i∈I,finiteL2Norm (f i) := by
  induction I using Finset.induction_on with
  | empty => simp [finiteL2Norm]
  | @insert i I hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (finiteL2Norm_add _ _).trans (add_le_add le_rfl ih)

theorem finite_weighted_resolvent {ι α : Type*} [Fintype ι] [DecidableEq ι]
    (I : Finset α) (M : α → Matrix ι ι ℝ) (hM : ∀i∈I,(M i).PosSemidef)
    {w E : ℝ} (hw : 0 ≤ w) (hE : 0 ≤ E) (h : ι → ℝ)
    (he : ∀i∈I,finiteL2Norm (M i*ᵥh-h) ≤ E) :
    let B := w • ∑i∈I,M i
    let W := w*(I.card:ℝ)
    finiteL2Norm ((1+B)⁻¹*ᵥh) ≤ finiteL2Norm h/(1+W)+E := by
  dsimp only
  let B := w • ∑i∈I,M i
  let W := w*(I.card:ℝ)
  have hB : B.PosSemidef := (Matrix.posSemidef_sum I hM).smul hw
  have hW : 0 ≤ W := mul_nonneg hw (Nat.cast_nonneg _)
  have herr : B*ᵥh-W • h = w • ∑i∈I,(M i*ᵥh-h) := by
    simp only [B,W,Matrix.smul_mulVec,Matrix.sum_mulVec,Finset.sum_sub_distrib,
      Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,smul_sub,smul_smul]
  have hb : finiteL2Norm (B*ᵥh-W • h) ≤ W*E := by
    rw [herr,finiteL2Norm_smul,abs_of_nonneg hw]
    calc
      _ ≤ w*(∑i∈I,finiteL2Norm (M i*ᵥh-h)) := mul_le_mul_of_nonneg_left (finiteL2Norm_sum _ _) hw
      _ ≤ w*(∑_i∈I,E) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum he) hw
      _ = _ := by simp [W,mul_assoc]
  change finiteL2Norm ((1+B)⁻¹*ᵥh) ≤ finiteL2Norm h/(1+W)+E
  have hi := finiteL2Norm_inverse_signal B hB W hW h
  refine hi.trans ?_
  rw [add_div]
  apply add_le_add le_rfl
  apply (div_le_iff₀ (show 0<1+W by linarith)).mpr
  exact hb.trans (by nlinarith)

end WeightedResolvent

section FiniteSupportEnergy
open Classical Matrix

theorem finite_support_error_energy {ι : Type*} (J T : Finset ι) (hJT : J⊆T)
    (M : Matrix ι ι ℝ) (h : ι → ℝ)
    (hcol : ∀x y,y∉J → M x y*h y=0)
    (e : ι → ℝ) (he : ∀x,e x=(∑y∈J,M x y*h y)-h x)
    (hesupp : ∀x,x∉J → e x=0) :
    finiteL2Norm ((fun (x y : T) => M x y)*ᵥ(fun x : T => h x)-(fun x : T => h x))^2=
      ∑x∈J,(e x)^2 := by
  have hsum (x : ι) : (∑y : T,M x y*h y)=∑y∈J,M x y*h y := by
    rw [Finset.sum_coe_sort T (fun y => M x y*h y)]
    exact (Finset.sum_subset hJT (fun y _ hy => hcol x y hy)).symm
  have herr (x : T) : (((fun (x y : T) => M x y)*ᵥ(fun x : T => h x))-
      (fun x : T => h x)) x=e x := by
    simp only [Pi.sub_apply,Matrix.mulVec,dotProduct,hsum,he]
  rw [finiteL2Norm_sq]
  simp_rw [herr]
  rw [Finset.sum_coe_sort T (fun x => (e x)^2)]
  exact (Finset.sum_subset hJT (fun x _ hx => by rw [hesupp x hx]; norm_num)).symm

theorem finiteL2Norm_le_of_energy {ι : Type*} [Fintype ι] {x : ι → ℝ} {A B c d : ℝ}
    (hA : 0≤A) (hB : 0≤B) (hc : 0 ≤ c) (hd : 0≤d)
    (he : finiteL2Norm x^2 ≤ A*c^2+B*d^2) :
    finiteL2Norm x ≤ Real.sqrt A*c+Real.sqrt B*d := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hnon : 0≤Real.sqrt A*c+Real.sqrt B*d := by positivity
  apply (sq_le_sq₀ (finiteL2Norm_nonneg _) hnon).mp
  refine he.trans ?_
  nlinarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg A) hc) (mul_nonneg (Real.sqrt_nonneg B) hd)]

end FiniteSupportEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_SignalRemainder
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PartitionArrow.arrows_finite _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.PolygonObject.Labelled.Cell.relabelIsoMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.Labelled.PointFiber.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.Labelled.instFintypeElemForallFinProdCutRingSupport _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.relabelMonoidal _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationBraided _root_.OAI.SimpleAmenable.PolygonObject.Labelled.translationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationBraided _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.evaluationMonoidal _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.fiberEmpty _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instBraidedLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFaithfulObjEvaluation _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instFintypeFiber _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instGroupoid _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instIsIso _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategory _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalCategoryStruct _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instMonoidalLabelledForget _root_.OAI.SimpleAmenable.PolygonObject.LabelledStage.UniformObject.instSymmetricCategory _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.TranslationFiltered.regular_filtered
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
section SourceSignalRemainder
open Classical Filter
open scoped Topology

theorem sourceSignalDelta_nonneg (D n : ℕ) (η : ℝ) : 0 ≤ sourceSignalDelta D η n := by
  unfold sourceSignalDelta; positivity

theorem sourceSignalDelta_tendsto {D : ℕ} (hD : 0<D) {η : ℝ} (hη : 0<η) :
    Tendsto (sourceSignalDelta D η) atTop (nhds 0) := by
  have ht := (tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<2 by norm_num)).atTop_mul_const hη
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have ht' := (Real.tendsto_sqrt_atTop.comp ht).const_mul_atTop hd
  have hh := ht'.inv_tendsto_atTop.const_mul 38880
  change Tendsto (fun n => 38880/((D:ℝ)*Real.sqrt ((2:ℝ)^n*η))) atTop (nhds 0)
  simpa only [div_eq_mul_inv,mul_zero,Function.comp_apply,Pi.inv_apply] using hh

theorem sourceSignalDelta_bound {D n i : ℕ} {η : ℝ} (hD : 0<D) (hη : 0<η)
    (hi : n ≤ i) : 38880/((D:ℝ)*Real.sqrt ((2:ℝ)^i*η)) ≤ sourceSignalDelta D η n := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) hη.le)) hd.le

theorem sourceSignalError_nonneg {A B Cv Ca Cr η κ : ℝ} (hCv : 0≤Cv) (hCa : 0≤Ca)
    (hCr : 0≤Cr) (hη : 0≤η) (D n : ℕ) : 0 ≤ sourceSignalError A B Cv Ca Cr η κ D n := by
  unfold sourceSignalError
  positivity [sourceSignalDelta_nonneg D n η]

theorem sourceSignalError_tendsto {D : ℕ} (hD : 0<D) (A B Cv Ca Cr κ : ℝ)
    {η : ℝ} (hη : 0<η) :
    Tendsto (sourceSignalError A B Cv Ca Cr η κ D) atTop
      (nhds (Real.sqrt A*Cv*η+Real.sqrt B*Cr*Ca*Real.sqrt κ)) := by
  have hδ := sourceSignalDelta_tendsto hD hη
  have hs : Tendsto (fun n : ℕ => (1/4:ℝ)^n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hh := ((hδ.const_add 1).const_mul (Cv*η) |>.add (hδ.const_mul Ca) |>.const_mul (Real.sqrt A)).add
    (((hs.const_add κ).sqrt.const_mul (Real.sqrt B)).mul_const (Cr*Ca))
  change Tendsto (fun n => Real.sqrt A*(Cv*η*(1+sourceSignalDelta D η n)+Ca*sourceSignalDelta D η n)+
    Real.sqrt B*Real.sqrt (κ+(1/4:ℝ)^n)*(Cr*Ca)) atTop _
  simpa only [mul_zero,add_zero,mul_one,mul_assoc,mul_left_comm,mul_comm] using hh

theorem sourceSignalBound_tendsto {D : ℕ} (hD : 0<D) (A B Cv Ca Cr C κ : ℝ)
    {η : ℝ} (hη : 0<η) :
    Tendsto (fun n => C/(1+sourceDyadicMass n)+sourceSignalError A B Cv Ca Cr η κ D n)
      atTop (nhds (Real.sqrt A*Cv*η+Real.sqrt B*Cr*Ca*Real.sqrt κ)) := by
  have hm : Tendsto (fun n => 1+sourceDyadicMass n) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith : ∀n,sourceDyadicMass n ≤ 1+sourceDyadicMass n) sourceDyadicMass_tendsto
  have ht := hm.inv_tendsto_atTop.const_mul C
  have ht' : Tendsto (fun n => C/(1+sourceDyadicMass n)) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Pi.inv_apply] using ht
  simpa only [zero_add] using ht'.add (sourceSignalError_tendsto hD A B Cv Ca Cr κ hη)

end SourceSignalRemainder

section PolygonSignalInverse
open Classical Filter Matrix
open scoped Topology

theorem sourceFlagMatrix_inverse_signal_oai {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (g : polygonFullGroup a m) (ψ χ : (ℝ×ℝ) → ℝ)
    (hψ : ContDiff ℝ 2 ψ) (hsψ : HasCompactSupport ψ) (q K L : ℝ)
    (hL : 0<L) (hKL : K+2 ≤ L)
    (hcompact : ∀x,K ≤ ‖x‖ → ψ x=0)
    (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    (hχ₁ : ∀x,‖x‖ ≤ K+2 → χ x=1)
    (hχc : ∀x,L ≤ ‖x‖ → χ x=0) :
    ∃C₁ C₂ : ℝ,0≤C₁ ∧ 0≤C₂ ∧ ∀η : ℝ,0<η → η≤1 → ∀κ : ℝ,0<κ →
      ∀ε : ℝ,0<ε → ∀ᶠn : ℕ in atTop,
        ∀T : Finset (FlagSite a m D v),
          flagBoxFinset hD (mul_pos (sourceDyadicN_pos n) hL)⊆T →
          finiteL2Norm (((1 : Matrix T T ℝ)+(Matrix.of (fun (z w : T) => sourceFlagMatrix (v:=v) χ ((D:ℝ)^4/5) η κ n z.val w.val)))⁻¹*ᵥ
            (fun z : T => flagSignalDifference (v:=v) hD g (fun x => q+ψ x) (sourceDyadicN n) z.val)) ≤
              C₁*η+C₂*Real.sqrt κ+ε := by
  obtain ⟨R,Q,Cv,Ca,hR,hQ,hCv,hCa,happrox⟩ :=
    polygon_signal_approx_identity (v:=v) hD g ψ χ hψ hsψ q K L hL hKL hcompact hχ hχ₁ hχc
  obtain ⟨C,hC,henergy⟩ := compactSignal_energy (v:=v) hD g ψ hψ hsψ q
  let A := flagVolumeConstant m D L
  let B := flagExceptionalConstant a m D L
  let Cr := flagRowSumConstant D
  have hA : 0≤A := by dsimp [A,flagVolumeConstant]; positivity
  have hB : 0≤B := by dsimp [B,flagExceptionalConstant]; positivity
  have hCr : 0≤Cr := by dsimp [Cr,flagRowSumConstant]; positivity
  refine ⟨Real.sqrt A*Cv,Real.sqrt B*Cr*Ca,by positivity,by positivity,
    fun η hη hη₁ κ hκ ε hε => ?_⟩
  have ht := sourceSignalBound_tendsto hD A B Cv Ca Cr C κ hη
  have ht' := ht.eventually_lt_const
    (show Real.sqrt A*Cv*η+Real.sqrt B*Cr*Ca*Real.sqrt κ <
      (Real.sqrt A*Cv)*η+(Real.sqrt B*Cr*Ca)*Real.sqrt κ+ε by linarith)
  filter_upwards [ht',sourceDyadic_radius_eventually Q,sourceDyadic_radius_eventually (36/η),
    sourceDyadic_fine_eventually (max R 1) hκ] with n hn hQN hrad hf
  intro T hJT
  let N := sourceDyadicN n
  have hN : 0<N := sourceDyadicN_pos n
  have hN₁ : 1≤N := sourceDyadicN_one_le n
  have h2N : (2:ℝ)^n≤N := by
    unfold N sourceDyadicN
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hQN' : Q≤N := hQN.trans h2N
  let J := flagBoxFinset (a:=a) (m:=m) (v:=v) hD (mul_pos hN hL)
  let h := flagSignalDifference (v:=v) hD g (fun x => q+ψ x) N
  let M : ℕ → Matrix T T ℝ := fun i => (fun (z w : T) => flagAveragingMatrix (a:=a) (m:=m) (D:=D) (v:=v) χ ((D:ℝ)^4/5) N ((2:ℝ)^i) η κ z.val w.val)
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have hρ : 0<(D:ℝ)^4/5 := by positivity
  have hM (i : ℕ) (hi : i∈sourceDyadicIndices n) : (M i).PosSemidef :=
    (flagAveragingMatrix_posSemidef χ hρ hN (by positivity) hκ).submatrix (fun z : T => z.val)
  have he (i : ℕ) (hi : i∈sourceDyadicIndices n) :
      finiteL2Norm (M i*ᵥ(fun z : T => h z)-(fun z : T => h z)) ≤
        sourceSignalError A B Cv Ca Cr η κ D n := by
    have his := sourceDyadic_scale_bounds hi
    have hiv := (Finset.mem_Icc.mp hi).1
    have hri : 36≤(2:ℝ)^i*η := by
      apply (div_le_iff₀ hη).mp
      exact hrad.trans (pow_le_pow_right₀ (by norm_num) hiv)
    have hfR := (le_max_left R 1).trans (hf i hi)
    have hf1 := (le_max_right R 1).trans (hf i hi)
    have hline : 1≤2*κ/((2:ℝ)^i/N) := by
      rw [mul_div_assoc]
      linarith
    obtain ⟨hesupp,herr⟩ := happrox N ((2:ℝ)^i) η κ hN₁ hQN' his.1 his.2.1 hη hη₁ hκ hri hline hfR
    let ei := fun z => (∑w∈J,flagAveragingMatrix χ ((D:ℝ)^4/5) N ((2:ℝ)^i) η κ z w*h w)-h z
    have hee := finite_support_error_energy J T hJT
      (flagAveragingMatrix χ ((D:ℝ)^4/5) N ((2:ℝ)^i) η κ) h
      (by
        intro z w hw
        rw [flagAveragingMatrix_box_support hD χ hL hN hχc _ _ _ _ z w (Or.inr hw),zero_mul])
      ei (fun _ => rfl) hesupp
    let δ := 38880/((D:ℝ)*Real.sqrt ((2:ℝ)^i*η))
    have hc : 0≤Cv*η*(1+δ)+Ca*δ := by dsimp [δ]; positivity
    have hκs : 0≤κ+(2:ℝ)^i/N := by positivity
    have hb : finiteL2Norm (M i*ᵥ(fun z : T => h z)-(fun z : T => h z)) ≤
        Real.sqrt A*(Cv*η*(1+δ)+Ca*δ)+Real.sqrt (B*(κ+(2:ℝ)^i/N))*(Cr*Ca) := by
      apply finiteL2Norm_le_of_energy hA (mul_nonneg hB hκs) hc (mul_nonneg hCr hCa)
      rw [hee]
      exact herr
    rw [Real.sqrt_mul hB] at hb
    refine hb.trans ?_
    have hd := sourceSignalDelta_bound hD hη hiv
    change δ ≤ sourceSignalDelta D η n at hd
    dsimp only [sourceSignalError]
    gcongr
    exact his.2.2
  have hs := finite_weighted_resolvent (sourceDyadicIndices n) M hM
    (sourceDyadicWeight_nonneg n) (sourceSignalError_nonneg hCv hCa hCr hη.le D n)
    (fun z : T => h z) he
  have hnorm : finiteL2Norm (fun z : T => h z) ≤ C := by
    apply (sq_le_sq₀ (finiteL2Norm_nonneg _) hC).mp
    rw [finiteL2Norm_sq]
    rw [show (∑i : T,h i.val^2) = ∑i∈T,h i^2 from Finset.sum_coe_sort T (fun i => h i^2)]
    exact henergy N hN₁ T
  have hmatrix : (sourceDyadicWeight n • ∑i∈sourceDyadicIndices n,M i)=
      (fun (z w : T) => sourceFlagMatrix (v:=v) χ ((D:ℝ)^4/5) η κ n z.val w.val) := by
    ext z w
    simp only [Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply]
    simp only [M,N,sourceFlagMatrix]
  dsimp only at hs
  rw [hmatrix] at hs
  change _ ≤ finiteL2Norm (fun z : T => h z)/(1+sourceDyadicMass n)+_ at hs
  refine hs.trans ((add_le_add ?_ le_rfl).trans hn.le)
  apply div_le_div_of_nonneg_right hnorm
  linarith [sourceDyadicMass_nonneg n]

end PolygonSignalInverse

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal_oai := @OAI.SimpleAmenable.sourceFlagMatrix_inverse_signal_oai
