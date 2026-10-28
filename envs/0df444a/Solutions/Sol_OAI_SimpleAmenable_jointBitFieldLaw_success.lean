-- Prove2me | solution 1 for OAI.SimpleAmenable.jointBitFieldLaw_success
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T04:50:37.506677+00:00
-- url     : https://prove2.me/submissions/6fb49dcf-6b46-4b46-9a21-19dcc1e6898b

import Mathlib
import Definitions.Def_OAIQ65Sa014

section
-- module Solutions.OAIQ065_SA.Compat
attribute [-instance] _root_.OAI.BarFiberProduct.prodBraided _root_.OAI.BarFiberProduct.prodSymmetric _root_.OAI.CoefficientNerve.alternating_preserves _root_.OAI.ConnectedProduct.connected_tensor _root_.OAI.FilteredNerve.connected _root_.OAI.FiniteFreeRep.finite_free _root_.OAI.GroupNerveCoordinates.connected _root_.OAI.GroupNerveCoordinates.zero_subsingleton _root_.OAI.HomologyAdditive.additive _root_.OAI.NerveHomotopy.homologyMap_isIso _root_.OAI.QuotientRegular.finite_regular_module _root_.OAI.RestrictedNerve.instIsMultiplicativeFunctorFinHAddNatOfNatFunctorCategory_solutions _root_.OAI.RestrictedNerve.restricted_groupoid _root_.OAI.RestrictedNerve.restricted_isIso _root_.OAI.RestrictedNerve.strings_braided _root_.OAI.RestrictedNerve.strings_inverse _root_.OAI.RestrictedNerve.strings_monoidal _root_.OAI.SimpleAmenable.PolygonGrid.instIsLocallyFiniteMeasureNatCount_solutions _root_.OAI.SimpleAmenable.RingCoinvariants.instAdditiveModuleCatMonoidAlgebraIntRepOfModuleMonoidAlgebra_solutions _root_.OAI.SimpleAmenable.fiveTrackPerfect _root_.OAI.TranslationFiltered.regular_filtered
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
end OAICompat434

end OAI
end

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

theorem sourceDyadicWeight_square (n : ℕ) :
    (sourceDyadicWeight n)^2=(4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ) := by
  have hb : 0 ≤ 4*Real.log 2 := by positivity
  unfold sourceDyadicWeight
  rw [sourceDyadic_log,← Real.rpow_mul_natCast (mul_nonneg hb (Nat.cast_nonneg n))]
  norm_num
  rw [Real.mul_rpow hb (Nat.cast_nonneg n)]

theorem sourceDyadicWeight_energy_bound {n : ℕ} (hn : 1 ≤ n) :
    ((sourceDyadicIndices n).card:ℝ)*(sourceDyadicWeight n)^2 ≤ 2*(4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-1/2:ℝ) := by
  have hn₀ : 0 < (n:ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn₁ : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [sourceDyadicIndices_card,Nat.cast_add,Nat.cast_one,sourceDyadicWeight_square]
  have hc : 0 ≤ (4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ) := by positivity
  have he : (n:ℝ)*(n:ℝ)^(-3/2:ℝ)=(n:ℝ)^(-1/2:ℝ) := by
    conv_lhs => lhs; rw [← Real.rpow_one (n:ℝ)]
    rw [← Real.rpow_add hn₀]
    norm_num
  calc
    _ ≤ (2*(n:ℝ))*((4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ)) :=
      mul_le_mul_of_nonneg_right (by linarith) hc
    _ = _ := by rw [show (2*(n:ℝ))*((4*Real.log 2)^(-3/2:ℝ)*(n:ℝ)^(-3/2:ℝ))=
        (2*(4*Real.log 2)^(-3/2:ℝ))*((n:ℝ)*(n:ℝ)^(-3/2:ℝ)) by ring,he]

theorem sourceDyadicWeight_energy_tendsto :
    Tendsto (fun n => ((sourceDyadicIndices n).card:ℝ)*(sourceDyadicWeight n)^2) atTop (nhds 0) := by
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(-1/2:ℝ)) atTop (nhds 0) := by
    convert (tendsto_rpow_neg_atTop (show (0:ℝ) < 1/2 by norm_num)).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ)) using 1
    all_goals try with_reducible_and_instances rfl
    norm_num
    rfl
  have ht' := ht.const_mul (2*(4*Real.log 2)^(-3/2:ℝ))
  simp only [mul_zero] at ht'
  apply squeeze_zero' (Eventually.of_forall (fun n => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))) _ ht'
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sourceDyadicWeight_energy_bound hn

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

section FlagWindowCounts
open Classical

theorem flagWindow_numerators {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    {x y : ℝ×ℝ} {B C : ℝ} (z : FlagSite a m D v) (hz : z∈flagWindow x y B C) :
    (flagSiteNumerator z).1∈cutRectangle (D*x.1) (D*y.1) (D*B) (D*C) ∧
    (flagSiteNumerator z).2∈cutRectangle (D*x.2) (D*y.2) (D*B) (D*C) := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  have he₁ := congrArg Prod.fst (flagSiteNumerator_spec z)
  have he₂ := congrArg Prod.snd (flagSiteNumerator_spec z)
  change ordinary (flagSiteNumerator z).1/(D:ℝ)=z.val.2.val.1 at he₁
  change ordinary (flagSiteNumerator z).2/(D:ℝ)=z.val.2.val.2 at he₂
  have ho₁ := hz.1
  have ho₂ := hz.2.1
  rw [← he₁] at ho₁
  rw [← he₂] at ho₂
  have hc₁ : y.1 ≤ conjugate (flagSiteNumerator z).1/(D:ℝ) ∧
      conjugate (flagSiteNumerator z).1/(D:ℝ)≤y.1+C := hz.2.2.1
  have hc₂ : y.2 ≤ conjugate (flagSiteNumerator z).2/(D:ℝ) ∧
      conjugate (flagSiteNumerator z).2/(D:ℝ)≤y.2+C := hz.2.2.2
  simp only [Set.mem_Icc,le_div_iff₀ hd,div_le_iff₀ hd] at ho₁ ho₂ hc₁ hc₂
  constructor <;> constructor <;> constructor <;> nlinarith

theorem flagWindow_card_bound {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (t : Fin m) {x y : ℝ×ℝ} {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (S : Finset (FlagSite a m D v)) (hT : ∀z∈S,z.val.1=t)
    (hS : ∀z∈S,z∈flagWindow x y B C) :
    (S.card:ℝ) ≤ ((D:ℝ)^2*B*C+2)^2 := by
  have hd : (0:ℝ)<D := by exact_mod_cast hD
  let T₁ := (cutRectangle_finite (D*x.1) (D*y.1) (D*B) (D*C) (mul_pos hd hC)).toFinset
  let T₂ := (cutRectangle_finite (D*x.2) (D*y.2) (D*B) (D*C) (mul_pos hd hC)).toFinset
  have hc₁ : (T₁.card:ℝ)<(D:ℝ)^2*B*C+2 := by
    have hh := cutRectangle_card_bound T₁ (D*x.1) (D*y.1) (D*B) (D*C)
      (mul_nonneg hd.le hB) (mul_pos hd hC) (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  have hc₂ : (T₂.card:ℝ)<(D:ℝ)^2*B*C+2 := by
    have hh := cutRectangle_card_bound T₂ (D*x.2) (D*y.2) (D*B) (D*C)
      (mul_nonneg hd.le hB) (mul_pos hd hC) (fun u hu => (Set.Finite.mem_toFinset _).mp hu)
    nlinarith
  have hi : Set.InjOn (flagSiteNumerator (a:=a) (m:=m) (D:=D) (v:=v)) (↑S : Set (FlagSite a m D v)) := by
    intro z hz w hw hn
    apply flagSite_key_injective
    exact Prod.ext ((hT z hz).trans (hT w hw).symm) hn
  have hn : S.card ≤ T₁.card*T₂.card := by
    rw [← Finset.card_image_of_injOn hi,← Finset.card_product]
    apply Finset.card_le_card
    intro n hn
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hn
    have hh := flagWindow_numerators hD z (hS z hz)
    simpa only [Finset.mem_product,T₁,T₂,Set.Finite.mem_toFinset] using hh
  have hn' : (S.card:ℝ) ≤ (T₁.card:ℝ)*(T₂.card:ℝ) := by exact_mod_cast hn
  calc
    (S.card:ℝ) ≤ (T₁.card:ℝ)*(T₂.card:ℝ) := hn'
    _ ≤ ((D:ℝ)^2*B*C+2)*((D:ℝ)^2*B*C+2) :=
      mul_le_mul hc₁.le hc₂.le (Nat.cast_nonneg _) (by positivity)
    _ = _ := (pow_two _).symm

end FlagWindowCounts

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

theorem thresholdLaw_isProbability {s κ : ℝ} (hs : 0 < s) (hκ : 0<κ) :
    IsProbabilityMeasure (thresholdLaw s κ) := by
  have hlt : κ/s<2*κ/s := by exact (div_lt_div_iff_of_pos_right hs).mpr (by linarith)
  have : IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (κ/s) (2*κ/s))) :=
    ProbabilityTheory.cond_isProbabilityMeasure_of_finite
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr hlt))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  unfold thresholdLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem separatorMatrix_bounds {a : ℕ} {v : ℝ×ℝ}
    (μ : Measure (Fin 4 → ℝ)) [IsProbabilityMeasure μ] (z w : SquareFlag a v) :
    0 ≤ separatorMatrix μ z w ∧ separatorMatrix μ z w≤1 := by
  rw [separatorMatrix_eq_measure]
  exact ⟨ENNReal.toReal_nonneg,measureReal_le_one⟩

end FlagSeparatorMatrices

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_NoiseTensor
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

section NoiseMoments
open Classical MeasureTheory

theorem noiseFactor_continuous {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f) (i : NoiseFactor) :
    Continuous (noiseFactor f i) := by
  have hc := hf.continuous
  have hd := hf.continuous_deriv le_rfl
  cases i <;> dsimp [noiseFactor] <;> fun_prop

theorem noiseFactor_compact {f : ℝ → ℝ} (hf : HasCompactSupport f) (i : NoiseFactor) :
    HasCompactSupport (noiseFactor f i) := by
  cases i
  · exact hf
  · exact hf.deriv
  · exact hf.mul_left
  · have hh : HasCompactSupport (fun x => f x/2) := by
      convert! (hf.mul_right (f':=fun _ => (2:ℝ)⁻¹)) using 1
      all_goals try with_reducible_and_instances rfl
    exact hf.deriv.mul_left.add hh

theorem noiseFactor_integrable_product {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (i j : NoiseFactor) :
    Integrable (fun x => noiseFactor f i x*noiseFactor f j x) :=
  ((noiseFactor_continuous hf i).mul (noiseFactor_continuous hf j)).integrable_of_hasCompactSupport
    (noiseFactor_compact hc i).mul_right

theorem noiseFactor_centered {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (he : Function.Even f) (i : NoiseFactor) (hi : i≠.base) :
    (∫x : ℝ,noiseFactor f i x*f x)=0 := by
  have hd (x : ℝ) : HasDerivAt f (deriv f x) x := (hf.differentiable (by norm_num) x).hasDerivAt
  have hff := noiseFactor_integrable_product hf hc .base .base
  have hfd := noiseFactor_integrable_product hf hc .base .score
  have hdf := noiseFactor_integrable_product hf hc .score .base
  dsimp only [noiseFactor] at hff hfd hdf
  cases i
  · exact (hi rfl).elim
  · have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hd x) (fun x _ => hd x) hfd hdf hff
    have heq : (∫x : ℝ,f x*deriv f x)=(∫x : ℝ,deriv f x*f x) := by
      congr 1
      funext x
      ring
    dsimp [noiseFactor] at h ⊢
    linarith
  · have h := integral_neg_eq_self (fun x : ℝ => x*f x*f x) volume
    have heq : (fun x : ℝ => (-x)*f (-x)*f (-x))=(fun x : ℝ => -(x*f x*f x)) := by
      funext x
      rw [he x]
      ring
    change (∫x : ℝ,(-x)*f (-x)*f (-x))=(∫x : ℝ,x*f x*f x) at h
    rw [heq,integral_neg] at h
    dsimp [noiseFactor]
    linarith
  · have hup (x : ℝ) : HasDerivAt (fun x => x*f x) (f x+x*deriv f x) x := by
      convert! (hasDerivAt_id x).mul (hd x) using 1; simp only [one_mul,id_eq]
    have hp := noiseFactor_integrable_product hf hc .position .score
    have hp₀ := noiseFactor_integrable_product hf hc .position .base
    dsimp only [noiseFactor] at hp hp₀
    have hp' : Integrable (fun x : ℝ => (f x+x*deriv f x)*f x) := by
      have hj := noiseFactor_integrable_product hf hc .diagonal .base
      apply (hj.add (hff.div_const 2)).congr
      filter_upwards with x
      dsimp [noiseFactor]
      ring
    have h := integral_mul_deriv_eq_deriv_mul_of_integrable
      (fun x _ => hup x) (fun x _ => hd x) hp hp' hp₀
    let I := ∫x : ℝ,x*f x*deriv f x
    have hright : (∫x : ℝ,(f x+x*deriv f x)*f x)=(∫x : ℝ,f x*f x)+I := by
      have hi : Integrable (fun x : ℝ => x*deriv f x*f x) := by
        apply hp.congr
        filter_upwards with x
        ring
      rw [show (fun x : ℝ => (f x+x*deriv f x)*f x)=
        (fun x : ℝ => f x*f x+x*deriv f x*f x) by ext x; ring,integral_add hff hi]
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      ring
    change I=-(∫x : ℝ,(f x+x*deriv f x)*f x) at h
    rw [hright] at h
    have hgoal : (∫x : ℝ,noiseFactor f .diagonal x*f x)=I+(∫x : ℝ,f x*f x)/2 := by
      have hi : Integrable (fun x : ℝ => x*f x*deriv f x) := hp
      have hb : Integrable (fun x : ℝ => (f x*f x)/2) := hff.div_const 2
      rw [show (fun x : ℝ => noiseFactor f .diagonal x*f x)=
        (fun x : ℝ => x*f x*deriv f x+(f x*f x)/2) by ext x; dsimp [noiseFactor]; ring,
        integral_add hi hb,integral_div]
    rw [hgoal]
    linarith

end NoiseMoments

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteOrthogonalEnergy
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

section SmoothNoise
open Classical MeasureTheory
open scoped ContDiff

theorem rawNoiseMass_pos : 0 < rawNoiseMass := by
  have hc : Continuous (fun x : ℝ => (rawNoiseBump x)^2) := rawNoiseBump.continuous.pow 2
  have hs : HasCompactSupport (fun x : ℝ => (rawNoiseBump x)^2) := by
    convert! rawNoiseBump.hasCompactSupport.mul_right (f':=rawNoiseBump) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [pow_two,Pi.mul_apply]
  apply integral_pos_of_integrable_nonneg_nonzero (x:=(0:ℝ)) hc (hc.integrable_of_hasCompactSupport hs)
    (fun _ => sq_nonneg _)
  have hh : rawNoiseBump (0 : ℝ)=1 := rawNoiseBump.one_of_mem_closedBall (by
    simp [rawNoiseBump])
  simp [hh]

theorem smoothNoiseRoot_even : Function.Even smoothNoiseRoot := by
  intro x
  simp only [smoothNoiseRoot,rawNoiseBump.neg]

theorem smoothNoiseRoot_contDiff : ContDiff ℝ ∞ smoothNoiseRoot :=
  rawNoiseBump.contDiff.div_const _

theorem smoothNoiseRoot_compact : HasCompactSupport smoothNoiseRoot := by
  convert! rawNoiseBump.hasCompactSupport.mul_right (f':=fun _ => (Real.sqrt rawNoiseMass)⁻¹) using 1
  all_goals try with_reducible_and_instances rfl

theorem smoothNoiseRoot_zero {x : ℝ} (hx : 1≤|x|) : smoothNoiseRoot x=0 := by
  rw [smoothNoiseRoot]
  have hh : rawNoiseBump x=0 := rawNoiseBump.zero_of_le_dist (by
    simpa only [rawNoiseBump,Real.dist_eq,sub_zero] using hx)
  rw [hh,zero_div]

theorem smoothNoiseRoot_normalized : (∫x : ℝ,smoothNoiseRoot x^2)=1 := by
  simp only [smoothNoiseRoot,div_pow]
  rw [integral_div,Real.sq_sqrt rawNoiseMass_pos.le]
  change rawNoiseMass/rawNoiseMass=1
  exact div_self rawNoiseMass_pos.ne'

end SmoothNoise

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AffineNoiseEnergy
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

section ActualNoiseLaw
open Classical MeasureTheory ProbabilityTheory
open scoped ContDiff ENNReal

theorem smoothNoiseDensity_measurable : Measurable smoothNoiseDensity :=
  (smoothNoiseRoot_contDiff.continuous.pow 2).measurable.ennreal_ofReal

instance smoothNoiseLaw_probability : IsProbabilityMeasure smoothNoiseLaw := by
  constructor
  rw [smoothNoiseLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  have hi : Integrable (fun x : ℝ => smoothNoiseRoot x^2) := by
    have hc := smoothNoiseRoot_contDiff.continuous.pow 2
    apply hc.integrable_of_hasCompactSupport
    convert! smoothNoiseRoot_compact.mul_right (f':=smoothNoiseRoot) using 1
    all_goals try with_reducible_and_instances rfl
    ext x
    simp only [Pi.mul_apply,pow_two]
  change (∫⁻x : ℝ,ENNReal.ofReal (smoothNoiseRoot x^2))=1
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => sq_nonneg _)),
    smoothNoiseRoot_normalized,ENNReal.ofReal_one]

theorem smoothNoiseLaw_bounded : ∀ᵐx ∂smoothNoiseLaw,x∈Set.Icc (-1:ℝ) 1 := by
  rw [smoothNoiseLaw,ae_withDensity_iff smoothNoiseDensity_measurable]
  filter_upwards with x hx
  by_contra h
  have hh : 1≤|x| := by
    have hn : ¬ |x|≤1 := by simpa only [abs_le,Set.mem_Icc] using h
    exact (lt_of_not_ge hn).le
  have hz := smoothNoiseRoot_zero hh
  exact hx (by simp [smoothNoiseDensity,hz])

theorem smoothNoiseLaw_centered : (∫x : ℝ,x ∂smoothNoiseLaw)=0 := by
  rw [smoothNoiseLaw,integral_withDensity_eq_integral_toReal_smul smoothNoiseDensity_measurable
    (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [smoothNoiseDensity,ENNReal.toReal_ofReal (sq_nonneg _),smul_eq_mul]
  have h := noiseFactor_centered (smoothNoiseRoot_contDiff.of_le (by norm_num))
    smoothNoiseRoot_compact smoothNoiseRoot_even .position (by decide)
  convert! h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ext x
  simp only [noiseFactor]
  ring

instance independentSmoothNoiseLaw_probability (ι : Type*) :
    IsProbabilityMeasure (independentSmoothNoiseLaw ι) := by
  unfold independentSmoothNoiseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

theorem independentSmoothNoiseLaw_independent (ι : Type*) :
    iIndepFun (fun (i : ι) (x : ι → ℝ) => x i) (independentSmoothNoiseLaw ι) :=
  iIndepFun_infinitePi (fun _ => measurable_id)

theorem independentSmoothNoiseLaw_map (ι : Type*) (i : ι) :
    (independentSmoothNoiseLaw ι).map (fun x => x i)=smoothNoiseLaw :=
  Measure.infinitePi_map_eval _ i

theorem independentSmoothNoiseLaw_bounded (ι : Type*) (i : ι) :
    ∀ᵐx ∂independentSmoothNoiseLaw ι,x i∈Set.Icc (-1:ℝ) 1 := by
  have hh := smoothNoiseLaw_bounded
  rw [← independentSmoothNoiseLaw_map ι i] at hh
  exact (ae_map_iff (measurable_pi_apply i).aemeasurable (by measurability)).mp hh

theorem independentSmoothNoiseLaw_centered (ι : Type*) (i : ι) :
    (∫x : ι → ℝ,x i ∂independentSmoothNoiseLaw ι)=0 := by
  have hh := smoothNoiseLaw_centered
  rw [← independentSmoothNoiseLaw_map ι i] at hh
  rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)] at hh
  exact hh

end ActualNoiseLaw

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

theorem planeTent_le_one (s : ℝ) (x y : ℝ×ℝ) : planeTent s x y ≤ 1 := by
  have h₁ : max (1-|(x.1-y.1)/s|) 0 ≤ 1 := max_le (by linarith [abs_nonneg ((x.1-y.1)/s)]) zero_le_one
  have h₂ : max (1-|(x.2-y.2)/s|) 0 ≤ 1 := max_le (by linarith [abs_nonneg ((x.2-y.2)/s)]) zero_le_one
  exact (mul_le_mul h₁ h₂ (le_max_right _ _) zero_le_one).trans_eq (one_mul 1)

theorem flagAveragingMatrix_cutoff_left {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ N r η κ : ℝ) (z w : FlagSite a m D v)
    (hz : χ (scaledSiteConjugate N z)=0) : flagAveragingMatrix χ ρ N r η κ z w=0 := by
  simp [flagAveragingMatrix,hz]

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

theorem flagAveragingMatrix_localization {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (ρ κ : ℝ) {N r η : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (z w : FlagSite a m D v)
    (hw : flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    w.val.1=z.val.1 ∧ w∈flagWindow
      (z.val.2.val.1-r/N,z.val.2.val.2-r/N)
      ((flagSiteConjugate z).1-N*η,(flagSiteConjugate z).2-N*η) (2*(r/N)) (2*(N*η)) := by
  have ht : z.val.1=w.val.1 := by
    by_contra hh
    simp [flagAveragingMatrix,hh] at hw
  have hk₁ : planeTent (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w) ≠ 0 := by
    intro he
    simp [flagAveragingMatrix,he] at hw
  have hk₂ : planeTent (N*η) (flagSiteConjugate z) (flagSiteConjugate w) ≠ 0 := by
    intro he
    simp [flagAveragingMatrix,he] at hw
  have hx := (planeTent_ne_zero (div_pos hr hN) _ _).mp hk₁
  have hy := (planeTent_ne_zero (mul_pos hN hη) _ _).mp hk₂
  have hx₁ := abs_lt.mp hx.1
  have hx₂ := abs_lt.mp hx.2
  have hy₁ := abs_lt.mp hy.1
  have hy₂ := abs_lt.mp hy.2
  refine ⟨ht.symm,?_,?_,?_,?_⟩ <;>
    simp only [flagSiteOrdinary] at hx₁ hx₂ <;> constructor <;> linarith

theorem flagAveragingMatrix_row_card {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (χ : (ℝ×ℝ) → ℝ) (ρ κ : ℝ) {N r η : ℝ} (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v))
    (hS : ∀w∈S,flagAveragingMatrix χ ρ N r η κ z w ≠ 0) :
    (S.card:ℝ) ≤ (4*(D:ℝ)^2*r*η+2)^2 := by
  have hloc := fun w hw => flagAveragingMatrix_localization χ ρ κ hN hr hη z w (hS w hw)
  have hc := flagWindow_card_bound hD z.val.1
    (show 0 ≤ 2*(r/N) by positivity) (show 0 < 2*(N*η) by positivity) S
    (fun w hw => (hloc w hw).1) (fun w hw => (hloc w hw).2)
  have he : (D:ℝ)^2*(2*(r/N))*(2*(N*η))+2=4*(D:ℝ)^2*r*η+2 := by
    field_simp
    ring
  rwa [he] at hc

theorem flagAveragingMatrix_entry_bounds {a m D : ℕ} {v : ℝ×ℝ}
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (hκ : 0 < κ) (z w : FlagSite a m D v) :
    0 ≤ flagAveragingMatrix χ ρ N r η κ z w ∧
    flagAveragingMatrix χ ρ N r η κ z w ≤ (ρ*(r*η)^2)⁻¹ := by
  have : IsProbabilityMeasure (thresholdLaw (r/N) κ) := thresholdLaw_isProbability (div_pos hr hN) hκ
  have hp := separatorMatrix_bounds (thresholdLaw (r/N) κ) z.val.2 w.val.2
  have hk₁ := planeTent_nonneg (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)
  have hk₂ := planeTent_nonneg (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hk₁' := planeTent_le_one (r/N) (flagSiteOrdinary z) (flagSiteOrdinary w)
  have hk₂' := planeTent_le_one (N*η) (flagSiteConjugate z) (flagSiteConjugate w)
  have hχz := hχ (scaledSiteConjugate N z)
  have hχw := hχ (scaledSiteConjugate N w)
  have hd : 0 < ρ*(r*η)^2 := mul_pos hρ (sq_pos_of_pos (mul_pos hr hη))
  unfold flagAveragingMatrix
  split_ifs
  · constructor
    · exact mul_nonneg (mul_nonneg (mul_nonneg
        (div_nonneg (mul_nonneg hχz.1 hχw.1) hd.le) hk₁) hk₂) hp.1
    · have hc : χ (scaledSiteConjugate N z)*χ (scaledSiteConjugate N w) ≤ 1 :=
        (mul_le_mul hχz.2 hχw.2 hχw.1 zero_le_one).trans_eq (one_mul 1)
      calc
        _ ≤ (1/(ρ*(r*η)^2))*1*1*1 := by gcongr <;> first | exact hp.1 | exact hp.2
        _ = _ := by ring
  · exact ⟨le_rfl,inv_nonneg.mpr hd.le⟩

theorem flagAveragingMatrix_row_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0 < D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0 < ρ) (hN : 0 < N) (hr : 0 < r)
    (hη : 0 < η) (hκ : 0 < κ) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑w∈S,(flagAveragingMatrix χ ρ N r η κ z w)^2 ≤
      (4*(D:ℝ)^2*r*η+2)^2 / (ρ*(r*η)^2)^2 := by
  let T := S.filter (fun w => flagAveragingMatrix χ ρ N r η κ z w ≠ 0)
  have he : (∑w∈S,(flagAveragingMatrix χ ρ N r η κ z w)^2)=
      ∑w∈T,(flagAveragingMatrix χ ρ N r η κ z w)^2 := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro w hw hwt
    have hh : flagAveragingMatrix χ ρ N r η κ z w=0 := by simpa [T,hw] using hwt
    simp [hh]
  rw [he]
  have hc := flagAveragingMatrix_row_card hD χ ρ κ hN hr hη z T
    (fun w hw => (Finset.mem_filter.mp hw).2)
  have hb (w : FlagSite a m D v) :
      (flagAveragingMatrix χ ρ N r η κ z w)^2 ≤ ((ρ*(r*η)^2)⁻¹)^2 := by
    have hh := flagAveragingMatrix_entry_bounds χ hχ hρ hN hr hη hκ z w
    exact pow_le_pow_left₀ hh.1 hh.2 2
  calc
    _ ≤ ∑_w∈T,((ρ*(r*η)^2)⁻¹)^2 := Finset.sum_le_sum (fun w _ => hb w)
    _ = (T.card:ℝ)*((ρ*(r*η)^2)⁻¹)^2 := by simp
    _ ≤ (4*(D:ℝ)^2*r*η+2)^2*((ρ*(r*η)^2)⁻¹)^2 :=
      mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by rw [div_eq_mul_inv,inv_pow]

end AveragingRowBounds

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_AveragingUniformCovariance
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

section FiniteCovarianceEnergy
open Classical

theorem finite_half_geometric_sum (I : Finset ℕ) :
    ∑i∈I,(1/2:ℝ)^i ≤ 2 := by
  have hi : I ⊆ Finset.range (I.sup id+1) := by
    intro i hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f:=id) hi))
  calc
    _ ≤ ∑i∈Finset.range (I.sup id+1),(1/2:ℝ)^i :=
      Finset.sum_le_sum_of_subset_of_nonneg hi (fun _ _ _ => by positivity)
    _ ≤ 2 := by
      have h := geom_sum_Ico_le_of_lt_one (m:=0) (n:=I.sup id+1)
        (show (0:ℝ) ≤ 1/2 by norm_num) (show (1/2:ℝ)<1 by norm_num)
      norm_num at h ⊢
      exact h

end FiniteCovarianceEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteFieldConcentration
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
section FiniteFieldConcentration
open Classical MeasureTheory ProbabilityTheory
open scoped NNReal

theorem subgaussian_parameter_mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c d : ℝ≥0} (h : HasSubgaussianMGF X c μ) (hcd : c≤d) :
    HasSubgaussianMGF X d μ where
  integrable_exp_mul := h.integrable_exp_mul
  mgf_le t := (h.mgf_le t).trans (Real.exp_le_exp.mpr (by
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hcd) (sq_nonneg t)) (by norm_num)))

theorem finite_weighted_noise_tail {Ω ι : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (hind : iIndepFun X μ)
    (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
    (hc : ∀i,∫ω,X i ω ∂μ=0) (S : Finset ι) (b : ι → ℝ)
    {V ε : ℝ} (hV : 0≤V) (he : ∑i∈S,(b i)^2 ≤ V) (hε : 0≤ε) :
    μ.real {ω | ε ≤ |∑i∈S,b i*X i ω|} ≤ 2*Real.exp (-ε^2/(2*V)) := by
  have hsub (i : ι) : HasSubgaussianMGF (X i) 1 μ := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (hm i) (hb i) (hc i)
    norm_num at h
    exact h
  have hi := hind.comp (fun i x => b i*x) (fun i => measurable_const.mul measurable_id)
  have hs : HasSubgaussianMGF (fun ω => ∑i∈S,b i*X i ω)
      (∑i∈S,NNReal.mk ((b i)^2) (sq_nonneg _)) μ := by
    apply HasSubgaussianMGF.sum_of_iIndepFun hi
    intro i hi
    have h := (hsub i).const_mul (b i)
    change HasSubgaussianMGF (fun ω => b i*X i ω) ((NNReal.mk ((b i)^2) (sq_nonneg _))*1) μ at h
    simpa only [mul_one,Function.comp_def] using h
  have hv : HasSubgaussianMGF (fun ω => ∑i∈S,b i*X i ω) (NNReal.mk V hV) μ := by
    apply subgaussian_parameter_mono hs
    apply NNReal.coe_le_coe.mp
    simpa only [NNReal.coe_sum,NNReal.coe_mk] using he
  have hset : {ω | ε ≤ |∑i∈S,b i*X i ω|} ⊆
      {ω | ε ≤ ∑i∈S,b i*X i ω} ∪ {ω | ε ≤ -(∑i∈S,b i*X i ω)} := by
    intro ω hω
    change ε ≤ |∑i∈S,b i*X i ω| at hω
    rcases le_abs.mp hω with h|h
    · exact Or.inl h
    · exact Or.inr h
  have hh := (measureReal_mono (μ:=μ) hset).trans (measureReal_union_le _ _)
  have hpos := hv.measure_ge_le hε
  have hneg := hv.neg.measure_ge_le hε
  dsimp at hpos hneg
  linarith

theorem finite_matrix_noise_tail {Ω ι ζ : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : ι → Ω → ℝ) (hind : iIndepFun X μ)
    (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
    (hc : ∀i,∫ω,X i ω ∂μ=0) (S : Finset ι) (T : Finset ζ) (B : ζ → ι → ℝ)
    {V ε : ℝ} (hV : 0≤V) (he : ∀z∈T,∑i∈S,(B z i)^2 ≤ V) (hε : 0≤ε) :
    μ.real {ω | ∃z∈T,ε ≤ |∑i∈S,B z i*X i ω|} ≤
      2*(T.card:ℝ)*Real.exp (-ε^2/(2*V)) := by
  have heq : {ω | ∃z∈T,ε ≤ |∑i∈S,B z i*X i ω|}=
      ⋃z∈T,{ω | ε ≤ |∑i∈S,B z i*X i ω|} := by ext; simp
  rw [heq]
  calc
    _ ≤ ∑z∈T,μ.real {ω | ε ≤ |∑i∈S,B z i*X i ω|} := measureReal_biUnion_finset_le _ _
    _ ≤ ∑_z∈T,2*Real.exp (-ε^2/(2*V)) := Finset.sum_le_sum (fun z hz =>
      finite_weighted_noise_tail μ X hind hm hb hc S (B z) hV (he z hz) hε)
    _ = _ := by simp; ring

end FiniteFieldConcentration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_PolygonCovarianceEnergy
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

section PolygonDyadicRowEnergy
open Classical

theorem finite_sum_row_energy {α ι : Type*} (S : Finset α) (I : Finset ι)
    (f : ι → α → ℝ) (b : ι → ℝ) (hb : ∀i∈I,0 ≤ b i)
    (he : ∀i∈I,∑x∈S,(f i x)^2 ≤ (b i)^2) :
    ∑x∈S,(∑i∈I,f i x)^2 ≤ (∑i∈I,b i)^2 := by
  have hpair (i j : ι) (hi : i∈I) (hj : j∈I) : ∑x∈S,f i x*f j x ≤ b i*b j := by
    apply le_of_sq_le_sq _ (mul_nonneg (hb i hi) (hb j hj))
    calc
      _ ≤ (∑x∈S,(f i x)^2)*(∑x∈S,(f j x)^2) := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
      _ ≤ (b i)^2*(b j)^2 := mul_le_mul (he i hi) (he j hj)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
      _ = _ := (mul_pow _ _ _).symm
  calc
    _ = ∑i∈I,∑j∈I,∑x∈S,f i x*f j x := by
      simp_rw [pow_two,Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ ≤ ∑i∈I,∑j∈I,b i*b j :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hpair i j hi hj))
    _ = _ := by rw [pow_two,Finset.sum_mul_sum]

theorem finite_half_geometric_tail (I : Finset ℕ) (n : ℕ) (hn : ∀i∈I,n ≤ i) :
    ∑i∈I,(1/2:ℝ)^i ≤ 2*(1/2:ℝ)^n := by
  have hi : Set.InjOn (fun i => i-n) I := by
    intro i hi j hj he
    have hi₀ := hn i hi
    have hj₀ := hn j hj
    change i-n=j-n at he
    omega
  have he : (∑i∈I,(1/2:ℝ)^i)=(1/2:ℝ)^n*(∑j∈I.image (fun i => i-n),(1/2:ℝ)^j) := by
    rw [Finset.sum_image hi,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [← pow_add,Nat.add_sub_of_le (hn i hi)]
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (finite_half_geometric_sum (I.image (fun i => i-n)))
    (pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n)
  simpa [mul_comm] using hh

theorem flagAveragingMatrix_row_energy_uniform {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N r η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hr : 1 ≤ r)
    (hη : 0<η) (hκ : 0<κ) (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑y∈S,(flagAveragingMatrix χ ρ N r η κ z y)^2 ≤ (flagRowConstant D ρ η/r)^2 := by
  have hr₀ : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hd : 0<ρ*(r*η)^2 := by positivity
  have hn : 4*(D:ℝ)^2*r*η+2 ≤ (4*(D:ℝ)^2*η+2)*r := by nlinarith
  calc
    _ ≤ (4*(D:ℝ)^2*r*η+2)^2/(ρ*(r*η)^2)^2 :=
      flagAveragingMatrix_row_energy hD χ hχ hρ hN hr₀ hη hκ z S
    _ ≤ ((4*(D:ℝ)^2*η+2)*r)^2/(ρ*(r*η)^2)^2 := by
      gcongr
    _ = _ := by unfold flagRowConstant; field_simp

theorem flagAveragingMatrix_dyadic_row_energy {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {ρ N η κ : ℝ} (hρ : 0<ρ) (hN : 0<N) (hη : 0<η) (hκ : 0<κ)
    (I : Finset ℕ) (n : ℕ) (hn : ∀i∈I,n ≤ i) (w : ℝ)
    (z : FlagSite a m D v) (S : Finset (FlagSite a m D v)) :
    ∑y∈S,(w*∑i∈I,flagAveragingMatrix χ ρ N ((2:ℝ)^i) η κ z y)^2 ≤
      (2*flagRowConstant D ρ η*w/(2:ℝ)^n)^2 := by
  have hC : 0 ≤ flagRowConstant D ρ η := by unfold flagRowConstant; positivity
  have hei := finite_sum_row_energy S I
    (fun i y => flagAveragingMatrix χ ρ N ((2:ℝ)^i) η κ z y)
    (fun i => flagRowConstant D ρ η/(2:ℝ)^i)
    (by intro i hi; positivity)
    (fun i _ => flagAveragingMatrix_row_energy_uniform hD χ hχ hρ hN
      (one_le_pow₀ (by norm_num)) hη hκ z S)
  have hsum : ∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i ≤ 2*flagRowConstant D ρ η/(2:ℝ)^n := by
    have h : (∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i)=flagRowConstant D ρ η*(∑i∈I,(1/2:ℝ)^i) := by
      simp [Finset.mul_sum,div_eq_mul_inv]
    rw [h]
    have hh := mul_le_mul_of_nonneg_left (finite_half_geometric_tail I n hn) hC
    simpa [div_pow,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hsum₀ : 0 ≤ ∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  calc
    _ = w^2*(∑y∈S,(∑i∈I,flagAveragingMatrix χ ρ N ((2:ℝ)^i) η κ z y)^2) := by
      simp_rw [mul_pow,Finset.mul_sum]
    _ ≤ w^2*(∑i∈I,flagRowConstant D ρ η/(2:ℝ)^i)^2 :=
      mul_le_mul_of_nonneg_left hei (sq_nonneg _)
    _ ≤ w^2*(2*flagRowConstant D ρ η/(2:ℝ)^n)^2 := by gcongr
    _ = _ := by ring

end PolygonDyadicRowEnergy

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_CovarianceLimit
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

section SourceFieldConcentration
open Classical Filter MeasureTheory ProbabilityTheory
open scoped Topology

theorem sourceFlagMatrix_support {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) {K : ℝ} (hK : 0<K)
    (hcompact : ∀x,K ≤ ‖x‖ → χ x=0) (ρ η κ : ℝ) (n : ℕ)
    (z y : FlagSite a m D v) (hz : z∉sourceActiveSites (v:=v) hD hK n) :
    sourceFlagMatrix χ ρ η κ n z y=0 := by
  have hnot : ¬z∈flagSiteBox (sourceDyadicN n*K) := by
    simpa only [sourceActiveSites,Set.Finite.mem_toFinset] using hz
  have hc : χ (scaledSiteConjugate (sourceDyadicN n) z)=0 := by
    apply hcompact
    by_contra hh
    have hh' : ‖scaledSiteConjugate (sourceDyadicN n) z‖<K := lt_of_not_ge hh
    have h₁ := norm_fst_le (scaledSiteConjugate (sourceDyadicN n) z)
    have h₂ := norm_snd_le (scaledSiteConjugate (sourceDyadicN n) z)
    simp only [scaledSiteConjugate,Real.norm_eq_abs,abs_div,abs_of_pos (sourceDyadicN_pos n)] at h₁ h₂
    apply hnot
    constructor
    · have h := (div_lt_iff₀ (sourceDyadicN_pos n)).mp (h₁.trans_lt hh'); nlinarith
    · have h := (div_lt_iff₀ (sourceDyadicN_pos n)).mp (h₂.trans_lt hh'); nlinarith
  simp only [sourceFlagMatrix,flagAveragingMatrix_cutoff_left χ _ _ _ _ _ z y hc,
    Finset.sum_const_zero,mul_zero]

theorem sourceActiveSites_card {a m D : ℕ} {v : ℝ×ℝ}
    (hD : 0<D) {K : ℝ} (hK : 0<K) (n : ℕ) :
    ((sourceActiveSites (a:=a) (m:=m) (v:=v) hD hK n).card:ℝ) ≤
      (m:ℝ)*(2*(D:ℝ)^2*K+2)^2*(sourceDyadicN n)^2 := by
  have hc := flagSiteBox_card_bound (a:=a) (m:=m) (v:=v) hD
    (mul_pos (sourceDyadicN_pos n) hK) (sourceActiveSites hD hK n)
    (fun z hz => (Set.Finite.mem_toFinset _).mp hz)
  have hN := sourceDyadicN_one_le n
  have hp : 2*(D:ℝ)^2*(sourceDyadicN n*K)+2 ≤ (2*(D:ℝ)^2*K+2)*sourceDyadicN n := by
    nlinarith
  calc
    _ ≤ (m:ℝ)*(2*(D:ℝ)^2*(sourceDyadicN n*K)+2)^2 := hc
    _ ≤ (m:ℝ)*((2*(D:ℝ)^2*K+2)*sourceDyadicN n)^2 := by gcongr
    _ = _ := by ring

theorem sourceDyadicWeight_eventually_sq_le_one :
    ∀ᶠn : ℕ in atTop,(sourceDyadicWeight n)^2 ≤ 1 := by
  filter_upwards [sourceDyadicWeight_energy_tendsto.eventually_lt_const zero_lt_one] with n hn
  rw [sourceDyadicIndices_card,Nat.cast_add,Nat.cast_one] at hn
  nlinarith [sq_nonneg (sourceDyadicWeight n),Nat.cast_nonneg (α:=ℝ) n]

theorem sourceFlagMatrix_concentration {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Set.Icc (0:ℝ) 1)
    {K ρ η κ ε : ℝ} (hK : 0<K) (hcompact : ∀x,K ≤ ‖x‖ → χ x=0)
    (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ) (hε : 0<ε)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : FlagSite a m D v → Ω → ℝ) (hind : iIndepFun X μ)
    (hm : ∀i,AEMeasurable (X i) μ) (hb : ∀i,∀ᵐω ∂μ,X i ω∈Set.Icc (-1:ℝ) 1)
    (hc : ∀i,∫ω,X i ω ∂μ=0) :
    Tendsto (fun n => μ.real {ω | ∃z : FlagSite a m D v,
      ε ≤ |∑y∈sourceActiveSites hD hK n,sourceFlagMatrix χ ρ η κ n z y*X y ω|})
        atTop (nhds 0) := by
  let C := 2*flagRowConstant D ρ η
  let A := (m:ℝ)*(2*(D:ℝ)^2*K+2)^2
  let c := ε^2/(2*C^2)
  have hC : 0<C := by dsimp [C,flagRowConstant]; positivity
  have hA : 0≤A := by dsimp [A]; positivity
  have hc₀ : 0 < c := by dsimp [c]; positivity
  have ht4 := tendsto_pow_atTop_atTop_of_one_lt (show (1:ℝ)<4 by norm_num)
  have ht : Tendsto (fun n : ℕ => 2*A*((4:ℝ)^n)^4*Real.exp (-c*(4:ℝ)^n)) atTop (nhds 0) := by
    have ht := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4:ℝ) c hc₀).comp ht4
    have ht' := ht.const_mul (2*A)
    simpa only [Real.rpow_ofNat,mul_zero,mul_assoc,Function.comp_def] using ht'
  apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ ht
  filter_upwards [sourceDyadicWeight_eventually_sq_le_one] with n hw
  let S : Finset (FlagSite a m D v) := sourceActiveSites hD hK n
  have heq : {ω | ∃z : FlagSite a m D v,
      ε ≤ |∑y∈S,sourceFlagMatrix χ ρ η κ n z y*X y ω|} =
      {ω | ∃z∈S,ε ≤ |∑y∈S,sourceFlagMatrix χ ρ η κ n z y*X y ω|} := by
    ext ω
    constructor
    · rintro ⟨z,hz⟩
      refine ⟨z,?_,hz⟩
      by_contra hn
      have hzero (y : FlagSite a m D v) := sourceFlagMatrix_support hD χ hK hcompact ρ η κ n z y hn
      simp only [hzero,zero_mul,Finset.sum_const_zero,abs_zero] at hz
      exact (not_le.mpr hε) hz
    · rintro ⟨z,_,hz⟩; exact ⟨z,hz⟩
  have hrow (z : FlagSite a m D v) : ∑y∈S,(sourceFlagMatrix χ ρ η κ n z y)^2 ≤ C^2/(4:ℝ)^n := by
    have h := flagAveragingMatrix_dyadic_row_energy hD χ hχ hρ (sourceDyadicN_pos n) hη hκ
      (sourceDyadicIndices n) n (fun i hi => (Finset.mem_Icc.mp hi).1) (sourceDyadicWeight n) z S
    have hpow : ((2:ℝ)^n)^2=(4:ℝ)^n := by rw [← pow_mul,pow_mul']; norm_num
    calc
      _ ≤ (C*sourceDyadicWeight n/(2:ℝ)^n)^2 := h
      _ = C^2*(sourceDyadicWeight n)^2/(4:ℝ)^n := by rw [div_pow,mul_pow,hpow]
      _ ≤ _ := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (sq_nonneg C)
  rw [heq]
  calc
    _ ≤ 2*(S.card:ℝ)*Real.exp (-ε^2/(2*(C^2/(4:ℝ)^n))) :=
      finite_matrix_noise_tail μ X hind hm hb hc S S (sourceFlagMatrix χ ρ η κ n)
        (by positivity) (fun z _ => hrow z) hε.le
    _ ≤ 2*(A*(sourceDyadicN n)^2)*Real.exp (-ε^2/(2*(C^2/(4:ℝ)^n))) := by
      gcongr
      exact sourceActiveSites_card hD hK n
    _ = _ := by
      have hexp : -ε^2/(2*(C^2/(4:ℝ)^n)) = -c*(4:ℝ)^n := by dsimp [c]; field_simp
      rw [hexp]
      have hpow : (sourceDyadicN n)^2=((4:ℝ)^n)^4 := by
        unfold sourceDyadicN
        rw [← pow_mul,← pow_mul]
        rw [show (4:ℝ)=2^2 by norm_num,← pow_mul]
        congr 1
        omega
      rw [hpow]
      ring

end SourceFieldConcentration

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_HellingerDistance
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

section FiniteAffineLaw
open Classical MeasureTheory Matrix Set
open scoped ENNReal

instance finiteAffineNoiseLaw_probability {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (a : ι → ℝ) : IsProbabilityMeasure (finiteAffineNoiseLaw A a) := by
  unfold finiteAffineNoiseLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end FiniteAffineLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FiniteLawDistance
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

section FiniteField
open Classical Matrix MeasureTheory

theorem finiteCoefficientField_measurable {ι : Type*} (J : Finset ι)
    (a : ι → ℝ) (B : Matrix ι ι ℝ) : Measurable (finiteCoefficientField J a B) := by
  apply Measurable.of_eval
  intro z
  exact (measurable_const.add (measurable_pi_apply z)).add
    (Finset.measurable_sum _ (fun w _ => measurable_const.mul (measurable_pi_apply w)))

end FiniteField

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldHS
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

section SourceFieldLaw
open Classical Matrix MeasureTheory Filter
open scoped Topology

instance sourceSmoothFieldLaw_probability {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceSmoothFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n) := by
  unfold sourceSmoothFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (finiteCoefficientField_measurable _ _ _).aemeasurable

end SourceFieldLaw

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_ThresholdField
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
section ThresholdField
open Classical MeasureTheory Set

theorem thresholdField_measurable {ι : Type*} : Measurable (@thresholdField ι) := by
  apply Measurable.of_eval
  intro z
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_pi_apply z))
    measurable_const measurable_const

theorem signalSuccess_measurable {ι : Type*} [Countable ι] (a : ι → ℝ) :
    MeasurableSet {b : ι → Bool | signalSuccess a b} := by
  unfold signalSuccess
  measurability

theorem signalSuccess_of_noise {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (B : Matrix ι ι ℝ) (x : ι → ℝ) (hx : ∀z,x z∈Icc (-1:ℝ) 1)
    (hB : ∀z,|∑w∈J,B z w*x w|<1/2) :
    signalSuccess a (thresholdField (finiteCoefficientField J a B x)) := by
  intro z
  have hn := abs_lt.mp (hB z)
  have hxz := hx z
  rcases hxz with ⟨hxlo,hxhi⟩
  constructor
  · intro ha
    have hh : 0<finiteCoefficientField J a B x z := by
      unfold finiteCoefficientField
      linarith
    simp only [thresholdField,ite_eq_left hh]
  · intro ha
    have hh : ¬0<finiteCoefficientField J a B x z := by
      unfold finiteCoefficientField
      linarith
    simp only [thresholdField,ite_eq_right hh]

end ThresholdField

section SourceBitField
open Classical MeasureTheory Filter Set
open scoped Topology

instance sourceBitFieldLaw_probability {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) {L : ℝ} (hL : 0<L) (ρ η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (sourceBitFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n) := by
  unfold sourceBitFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map thresholdField_measurable.aemeasurable

theorem sourceBitFieldLaw_success {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (θ χ : (ℝ×ℝ) → ℝ) (hχ : ∀x,χ x∈Icc (0:ℝ) 1)
    {L ρ η κ : ℝ} (hL : 0<L) (hχc : ∀x,L≤‖x‖ → χ x=0)
    (hρ : 0<ρ) (hη : 0<η) (hκ : 0<κ) :
    Tendsto (fun n => (sourceBitFieldLaw (a:=a) (m:=m) (v:=v) hD θ χ hL ρ η κ n).real
      {b | ¬signalSuccess (flagMeanSignal θ (sourceDyadicN n)) b}) atTop (nhds 0) := by
  let μ := independentSmoothNoiseLaw (FlagSite a m D v)
  have ht := sourceFlagMatrix_concentration (v:=v) hD χ hχ hL hχc hρ hη hκ
    (show (0:ℝ)<1/2 by norm_num) μ (fun i x => x i)
    (independentSmoothNoiseLaw_independent _) (fun i => (measurable_pi_apply i).aemeasurable)
    (independentSmoothNoiseLaw_bounded _) (independentSmoothNoiseLaw_centered _)
  apply squeeze_zero (fun n => measureReal_nonneg) _ ht
  intro n
  unfold sourceBitFieldLaw sourceSmoothFieldLaw
  have hs : MeasurableSet {b : FlagSite a m D v → Bool | ¬signalSuccess (flagMeanSignal θ (sourceDyadicN n)) b} :=
    (signalSuccess_measurable _).compl
  rw [map_measureReal_apply thresholdField_measurable hs,
    map_measureReal_apply (finiteCoefficientField_measurable _ _ _)
      (thresholdField_measurable hs)]
  apply ENNReal.toReal_mono (measure_ne_top μ _)
  apply measure_mono_ae
  have hb : ∀ᵐx ∂μ,∀z,x z∈Icc (-1:ℝ) 1 := ae_all_iff.mpr (independentSmoothNoiseLaw_bounded _)
  filter_upwards [hb] with x hx
  intro hbad
  by_contra hnone
  apply hbad
  apply signalSuccess_of_noise _ _ _ _ hx
  intro z
  have hh : ¬(1/2:ℝ)≤|∑y∈sourceActiveSites (v:=v) hD hL n,sourceFlagMatrix χ ρ η κ n z y*x y| :=
    fun hz => hnone ⟨z,hz⟩
  exact lt_of_not_ge hh

end SourceBitField

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_FieldSignalData
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
section FieldSignalData
open Classical Set
open scoped ContDiff

namespace FieldSignalData

instance realLaw_probability (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.IsProbabilityMeasure (S.realLaw (a:=a) (m:=m) (v:=v) hD η κ n) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure (sourceSmoothFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n))

instance bitLaw_probability (S : FieldSignalData) {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (η κ : ℝ) (n : ℕ) : MeasureTheory.IsProbabilityMeasure (S.bitLaw (a:=a) (m:=m) (v:=v) hD η κ n) :=
  inferInstanceAs (MeasureTheory.IsProbabilityMeasure (sourceBitFieldLaw hD S.signal S.χ S.L_pos ((D:ℝ)^4/5) η κ n))

end FieldSignalData
end FieldSignalData

end SimpleAmenable
end
end

end OAI
end

section
-- module Solutions.OAIQ065_SA.SimpleAmenable_RandomFields_JointBitField
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
section JointBitField
open Classical MeasureTheory Filter
open scoped Topology

instance jointBitFieldLaw_probability {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) (η κ : ℝ) (n : ℕ) :
    IsProbabilityMeasure (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n) := by
  unfold jointBitFieldLaw
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | exact (continuous_eval_const _).aemeasurable | (apply Measurable.aemeasurable; measurability) | measurability)

end JointBitField

section JointFieldSuccess
open Classical MeasureTheory Filter Set
open scoped Topology

theorem jointBitFieldLaw_success_oai {k a m D : ℕ} (v : Fin k → ℝ×ℝ)
    (S : Fin k → FieldSignalData) (hD : 0<D) {η κ : ℝ} (hη : 0<η) (hκ : 0<κ) :
    Tendsto (fun n => (jointBitFieldLaw (a:=a) (m:=m) v S hD η κ n).real
      {b | ¬jointFieldSuccess v S n b}) atTop (nhds 0) := by
  let μ (n : ℕ) (j : Fin k) := (S j).bitLaw (a:=a) (m:=m) (v:=v j) hD η κ n
  let E (n : ℕ) (j : Fin k) := {b : FlagSite a m D (v j) → Bool |
    ¬signalSuccess (flagMeanSignal (S j).signal (sourceDyadicN n)) b}
  have ht (j : Fin k) : Tendsto (fun n => (μ n j).real (E n j)) atTop (nhds 0) :=
    sourceBitFieldLaw_success hD (S j).signal (S j).χ (S j).χ_range (S j).L_pos (S j).χ_zero
      (by positivity) hη hκ
  have hs : Tendsto (fun n => ∑j,(μ n j).real (E n j)) atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finsetSum Finset.univ (fun j _ => ht j)
  apply squeeze_zero (fun _ => measureReal_nonneg) _ hs
  intro n
  have he : {b : ∀j,FlagSite a m D (v j) → Bool | ¬jointFieldSuccess v S n b}=
      ⋃j,Function.eval j ⁻¹' E n j := by ext b; simp [jointFieldSuccess,E]
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  apply Finset.sum_le_sum
  intro j _
  have hp := measurePreserving_eval (μ n) j
  have hm : MeasurableSet (E n j) := (signalSuccess_measurable _).compl
  have hh := map_measureReal_apply (μ:=Measure.pi (μ n)) hp.measurable hm
  rw [hp.map_eq] at hh
  exact hh.symm.le

end JointFieldSuccess

end SimpleAmenable
end
end

end OAI
end

theorem solution : type_of% @OAI.SimpleAmenable.jointBitFieldLaw_success_oai := @OAI.SimpleAmenable.jointBitFieldLaw_success_oai
