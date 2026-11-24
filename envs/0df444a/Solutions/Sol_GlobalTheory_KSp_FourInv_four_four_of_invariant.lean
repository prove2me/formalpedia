-- Prove2me | solution 1 for GlobalTheory.KSp.FourInv.four_four_of_invariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:54:39.681099+00:00
-- url     : https://prove2.me/submissions/df3616ba-6236-4351-be3c-945132233037

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_UnipVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BicharacterFourierTransformTwiceEqPosSmulReflect
import Theorems.Thm_GlobalTheory_KSp_FourInv_isOpen_ann
import Theorems.Thm_GlobalTheory_KSp_FourInv_four_eq_zero
import Theorems.Thm_GlobalTheory_KSp_FourInv_four_indicator
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
noncomputable section
namespace GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}
variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
private theorem exists_four_four_eq_smul_neg_of_ann_invariant (hX : Good X) (he : IsPair e) (L : AddSubgroup X)
    (hLc : IsCompact (L : Set X)) (hLo : IsOpen (L : Set X)) :
    ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, (∀ t ∈ ann he (L : Set X), ∀ x, φ (x + t) = φ x) →
      ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  have := hX.sc
  set A := ann he (L : Set X) with hA
  set B := ann he (A : Set X) with hB
  have hAo : IsOpen (A : Set X) := isOpen_ann he hLc
  have hAc : IsCompact (A : Set X) := by
    obtain ⟨K, hK, hKA⟩ := he.big (L : Set X) (hLo.mem_nhds L.zero_mem)
    exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen A hAo) fun y hy => hKA y hy
  have hBo : IsOpen (B : Set X) := isOpen_ann he hAc
  have hBc : IsCompact (B : Set X) := by
    obtain ⟨K, hK, hKB⟩ := he.big (A : Set X) (hAo.mem_nhds A.zero_mem)
    exact hK.of_isClosed_subset (AddSubgroup.isClosed_of_isOpen B hBo) fun y hy => hKB y hy
  have hLB : (L : Set X) ⊆ B := by
    intro z hz
    show ∀ y ∈ (A : Set X), e y z = 1
    intro y hy
    have hy' : ∀ x ∈ (L : Set X), e x y = 1 := hy
    rw [he.symm]
    exact hy' z hz
  have hBA : (ann he (B : Set X) : Set X) = A := by
    ext z
    constructor
    · intro hz
      have hz' : ∀ y ∈ (B : Set X), e y z = 1 := hz
      show ∀ x ∈ (L : Set X), e x z = 1
      exact fun x hx => hz' x (hLB hx)
    · intro hz
      show ∀ y ∈ (B : Set X), e y z = 1
      intro y hy
      have hy' : ∀ w ∈ (A : Set X), e w y = 1 := hy
      rw [he.symm]
      exact hy' z hz
  have hApos : 0 < μ.real (A : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hAo.measure_pos μ ⟨0, A.zero_mem⟩).ne' hAc.measure_lt_top.ne
  have hBpos : 0 < μ.real (B : Set X) := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (hBo.measure_pos μ ⟨0, B.zero_mem⟩).ne' hBc.measure_lt_top.ne
  refine ⟨μ.real (A : Set X) * μ.real (B : Set X), mul_pos hApos hBpos, fun φ hφ hs w => ?_⟩
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hSc : IsCompact (tsupport φ) := hφ'.2.isCompact
  have : IsFiniteMeasure (μ.restrict (tsupport φ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSc.measure_lt_top⟩
  have : IsFiniteMeasure (μ.restrict (B : Set X)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBc.measure_lt_top⟩
  have h1 : ∀ x, ∫ z, e x z * φ z ∂μ = ∫ z in tsupport φ, e x z * φ z ∂μ := fun x =>
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]).symm
  have h2 : ∫ x, e w x * ∫ z, e x z * φ z ∂μ ∂μ = ∫ x in (B : Set X), e w x * ∫ z, e x z * φ z ∂μ ∂μ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
      have h0 := four_eq_zero μ he hs (y := x) hx
      simp only [four] at h0
      rw [h0, mul_zero]).symm
  have h3 : ∀ x, e w x * ∫ z in tsupport φ, e x z * φ z ∂μ =
      ∫ z in tsupport φ, e w x * (e x z * φ z) ∂μ := fun x => (integral_const_mul _ _).symm
  obtain ⟨C0, hC0⟩ := hφ'.1.continuous.bounded_above_of_compact_support hφ'.2
  have hcont : Continuous (Function.uncurry fun x z => e w x * (e x z * φ z)) :=
    (he.lc.continuous.comp (continuous_const.prodMk continuous_fst)).mul
      (he.lc.continuous.mul (hφ'.1.continuous.comp continuous_snd))
  have hint : Integrable (Function.uncurry fun x z => e w x * (e x z * φ z))
      ((μ.restrict (B : Set X)).prod (μ.restrict (tsupport φ))) :=
    (integrable_const C0).mono' hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => by
      simp only [Function.uncurry, norm_mul, he.norm, one_mul]
      exact hC0 p.2)
  have h4 : ∀ z, ∫ x in (B : Set X), e w x * (e x z * φ z) ∂μ =
      φ z * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) := by
    intro z
    have hB1 := four_indicator μ he B hBo (w + z)
    simp only [four] at hB1
    rw [← hB1, ← integral_indicator hBo.measurableSet, mul_comm (φ z), ← integral_mul_const]
    congr 1
    ext x
    by_cases hx : x ∈ (B : Set X)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, he.add, he.symm z x]
      ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      ring
  have h5 : ∀ z, φ z * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) =
      φ (-w) * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) := by
    intro z
    by_cases hz : w + z ∈ (ann he (B : Set X) : Set X)
    · have hzA : w + z ∈ (A : Set X) := hBA.subset hz
      have h := hs (w + z) hzA (-w)
      rw [neg_add_cancel_left] at h
      rw [h]
    · rw [Set.indicator_of_notMem hz, mul_zero, mul_zero]
  have h6 : ∫ z in tsupport φ, φ (-w) * (ann he (B : Set X) : Set X).indicator
      (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) ∂μ =
      ∫ z, φ (-w) * (ann he (B : Set X) : Set X).indicator (fun _ => (μ.real (B : Set X) : ℂ)) (w + z) ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => ?_
    rw [← h5 z, image_eq_zero_of_notMem_tsupport hz, zero_mul]
  have hAm : MeasurableSet (ann he (B : Set X) : Set X) := by
    rw [hBA]
    exact hAo.measurableSet
  simp only [four]
  rw [h2]
  simp_rw [h1, h3]
  rw [integral_integral_swap hint]
  simp_rw [h4, h5]
  rw [h6, integral_const_mul,
    integral_add_left_eq_self (fun z => (ann he (B : Set X) : Set X).indicator
      (fun _ => (μ.real (B : Set X) : ℂ)) z) w,
    integral_indicator_const _ hAm, hBA, Complex.real_smul]
  push_cast
  ring
end GlobalTheory.KSp.FourInv
namespace GlobalTheory.KSp
end GlobalTheory.KSp
end
end

set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.KSp GlobalTheory.KSp.FourInv
variable {X : Type} [AddCommGroup X] [TopologicalSpace X] {e : X → X → ℂ}
variable [IsTopologicalAddGroup X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure]
namespace GlobalTheory.KSp.FourInv
theorem _root_.solution (hX : Good X) (he : IsPair e) (M : AddSubgroup X) (hMc : IsCompact (M : Set X))
    (hMo : IsOpen (M : Set X)) : ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, (∀ t ∈ M, ∀ x, φ (x + t) = φ x) →
      ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  obtain ⟨K, hK, hKM⟩ := he.small (M : Set X) (hMo.mem_nhds M.zero_mem)
  obtain ⟨L, hLc, hLo, hKL⟩ := hX.large K hK
  obtain ⟨C, hC, hCφ⟩ := exists_four_four_eq_smul_neg_of_ann_invariant μ hX he L hLc hLo
  refine ⟨C, hC, fun φ hφ hs => hCφ φ hφ fun t ht => hs t (hKM t fun x hx => ?_)⟩
  exact (show ∀ y ∈ (L : Set X), e y t = 1 from ht) x (hKL hx)
end GlobalTheory.KSp.FourInv
