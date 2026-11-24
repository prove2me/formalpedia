-- Prove2me | solution 1 for GlobalTheory.JR.AbsInv.fourB_fourB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:02:00.215798+00:00
-- url     : https://prove2.me/submissions/3ae7efd9-e93f-4346-8960-0ecea5e73042

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Theorems.Thm_GlobalTheory_JR_AbsInv_integral_eq_zero_of_translate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open GlobalTheory.JR MeasureTheory Filter Topology
namespace GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in
private theorem fourB_eq_zero_of_not_mem_annihilator (μ : Measure V)
    [μ.IsAddHaarMeasure] (B : V → V → ℂ) (ha : ∀ x x' y, B (x + x') y = B x y * B x' y)
    (M N : AddSubgroup V) (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) (f : V → ℂ)
    (hi : ∀ x, ∀ m ∈ M, f (x + m) = f x) (y : V) (hy : y ∉ N) :
    _root_.GlobalTheory.JR.fourB μ B f y = 0 := by
  have hex : ∃ m ∈ M, B m y ≠ 1 := by
    by_contra h
    push_neg at h
    exact hy ((hN y).2 h)
  obtain ⟨m, hm, hBm⟩ := hex
  unfold _root_.GlobalTheory.JR.fourB
  apply _root_.GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ m (B m y) hBm
  intro x
  rw [hi x m hm, ha]
  ring
open MeasureTheory Filter Topology Pointwise in
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] in
variable [MeasurableSpace V] [BorelSpace V] in
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] in
private theorem integral_indicator_bicharacter_eq_indicator (μ : Measure V) [μ.IsAddHaarMeasure]
    (B : V → V → ℂ) (hs : ∀ x y, B x y = B y x) (ha : ∀ x x' y, B (x + x') y = B x y * B x' y)
    (M N : AddSubgroup V) (hNo : IsOpen (N : Set V)) (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (w : V) :
    ∫ y, (N : Set V).indicator (fun y => B w y) y ∂μ =
      (M : Set V).indicator (fun _ => ((μ.real N : ℝ) : ℂ)) w := by
  by_cases hw : w ∈ (M : Set V)
  · rw [Set.indicator_of_mem hw]
    have hfun : (N : Set V).indicator (fun y => B w y) = (N : Set V).indicator (fun _ => (1 : ℂ)) := by
      funext y
      by_cases hy : y ∈ (N : Set V)
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        exact (hM w).1 hw y hy
      · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    rw [hfun, integral_indicator_const _ hNo.measurableSet, Complex.real_smul, mul_one]
  · rw [Set.indicator_of_notMem hw]
    have hex : ∃ n ∈ N, B w n ≠ 1 := by
      by_contra h
      push_neg at h
      exact hw ((hM w).2 h)
    obtain ⟨n, hn, hBn⟩ := hex
    apply _root_.GlobalTheory.JR.AbsInv.integral_eq_zero_of_translate μ _ n (B w n) hBn
    intro y
    by_cases hy : y ∈ (N : Set V)
    · have hyn : y + n ∈ (N : Set V) := N.add_mem hy hn
      rw [Set.indicator_of_mem hyn, Set.indicator_of_mem hy, hs w (y + n), ha, hs y w, hs n w,
        mul_comm]
    · have hyn : y + n ∉ (N : Set V) := fun h => hy (by simpa using N.sub_mem h hn)
      rw [Set.indicator_of_notMem hyn, Set.indicator_of_notMem hy, mul_zero]
end GlobalTheory.JR.AbsInv
end

set_option autoImplicit false
open GlobalTheory.JR MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.AbsInv
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
open MeasureTheory Filter Topology Pointwise
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
variable [MeasurableSpace V] [BorelSpace V]
variable [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
namespace GlobalTheory.JR.AbsInv
namespace _root_.GlobalTheory.JR.AbsInv
theorem _root_.solution (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hNo : IsOpen (N : Set V)) (hNc : IsCompact (N : Set V))
    (hN : ∀ y, y ∈ N ↔ ∀ x ∈ M, B x y = 1) (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (f : V → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (hi : ∀ x, ∀ m ∈ M, f (x + m) = f x) (z : V) :
    _root_.GlobalTheory.JR.fourB μ B (_root_.GlobalTheory.JR.fourB μ B f) z = ((μ.real M * μ.real N : ℝ) : ℂ) * f (-z) := by
  have hNclo : IsClopen (N : Set V) := ⟨N.isClosed_of_isOpen hNo, hNo⟩
  let P : V → V → ℂ := fun x y => (N : Set V).indicator (fun _ => (1 : ℂ)) y * (f x * B x y) * B y z
  have hPy : ∀ y, ∫ x, P x y ∂μ = _root_.GlobalTheory.JR.fourB μ B f y * B y z := by
    intro y
    dsimp only [P]
    rw [integral_mul_const, integral_const_mul]
    congr 1
    by_cases hy : y ∈ (N : Set V)
    · rw [Set.indicator_of_mem hy, one_mul]
      rfl
    · rw [Set.indicator_of_notMem hy, zero_mul,
        fourB_eq_zero_of_not_mem_annihilator μ B ha M N hN f hi y hy]
  have hPx : ∀ x, ∫ y, P x y ∂μ =
      f x * (M : Set V).indicator (fun _ => ((μ.real N : ℝ) : ℂ)) (x + z) := by
    intro x
    rw [← integral_indicator_bicharacter_eq_indicator μ B hs ha M N hNo hM (x + z), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    dsimp only [P]
    by_cases hy : y ∈ (N : Set V)
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, ha, hs y z]
      ring
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
      ring
  have hPint : Integrable (Function.uncurry P) (μ.prod μ) := by
    apply Continuous.integrable_of_hasCompactSupport
    · have h1 : Continuous fun q : V × V => (N : Set V).indicator (fun _ => (1 : ℂ)) q.2 :=
        (hNclo.continuous_indicator continuous_const).comp continuous_snd
      have h2 : Continuous fun q : V × V => B q.2 z := hB.comp (continuous_snd.prodMk continuous_const)
      exact (h1.mul ((hf.comp continuous_fst).mul hB)).mul h2
    · apply HasCompactSupport.intro (hfc.isCompact.prod hNc)
      rintro ⟨x, y⟩ hq
      simp only [Set.mem_prod, not_and_or] at hq
      simp only [Function.uncurry_apply_pair, P]
      rcases hq with hx | hy
      · rw [image_eq_zero_of_notMem_tsupport hx]
        ring
      · rw [Set.indicator_of_notMem hy]
        ring
  have hpre : MeasurableSet ((fun x => x + z) ⁻¹' (M : Set V)) :=
    (hMo.preimage (continuous_add_right z)).measurableSet
  calc _root_.GlobalTheory.JR.fourB μ B (_root_.GlobalTheory.JR.fourB μ B f) z
      = ∫ y, _root_.GlobalTheory.JR.fourB μ B f y * B y z ∂μ := rfl
    _ = ∫ y, ∫ x, P x y ∂μ ∂μ := integral_congr_ae (Eventually.of_forall fun y => (hPy y).symm)
    _ = ∫ x, ∫ y, P x y ∂μ ∂μ := (integral_integral_swap hPint).symm
    _ = ∫ x, f x * (M : Set V).indicator (fun _ => ((μ.real N : ℝ) : ℂ)) (x + z) ∂μ :=
        integral_congr_ae (Eventually.of_forall hPx)
    _ = ∫ x, ((fun x => x + z) ⁻¹' (M : Set V)).indicator
          (fun _ => ((μ.real N : ℝ) : ℂ) * f (-z)) x ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        dsimp only
        by_cases hx : x + z ∈ (M : Set V)
        · have hfx : f x = f (-z) := by
            have e : -z + (x + z) = x := by abel
            have := hi (-z) (x + z) hx
            rwa [e] at this
          rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ (fun x => x + z) ⁻¹' (M : Set V) from hx),
            hfx, mul_comm]
        · rw [Set.indicator_of_notMem hx,
            Set.indicator_of_notMem (show x ∉ (fun x => x + z) ⁻¹' (M : Set V) from hx), mul_zero]
    _ = ((μ.real M * μ.real N : ℝ) : ℂ) * f (-z) := by
        rw [integral_indicator_const _ hpre, Complex.real_smul]
        simp only [measureReal_def, measure_preimage_add_right]
        push_cast
        ring
end _root_.GlobalTheory.JR.AbsInv
end GlobalTheory.JR.AbsInv
