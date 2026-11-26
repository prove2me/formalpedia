-- Prove2me | solution 1 for Kyprianou.Ch04.exhaustedPhysicalL2Isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:41:30.555933+00:00
-- url     : https://prove2.me/submissions/4acae36e-fe70-4b58-8edf-e152b5fdbf88

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_markBandCutoffConvergence
import Theorems.Thm_Kyprianou_Ch04_physicalL2LimitTransfer
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false

/-- Extend a physical isometry on finite bands to every integrable L2 kernel. -/
theorem solution {A Omega : Type} [MeasurableSpace A] [MeasurableSpace Omega]
    (mu : Measure A) (P : Measure Omega) (T : (A → ℝ) → Omega → ℝ)
    (hT : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu →
      Integrable (T f) P ∧ Integrable (T g) P ∧
        (∫ w, |T f w - T g w| ∂P) ≤ 2 * ∫ a, |f a - g a| ∂mu)
    (hSub : ∀ f g : A → ℝ, Measurable f → Measurable g →
      Integrable f mu → Integrable g mu → T (f - g) =ᵐ[P] T f - T g)
    (B : ℕ → Set A) (hB : ∀ n, MeasurableSet (B n))
    (hmono : Monotone B) (hcover : (⋃ n, B n) = Set.univ)
    (hSq : ∀ (n : ℕ) (f : A → ℝ), Measurable f → Integrable f mu →
      MemLp f 2 mu → (∀ a ∉ B n, f a = 0) →
      Integrable (fun w => (T f w)^2) P ∧
        (∫ w, (T f w)^2 ∂P) = ∫ a, (f a)^2 ∂mu)
    (g : A → ℝ) (hgm : Measurable g) (hgi : Integrable g mu) (hg : MemLp g 2 mu) :
    MemLp (T g) 2 P ∧ (∫ w, (T g w)^2 ∂P) = ∫ a, (g a)^2 ∂mu := by
  classical
  let f := fun n => (B n).indicator g
  have hf (n : ℕ) : MemLp (f n) 2 mu := hg.indicator (hB n)
  have hm (n : ℕ) : Measurable (f n) := hgm.indicator (hB n)
  have hi (n : ℕ) : Integrable (f n) mu := hgi.indicator (hB n)
  have hTi (n : ℕ) := hT (f n) g (hm n) hgm (hi n) hgi
  have hSn (n : ℕ) := hSq n (f n) (hm n) (hi n) (hf n)
    (fun a ha => Set.indicator_of_notMem ha g)
  have hX (n : ℕ) : MemLp (T (f n)) 2 P :=
    (memLp_two_iff_integrable_sq (hTi n).1.aestronglyMeasurable).2 (hSn n).1
  have hconv := Kyprianou.Ch04.markBandCutoffConvergence mu B hB hmono hcover g hgi hg
  have hL1 : Tendsto (fun n => ∫ w, |T (f n) w - T g w| ∂P) atTop (𝓝 0) := by
    have h := hconv.2.const_mul (2 : ℝ)
    rw [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
      (fun _ => integral_nonneg fun _ => abs_nonneg _) (fun n => (hTi n).2.2)
  have hDiff (n m : ℕ) : (∫ w, (T (f n) w - T (f m) w)^2 ∂P) =
      ∫ a, (f n a - f m a)^2 ∂mu := by
    have hz (a : A) (ha : a ∉ B (max n m)) : (f n - f m) a = 0 := by
      have hn : a ∉ B n := fun h => ha (hmono (le_max_left _ _) h)
      have hm' : a ∉ B m := fun h => ha (hmono (le_max_right _ _) h)
      simp [f, Set.indicator_of_notMem hn, Set.indicator_of_notMem hm']
    have hs := hSq (max n m) (f n - f m) ((hm n).sub (hm m))
      ((hi n).sub (hi m)) ((hf n).sub (hf m)) hz
    have he : (fun w => (T (f n - f m) w)^2) =ᵐ[P]
        fun w => (T (f n) w - T (f m) w)^2 :=
      (hSub (f n) (f m) (hm n) (hm m) (hi n) (hi m)).fun_comp (fun x : ℝ => x^2)
    exact (integral_congr_ae he).symm.trans hs.2
  exact Kyprianou.Ch04.physicalL2LimitTransfer mu P f g (fun n => T (f n)) (T g)
    hf hg hX (fun n => (hTi n).1) (hTi 0).2.1 hconv.1 hL1
    (fun n => (hSn n).2) hDiff
