-- Prove2me | solution 1 for Kyprianou.Ch04.physicalStepGridIdentityV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:56:14.871061+00:00
-- url     : https://prove2.me/submissions/879eefbe-2044-4398-960a-44600041b1c4

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch04_clippedGridWindowIntegralV1
import Theorems.Thm_Kyprianou_Ch04_referenceMarkWindowLinearV1
import Theorems.Thm_Kyprianou_Ch04_physicalMarkIndicatorWindowIntegralV1
import Theorems.Thm_Kyprianou_Ch04_closedTimeBandIntensityFinite
import Theorems.Thm_Kyprianou_Ch04_boundedSupportedWindowIntegrableV1
open MeasureTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Exact physical compensated integral identity for the finite step weights. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfin : ν B < ⊤)
    (hmark : ∀ z ∈ B, |z| ≤ 1)
    (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ) (H : ℕ → Ω → ℝ)
    (Y : NNReal → Ω → ℝ)
    (hY : ∀ t w, Y t w =
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ B, z.2 ∂(N.N w)) -
        (t : ℝ) * (∫ x in B,x ∂ν)) :
    let g := fun (p : (NNReal × Ω) × ℝ) =>
      B.indicator (fun x => x * ∑ k ∈ Finset.range n,
        (Ioc (u k) (u (k+1))).indicator (fun _ => H k p.1.2) p.1.1) p.2
    ∀ᵐ w ∂P, ∀ t : NNReal,
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,w),z.2) ∂(N.N w)) -
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ (univ : Set ℝ),
        g ((z.1.toNNReal,w),z.2) ∂referenceIntensity ν) =
      ∑ k ∈ Finset.range n, H k w *
        (Y (min t (u (k+1))) w-Y (min t (u k)) w) := by
  intro g
  let D (t : NNReal) := Icc (0 : ℝ) (t : ℝ) ×ˢ B
  let Q (z : ℝ × ℝ) := B.indicator id z.2
  have hQ : Measurable Q := (measurable_id.indicator hB).comp measurable_snd
  have hQb (z : ℝ × ℝ) : ‖Q z‖ ≤ 1 := by
    by_cases hz : z.2 ∈ B
    · simpa [Q,Real.norm_eq_abs,hz] using hmark z.2 hz
    · simp [Q,hz]
  have hQs (z : ℝ × ℝ) (hz : z.2 ∉ B) : Q z = 0 := by simp [Q,hz]
  have hI (t : NNReal) : referenceIntensity ν (D t) < ⊤ :=
    (Kyprianou.Ch04.closedTimeBandIntensityFinite ν t B hfin).lt_top
  have hN (t : NNReal) : ∀ᵐ w ∂P, N.N w (D t) < ⊤ := by
    filter_upwards [N.integer_valued (measurableSet_Icc.prod hB) (hI t).ne] with w hw
    obtain ⟨m,hm⟩ := hw
    rw [hm]
    exact ENNReal.natCast_lt_top m
  have hAll : ∀ᵐ w ∂P, ∀ m : ℕ, N.N w (D m) < ⊤ := ae_all_iff.mpr (fun m => hN m)
  filter_upwards [hAll] with w hw
  intro t
  obtain ⟨m,hm⟩ := exists_nat_ge t
  have hNt : N.N w (D t) < ⊤ := (measure_mono (fun z hz =>
    show z ∈ D m from ⟨⟨hz.1.1,hz.1.2.trans (by exact_mod_cast hm)⟩,hz.2⟩)).trans_lt (hw m)
  have hiN := (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 (N.N w) t B hB hNt
    Q hQ 1 hQb hQs).1
  have hiR := (Kyprianou.Ch04.boundedSupportedWindowIntegrableV1 (referenceIntensity ν) t B hB
    (hI t) Q hQ 1 hQb hQs).1
  have hg (z : ℝ × ℝ) : g ((z.1.toNNReal,w),z.2) =
      (∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k w) z.1.toNNReal) * Q z := by
    by_cases hz : z.2 ∈ B <;> simp [g,Q,Set.indicator_apply,hz,mul_comm]
  simp_rw [hg]
  rw [Kyprianou.Ch04.clippedGridWindowIntegralV1 (N.N w) Q t t le_rfl u hu n
    (fun k => H k w) hiN,
    Kyprianou.Ch04.clippedGridWindowIntegralV1 (referenceIntensity ν) Q t t le_rfl u hu n
    (fun k => H k w) hiR,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hY,hY]
  simp only [Q]
  have hMask (s : NNReal) : (∫ z in Icc (0 : ℝ) (s : ℝ) ×ˢ (univ : Set ℝ),
      B.indicator id z.2 ∂(N.N w)) = ∫ z in Icc (0 : ℝ) (s : ℝ) ×ˢ B, z.2 ∂(N.N w) := by
    exact Kyprianou.Ch04.physicalMarkIndicatorWindowIntegralV1
      (N.N w) s B hB (fun z => z.2)
  rw [hMask,hMask,Kyprianou.Ch04.referenceMarkWindowLinearV1 ν _ B hB id,
    Kyprianou.Ch04.referenceMarkWindowLinearV1 ν _ B hB id]
  simp only [id] <;> ring
