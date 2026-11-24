-- Prove2me | solution 1 for Kyprianou.Ch02.bvLevyCanonicalJordanTimeLaplaceFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:50:09.202228+00:00
-- url     : https://prove2.me/submissions/1a43e943-80a3-4ede-a0c5-a4745b262621

import Theorems.Thm_Kyprianou_Ch02_bvLevyJordanGridIncrementTendstoV1
import Theorems.Thm_Kyprianou_Ch02_levyJordanGridPairAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceIntegralTendstoV1
import Theorems.Thm_Kyprianou_Ch02_nonnegLaplaceCellIdentityV1
import Theorems.Thm_Kyprianou_Ch02_levyJordanGridLaplacePowerV1
import Theorems.Thm_Kyprianou_Ch02_laplacePowerFactorisationV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanPathwiseV1
import Theorems.Thm_Kyprianou_Ch02_levyCoordinateAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch02_bvLevyCanonicalJordanMarginalProcessesV1
import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology
set_option autoImplicit false
set_option linter.unusedVariables false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hBV : ∀ᵐ ω ∂P, LocallyBoundedVariationOn (fun t : ℝ≥0 => X t ω) Set.univ) :
    let V : ℝ≥0 → Ω → ℝ := fun t ω =>
      variationOnFromTo (fun s => X s ω) Set.univ 0 t
    let A : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω + X t ω) / 2
    let B : ℝ≥0 → Ω → ℝ := fun t ω => (V t ω - X t ω) / 2
    ∀ t : ℝ≥0, ∀ u v : ℝ, 0 < u → 0 < v →
      (∫ ω, Real.exp (-(u * A t ω + v * B t ω)) ∂P) =
      (∫ ω, Real.exp (-(u * A t ω)) ∂P) *
        (∫ ω, Real.exp (-(v * B t ω)) ∂P) := by
  dsimp only
  intro t u v hu hv
  have hu0 : 0 ≤ u := hu.le
  have hv0 : 0 ≤ v := hv.le
  let V (s : ℝ≥0) (ω : Ω) := variationOnFromTo (fun r => X r ω) Set.univ 0 s
  let A (s : ℝ≥0) (ω : Ω) := (V s ω + X s ω) / 2
  let B (s : ℝ≥0) (ω : Ω) := (V s ω - X s ω) / 2
  -- Canonical equal-grid Jordan pair (matches IncrementTendsto / PairAEMeasurable)
  let G : ℕ → Ω → ℝ × ℝ := fun n ω =>
    let g (k : ℕ) := (0 : ℝ≥0) + (t - 0) * (k : ℝ≥0) / ((n + 1 : ℕ) : ℝ≥0)
    let d (k : ℕ) := X (g (k + 1)) ω - X (g k) ω
    (∑ k : Fin (n + 1), max (d k.val) 0, ∑ k : Fin (n + 1), max (-d k.val) 0)
  let At : Ω → ℝ := A t
  let Bt : Ω → ℝ := B t
  let f : Ω → ℝ × ℝ := fun ω => (At ω, Bt ω)
  obtain ⟨hMonoA, hMonoB, _⟩ :=
    Kyprianou.Ch02.bvLevyCanonicalJordanPathwiseV1 P X hX hBV
  obtain ⟨hLevyA, hLevyB⟩ :=
    Kyprianou.Ch02.bvLevyCanonicalJordanMarginalProcessesV1 P X hX hBV
  have hAt_nonneg : ∀ᵐ ω ∂P, 0 ≤ At ω := by
    filter_upwards [hMonoA] with ω hmono
    have hle : A 0 ω ≤ A t ω := hmono (bot_le : (0 : ℝ≥0) ≤ t)
    have h0 : A 0 ω = 0 := by
      simp [A, V, variationOnFromTo.self, congrFun hLevyA.start_zero ω]
    simpa [At, h0] using hle
  have hBt_nonneg : ∀ᵐ ω ∂P, 0 ≤ Bt ω := by
    filter_upwards [hMonoB] with ω hmono
    have hle : B 0 ω ≤ B t ω := hmono (bot_le : (0 : ℝ≥0) ≤ t)
    have h0 : B 0 ω = 0 := by
      simp [B, V, variationOnFromTo.self, congrFun hLevyB.start_zero ω]
    simpa [Bt, h0] using hle
  have hInc :=
    Kyprianou.Ch02.bvLevyJordanGridIncrementTendstoV1 P X hX hBV 0 t (bot_le : (0 : ℝ≥0) ≤ t)
  have htend : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (nhds (f ω)) := by
    filter_upwards [hInc] with ω hG
    -- G matches IncrementTendsto's G(_,0,t); target increment Y 0 t = Y t = f ω
    have hG' : Tendsto (fun n => G n ω) atTop
        (nhds (increment (fun s ω' => (A s ω', B s ω')) 0 t ω)) := by
      simpa [G, A, B, V] using hG
    convert hG'
    simp [increment, f, At, Bt, A, B, V, congrFun hX.start_zero ω, variationOnFromTo.self]
  have hmG : ∀ n, AEMeasurable (G n) P := fun n =>
    Kyprianou.Ch02.levyJordanGridPairAEMeasurableV1 P X hX n 0 t
  have hnG : ∀ n, ∀ᵐ ω ∂P, 0 ≤ (G n ω).1 ∧ 0 ≤ (G n ω).2 := fun n =>
    Eventually.of_forall fun ω => by
      change 0 ≤ (∑ k : Fin (n + 1), max _ 0) ∧ 0 ≤ (∑ k : Fin (n + 1), max _ 0)
      exact ⟨Finset.sum_nonneg fun _ _ => le_max_right _ _,
        Finset.sum_nonneg fun _ _ => le_max_right _ _⟩
  have hJtend :=
    Kyprianou.Ch02.nonnegLaplaceIntegralTendstoV1 P G f hmG hnG htend u v hu0 hv0
  have hAtend :=
    Kyprianou.Ch02.nonnegLaplaceIntegralTendstoV1 P G f hmG hnG htend u 0 hu0 le_rfl
  have hBtend :=
    Kyprianou.Ch02.nonnegLaplaceIntegralTendstoV1 P G f hmG hnG htend 0 v le_rfl hv0
  let Z : ℕ → Ω → ℝ := fun n => X (t / ((n + 1 : ℕ) : ℝ≥0))
  let a : ℕ → ℝ := fun n => ∫ ω, Real.exp (-(u * max (Z n ω) 0)) ∂P
  let b : ℕ → ℝ := fun n => ∫ ω, Real.exp (-(v * max (-Z n ω) 0)) ∂P
  have hZae (n : ℕ) : AEMeasurable (Z n) P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P X hX (t / ((n + 1 : ℕ) : ℝ≥0))
  have hcell (n : ℕ) :=
    Kyprianou.Ch02.nonnegLaplaceCellIdentityV1 P (Z n) (hZae n) u v hu0 hv0
  -- Align grid Laplace power (uses g k = t*k/(n+1) = 0+(t-0)*k/(n+1))
  have hpowJ (n : ℕ) :
      (∫ ω, Real.exp (-(u * (G n ω).1 + v * (G n ω).2)) ∂P) =
        (a n + b n - 1) ^ (n + 1) := by
    have hp := Kyprianou.Ch02.levyJordanGridLaplacePowerV1 P X hX t n u v
    have hc := (hcell n).2.2.2
    have hp' :
        (∫ ω, Real.exp (-(u * (G n ω).1 + v * (G n ω).2)) ∂P) =
          (∫ ω, Real.exp (-(u * max (Z n ω) 0 + v * max (-Z n ω) 0)) ∂P) ^ (n + 1) := by
      simpa [G, Z] using hp
    rw [hp', hc]
  have hpowA (n : ℕ) :
      (∫ ω, Real.exp (-(u * (G n ω).1)) ∂P) = (a n) ^ (n + 1) := by
    have hp := Kyprianou.Ch02.levyJordanGridLaplacePowerV1 P X hX t n u (0 : ℝ)
    have hp' :
        (∫ ω, Real.exp (-(u * (G n ω).1 + (0 : ℝ) * (G n ω).2)) ∂P) =
          (∫ ω, Real.exp (-(u * max (Z n ω) 0 + (0 : ℝ) * max (-Z n ω) 0)) ∂P) ^ (n + 1) := by
      simpa [G, Z] using hp
    simpa [zero_mul, add_zero, a] using hp'
  have hpowB (n : ℕ) :
      (∫ ω, Real.exp (-(v * (G n ω).2)) ∂P) = (b n) ^ (n + 1) := by
    have hp := Kyprianou.Ch02.levyJordanGridLaplacePowerV1 P X hX t n (0 : ℝ) v
    have hp' :
        (∫ ω, Real.exp (-((0 : ℝ) * (G n ω).1 + v * (G n ω).2)) ∂P) =
          (∫ ω, Real.exp (-((0 : ℝ) * max (Z n ω) 0 + v * max (-Z n ω) 0)) ∂P) ^ (n + 1) := by
      simpa [G, Z] using hp
    simpa [zero_mul, add_zero, b] using hp'
  have hAtend' :
      Tendsto (fun n => (a n) ^ (n + 1)) atTop
        (nhds (∫ ω, Real.exp (-(u * At ω)) ∂P)) := by
    have h : Tendsto (fun n => ∫ ω, Real.exp (-(u * (G n ω).1)) ∂P) atTop
        (nhds (∫ ω, Real.exp (-(u * At ω)) ∂P)) := by
      simpa [zero_mul, add_zero] using hAtend
    exact h.congr fun n => hpowA n
  have hBtend' :
      Tendsto (fun n => (b n) ^ (n + 1)) atTop
        (nhds (∫ ω, Real.exp (-(v * Bt ω)) ∂P)) := by
    have h : Tendsto (fun n => ∫ ω, Real.exp (-(v * (G n ω).2)) ∂P) atTop
        (nhds (∫ ω, Real.exp (-(v * Bt ω)) ∂P)) := by
      simpa [zero_mul, add_zero] using hBtend
    exact h.congr fun n => hpowB n
  have hJtend' :
      Tendsto (fun n => (a n + b n - 1) ^ (n + 1)) atTop
        (nhds (∫ ω, Real.exp (-(u * At ω + v * Bt ω)) ∂P)) :=
    hJtend.congr fun n => hpowJ n
  have hmAt : AEMeasurable At P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P A hLevyA t
  have hmBt : AEMeasurable Bt P :=
    Kyprianou.Ch02.levyCoordinateAEMeasurableV1 P B hLevyB t
  have hIntA : Integrable (fun ω => Real.exp (-(u * At ω))) P := by
    refine Integrable.of_bound
      (Real.measurable_exp.comp_aemeasurable (hmAt.const_mul u).neg).aestronglyMeasurable 1 ?_
    filter_upwards [hAt_nonneg] with ω hA
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hu0 hA))
  have hIntB : Integrable (fun ω => Real.exp (-(v * Bt ω))) P := by
    refine Integrable.of_bound
      (Real.measurable_exp.comp_aemeasurable (hmBt.const_mul v).neg).aestronglyMeasurable 1 ?_
    filter_upwards [hBt_nonneg] with ω hB
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hv0 hB))
  have hα : 0 < ∫ ω, Real.exp (-(u * At ω)) ∂P := by
    rw [integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hIntA]
    have : support (fun ω => Real.exp (-(u * At ω))) = univ := by
      ext ω; simp [Real.exp_ne_zero]
    simp [this, measure_univ]
  have hβ : 0 < ∫ ω, Real.exp (-(v * Bt ω)) ∂P := by
    rw [integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hIntB]
    have : support (fun ω => Real.exp (-(v * Bt ω))) = univ := by
      ext ω; simp [Real.exp_ne_zero]
    simp [this, measure_univ]
  have hfac :
      Tendsto (fun n => (a n + b n - 1) ^ (n + 1)) atTop
        (nhds ((∫ ω, Real.exp (-(u * At ω)) ∂P) *
          (∫ ω, Real.exp (-(v * Bt ω)) ∂P))) :=
    Kyprianou.Ch02.laplacePowerFactorisationV1 a b
      (∫ ω, Real.exp (-(u * At ω)) ∂P) (∫ ω, Real.exp (-(v * Bt ω)) ∂P)
      (fun n => (hcell n).1) (fun n => (hcell n).2.1) (fun n => (hcell n).2.2.1)
      hα hβ hAtend' hBtend'
  -- Targets match A t / B t from the let-binding
  change (∫ ω, Real.exp (-(u * A t ω + v * B t ω)) ∂P) =
    (∫ ω, Real.exp (-(u * A t ω)) ∂P) * (∫ ω, Real.exp (-(v * B t ω)) ∂P)
  simpa [At, Bt] using tendsto_nhds_unique hJtend' hfac
