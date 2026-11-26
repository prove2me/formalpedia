-- Prove2me | solution 1 for ManyServerQED.Scheduling.adapted_brownian_coordinate_at_monotone_times_is_martingale
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:44:28.801419+00:00
-- url     : https://prove2.me/submissions/9afaaacb-c749-4f74-a02d-a04b04f3dcce

import Definitions.Def_ManyServerQED_Scheduling_Diffusion

open Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

open ManyServerQED.Scheduling

theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {k : ℕ} (F : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → Fin k → ℝ) (hW : IsStdFBrownian P F W)
    {a : ℕ → ℝ≥0} (ha : Monotone a) (i : Fin k) :
    let H : Filtration ℕ mΩ := ⟨fun j => F (a j), fun _ _ h => F.mono (ha h), fun j => F.le (a j)⟩
    Martingale (fun j ω => W (a j) ω i) H P := by
  intro H
  let f (j : ℕ) (ω : Ω) := W (a j) ω i
  have hA (j : ℕ) : StronglyMeasurable[H j] (f j) :=
    ((measurable_pi_apply i).comp (hW.adapted (a j))).stronglyMeasurable
  have hF (j : ℕ) : Integrable (f j) P := (hW.brownian i).integrable_eval (a j)
  have h0 (j : ℕ) : (∫ ω, f j ω ∂P) = 0 := (hW.brownian i).integral_eval (a j)
  refine ⟨hA,?_⟩
  intro j l h
  let d := a l-a j
  have hd : a j+d = a l := add_tsub_cancel_of_le (ha h)
  let future (ω : Ω) (u : ℝ≥0) := W (a j+u) ω-W (a j) ω
  have hmeas (u : ℝ≥0) : @Measurable Ω (Fin k → ℝ) mΩ _ (fun ω => future ω u) :=
    ((hW.adapted (a j+u)).mono (F.le _) le_rfl).sub
      ((hW.adapted (a j)).mono (F.le _) le_rfl)
  have hMambient : @Measurable Ω (ℝ≥0 → Fin k → ℝ) mΩ _ future :=
    @measurable_pi_lambda Ω ℝ≥0 (fun _ => Fin k → ℝ) mΩ _ future hmeas
  have hIndependent := hW.indep_incr (a j)
  let m : MeasurableSpace Ω := MeasurableSpace.comap future inferInstance
  have hle : m ≤ mΩ := hMambient.comap_le
  have hi : @Indep Ω m (H j) mΩ P := hIndependent
  have hΔ : StronglyMeasurable[m] (f l-f j) := by
    have hProj : Measurable (fun p : ℝ≥0 → Fin k → ℝ => p d i) :=
      (measurable_pi_apply i).comp (measurable_pi_apply d)
    have hM : Measurable[m] future := measurable_iff_comap_le.2 le_rfl
    have he : (fun p : ℝ≥0 → Fin k → ℝ => p d i) ∘ future = f l-f j := by
      funext ω
      change W (a j+d) ω i-W (a j) ω i = W (a l) ω i-W (a j) ω i
      rw [hd]
    rw [← he]
    exact (hProj.comp hM).stronglyMeasurable
  have hExp : P[f l-f j | H j] =ᵐ[P] fun _ => (0:ℝ) := by
    have hh := condExp_indep_eq hle (H.le j) hΔ hi
    have hh' : (∫ ω, (f l-f j) ω ∂P) = 0 := by
      change (∫ ω, f l ω-f j ω ∂P) = 0
      rw [integral_sub (hF l) (hF j),h0,h0,sub_self]
    simpa only [hh'] using hh
  have hEq : f l = f j+(f l-f j) := by abel
  refine (condExp_congr_ae (Eventually.of_forall fun ω => congrFun hEq ω)).trans ?_
  refine (condExp_add (hF j) ((hF l).sub (hF j)) (H j)).trans ?_
  rw [condExp_of_stronglyMeasurable (H.le j) (hA j) (hF j)]
  filter_upwards [hExp] with ω hω
  change f j ω + P[f l-f j | H j] ω = f j ω
  rw [hω,add_zero]
