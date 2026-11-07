-- Prove2me | solution 1 for NonlinSSD.Optimality.weak_duality
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T04:01:24.84231+00:00
-- url     : https://prove2.me/submissions/a097a198-883a-404d-9030-8f528c7648b8

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic
import Theorems.Thm_NonlinSSD_Optimality_eq_25_measure_utility
import Theorems.Thm_SSDConstraint_Optimality_U1_eq_uOfMeasure_unique
import Theorems.Thm_DualSSD_Duality_secondPerformance_properties

open MeasureTheory NonlinSSD.Optimality

theorem nl2_U1_lip {a b : ℝ} {u : ℝ → ℝ} (hu : u ∈ U1 a b) :
    ∃ c : ℝ, 0 ≤ c ∧ (∀ s t, s < t → u t - u s ≤ c * (t - s)) ∧
      ∀ t, |u t| ≤ |u a| + c * |t - a| := by
  obtain ⟨hconc, hmono, hzero, c, hc, hlin⟩ := hu
  refine ⟨c, hc, fun s t hst => ?_, fun t => ?_⟩
  · have hslope : (u t - u s) / (t - s) ≤ c := by
      rcases le_or_gt s a with hsa | hsa
      · have h1 := hconc.slope_anti_adjacent (x := s - 1) (y := s) (z := t) trivial trivial
          (by linarith) hst
        have e1 := hlin s hsa
        have e2 := hlin (s - 1) (by linarith)
        have : (u s - u (s - 1)) / (s - (s - 1)) = c := by
          rw [e1, e2]; field_simp; ring
        linarith
      · have h1 := hconc.slope_anti_adjacent (x := a) (y := s) (z := t) trivial trivial hsa hst
        have h2 := hconc.slope_anti_adjacent (x := a - 1) (y := a) (z := s) trivial trivial
          (by linarith) hsa
        have e2 := hlin (a - 1) (by linarith)
        have : (u a - u (a - 1)) / (a - (a - 1)) = c := by
          rw [e2]; field_simp; ring
        linarith
    have hpos : 0 < t - s := sub_pos.2 hst
    rwa [div_le_iff₀ hpos] at hslope
  · rcases le_or_gt b t with hbt | hbt
    · rw [hzero t hbt, abs_zero]; positivity
    rcases lt_or_ge t a with hta | hta
    · rw [hlin t hta.le]
      calc |u a + c * (t - a)| ≤ |u a| + |c * (t - a)| := abs_add_le _ _
        _ = |u a| + c * |t - a| := by rw [abs_mul, abs_of_nonneg hc]
    · have h1 : u a ≤ u t := hmono hta
      have h2 : u t ≤ u b := hmono hbt.le
      have h3 : u b = 0 := hzero b le_rfl
      have : |u t| ≤ |u a| := by
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]; linarith
      have : 0 ≤ c * |t - a| := by positivity
      linarith

theorem nl2_U1_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {a b : ℝ} {u : ℝ → ℝ} (hu : u ∈ U1 a b)
    {X : Ω → ℝ} (hX : Integrable X P) : Integrable (fun ω => u (X ω)) P := by
  obtain ⟨c, hc, -, hbd⟩ := nl2_U1_lip hu
  have hmeas : Measurable u := hu.2.1.measurable
  refine Integrable.mono' ((integrable_const |u a|).add
    (((hX.sub (integrable_const a)).abs).const_mul c)) ?_ ?_
  · exact (hmeas.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
  · exact ae_of_all _ (fun ω => by simpa [Real.norm_eq_abs] using hbd (X ω))

/-- bounds on a supergradient of a monotone Lipschitz function -/
theorem nl2_supergrad_bounds {v : ℝ → ℝ} {c y g : ℝ} (hmono : Monotone v)
    (hlip : ∀ s t, s < t → v t - v s ≤ c * (t - s))
    (h : ∀ t, v t ≤ v y + g * (t - y)) : 0 ≤ g ∧ g ≤ c := by
  constructor
  · have h1 := h (y + 1)
    have h2 : v y ≤ v (y + 1) := hmono (by linarith)
    nlinarith
  · have h1 := h (y - 1)
    have h2 := hlip (y - 1) y (by linarith)
    nlinarith

theorem nl2_superdiff_facts {m : ℕ} (u : Fin m → ℝ → ℝ) (y θ : Fin (m + 1) → ℝ)
    (h : θ ∈ superdiff (fun y : Fin (m+1) → ℝ => y 0 + ∑ i : Fin m, u i (y i.succ)) y) :
    θ 0 = 1 ∧ ∀ i : Fin m, ∀ t, u i t ≤ u i (y i.succ) + θ i.succ * (t - y i.succ) := by
  have key : ∀ (k : Fin (m+1)) (t : ℝ),
      (∑ k' : Fin (m+1), θ k' * (Function.update y k t k' - y k')) = θ k * (t - y k) := by
    intro k t
    rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'; simp [Function.update_of_ne hk']
    · intro hk; exact absurd (Finset.mem_univ k) hk
  constructor
  · have hup : ∀ t, t + ∑ i : Fin m, u i (y i.succ) ≤
        (y 0 + ∑ i : Fin m, u i (y i.succ)) + θ 0 * (t - y 0) := by
      intro t
      have := h (Function.update y 0 t)
      rw [key] at this
      simpa [Function.update_of_ne (Fin.succ_ne_zero _)] using this
    have h1 := hup (y 0 + 1)
    have h2 := hup (y 0 - 1)
    nlinarith
  · intro i t
    have := h (Function.update y i.succ t)
    rw [key] at this
    have hsum : (∑ j : Fin m, u j (Function.update y i.succ t j.succ)) =
        (∑ j : Fin m, u j (y j.succ)) + (u i t - u i (y i.succ)) := by
      have : (∑ j : Fin m, (u j (Function.update y i.succ t j.succ) - u j (y j.succ))) =
          u i t - u i (y i.succ) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj
          have : j.succ ≠ i.succ := fun e => hj (Fin.succ_injective _ e)
          simp [Function.update_of_ne this]
        · intro hi; exact absurd (Finset.mem_univ i) hi
      rw [Finset.sum_sub_distrib] at this; linarith
    have h0 : Function.update y i.succ t 0 = y 0 :=
      Function.update_of_ne (Fin.succ_ne_zero i).symm _ _
    simp only at this
    rw [h0, hsum] at this
    linarith

theorem nl2_mul_integrable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {f g : Ω → ℝ} (hf : MemLp f ⊤ P) (hg : Integrable g P) :
    Integrable (fun ω => f ω * g ω) P :=
  hf.integrable_mul (memLp_one_iff_integrable.2 hg)

theorem nl2_F2_integrableOn {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (W : Ω → ℝ) (hW : Integrable W P) :
    IntegrableOn (F2 P W) (Set.Icc a b) μ := by
  have hc : Continuous (F2 P W) :=
    (DualSSD.Duality.secondPerformance_properties P W hW).1
  exact hc.continuousOn.integrableOn_compact isCompact_Icc

theorem nl2_slack_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : ℝ) (hab : a ≤ b) (μ : Measure ℝ)
    (hfin : μ Set.univ < ⊤) (hsupp : μ (Set.Icc a b)ᶜ = 0)
    (W V : Ω → ℝ) (hW : Integrable W P) (hV : Integrable V P) :
    (∫ η in Set.Icc a b, (F2 P V η - F2 P W η) ∂μ) =
      (∫ ω, uOfMeasure μ b (W ω) ∂P) - ∫ ω, uOfMeasure μ b (V ω) ∂P := by
  have : IsFiniteMeasure μ := ⟨hfin⟩
  rw [integral_sub (nl2_F2_integrableOn P a b μ V hV) (nl2_F2_integrableOn P a b μ W hW),
    eq_25_measure_utility P a b hab μ hfin hsupp W hW,
    eq_25_measure_utility P a b hab μ hfin hsupp V hV]
  ring

theorem solution
    {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (pr : Problem Ω 𝒵 P m) (z : 𝒵) (X : Fin m → Ω → ℝ)
    (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ)
    (hfeas : pr.Feasible z X)
    (hu : pr.UtilityAdmissible u)
    (hθ : pr.MultiplierAdmissible θ) :
    (∫ ω, pr.H z ω ∂P) ≤ pr.L z X u θ := by
  obtain ⟨-, hX, hD, hG⟩ := hfeas
  have huI : ∀ i {W : Ω → ℝ}, Integrable W P → Integrable (fun ω => u i (W ω)) P :=
    fun i _ hW => nl2_U1_integrable (hu i) hW
  have hTI : ∀ i, Integrable (fun ω => u i (X i ω) - u i (pr.Y i ω) +
      θ i ω * (pr.G i z ω - X i ω)) P := fun i =>
    ((huI i (hX i)).sub (huI i (pr.Y_integrable i))).add
      (nl2_mul_integrable (hθ.1 i) ((pr.G_integrable i z).sub (hX i)))
  unfold Problem.L
  rw [integral_add (pr.H_integrable z) (integrable_finsetSum _ (fun i _ => hTI i)),
    integral_finsetSum _ (fun i _ => hTI i)]
  refine le_add_of_nonneg_right (Finset.sum_nonneg (fun i _ => ?_))
  have hA : Integrable (fun ω => u i (X i ω) - u i (pr.Y i ω)) P :=
    (huI i (hX i)).sub (huI i (pr.Y_integrable i))
  have hB : Integrable (fun ω => θ i ω * (pr.G i z ω - X i ω)) P :=
    nl2_mul_integrable (hθ.1 i) ((pr.G_integrable i z).sub (hX i))
  rw [integral_add hA hB, integral_sub (huI i (hX i)) (huI i (pr.Y_integrable i))]
  have h1 : 0 ≤ (∫ ω, u i (X i ω) ∂P) - ∫ ω, u i (pr.Y i ω) ∂P := by
    obtain ⟨μ, ⟨hμfin, hμsupp, hμu⟩, -⟩ :=
      SSDConstraint.Optimality.U1_eq_uOfMeasure_unique (pr.a i) (pr.b i) (u i) (hu i)
    have hu' : u i = uOfMeasure μ (pr.b i) := hμu
    rw [hu', ← nl2_slack_eq P (pr.a i) (pr.b i) (pr.interval_nonempty i) μ
      (measure_lt_top μ _) hμsupp (X i) (pr.Y i) (hX i) (pr.Y_integrable i)]
    refine setIntegral_nonneg measurableSet_Icc (fun η hη => ?_)
    have := hD i η hη
    linarith
  have h2 : 0 ≤ ∫ ω, θ i ω * (pr.G i z ω - X i ω) ∂P := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hθ.2 i, hG i] with ω h1 h2
    exact mul_nonneg h1 (by simp only [Pi.zero_apply] at h1 ⊢; linarith)
  linarith
