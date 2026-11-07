-- Prove2me | solution 1 for NonlinSSD.Optimality.theorem_2_utility_multipliers
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T03:59:59.904507+00:00
-- url     : https://prove2.me/submissions/f5476427-cfcb-4d4d-9513-aec9c3b384c7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NonlinSSD_Optimality_Basic
import Theorems.Thm_NonlinSSD_Optimality_weak_duality
import Theorems.Thm_NonlinSSD_Optimality_eq_25_measure_utility
import Theorems.Thm_NonlinSSD_Optimality_eq_23_24_measure_multiplier
import Theorems.Thm_NonlinSSD_Optimality_theorem_1_subgradient
import Theorems.Thm_SSDConstraint_Optimality_uOfMeasure_mem_U1
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

section
variable {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}

theorem nl2_L_eq_of_compl (pr : Problem Ω 𝒵 P m) (z : 𝒵) (X : Fin m → Ω → ℝ)
    (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (hu : pr.UtilityAdmissible u) (hC : pr.Complementary z X u θ) :
    pr.L z X u θ = ∫ ω, pr.H z ω ∂P := by
  have hae : (fun ω => pr.H z ω + ∑ i : Fin m,
      (u i (X i ω) - u i (pr.Y i ω) + θ i ω * (pr.G i z ω - X i ω))) =ᵐ[P]
      (fun ω => pr.H z ω + ∑ i : Fin m, (u i (X i ω) - u i (pr.Y i ω))) := by
    have : ∀ᵐ ω ∂P, ∀ i, θ i ω * (X i ω - pr.G i z ω) = 0 := ae_all_iff.2 (fun i => hC.2 i)
    filter_upwards [this] with ω hω
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have e : θ i ω * (pr.G i z ω - X i ω) = -(θ i ω * (X i ω - pr.G i z ω)) := by ring
    rw [e, hω i]; ring
  have hI : ∀ i, Integrable (fun ω => u i (X i ω) - u i (pr.Y i ω)) P := fun i =>
    (nl2_U1_integrable (hu i) (hX i)).sub (nl2_U1_integrable (hu i) (pr.Y_integrable i))
  unfold Problem.L
  rw [integral_congr_ae hae, integral_add (pr.H_integrable z)
    (integrable_finsetSum _ (fun i _ => hI i)), integral_finsetSum _ (fun i _ => hI i)]
  have : ∀ i, (∫ ω, (u i (X i ω) - u i (pr.Y i ω)) ∂P) = 0 := by
    intro i
    rw [integral_sub (nl2_U1_integrable (hu i) (hX i)) (nl2_U1_integrable (hu i) (pr.Y_integrable i)),
      hC.1 i, sub_self]
  simp [this]

theorem nl2_converse (pr : Problem Ω 𝒵 P m) (z : 𝒵) (X : Fin m → Ω → ℝ)
    (u : Fin m → ℝ → ℝ) (θ : Fin m → Ω → ℝ)
    (hu : pr.UtilityAdmissible u) (hθ : pr.MultiplierAdmissible θ)
    (hmax : pr.MaximizesL z X u θ) (hD : pr.Dominates X)
    (hG : ∀ i, X i ≤ᵐ[P] pr.G i z) (hC : pr.Complementary z X u θ) :
    pr.IsOptimal z X := by
  refine ⟨⟨hmax.1, hmax.2.1, hD, hG⟩, fun z' X' hf' => ?_⟩
  calc (∫ ω, pr.H z' ω ∂P) ≤ pr.L z' X' u θ := weak_duality pr z' X' u θ hf' hu hθ
    _ ≤ pr.L z X u θ := hmax.2.2 z' hf'.1 X' hf'.2.1
    _ = ∫ ω, pr.H z ω ∂P := nl2_L_eq_of_compl pr z X u θ hmax.2.1 hu hC

end

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

section
variable {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}

theorem nl2_necessity (pr : Problem Ω 𝒵 P m) (hdom : pr.UniformDominance)
    (z : 𝒵) (X : Fin m → Ω → ℝ) (hopt : pr.IsOptimal z X) :
    ∃ u : Fin m → ℝ → ℝ, ∃ θ : Fin m → Ω → ℝ,
      pr.UtilityAdmissible u ∧ pr.MultiplierAdmissible θ ∧
      pr.MaximizesL z X u θ ∧ pr.Complementary z X u θ := by
  obtain ⟨μ, hμfin, hμsupp, hInC, hΛmax, hslack⟩ :=
    eq_23_24_measure_multiplier pr z X hdom hopt
  have hXi : ∀ i, Integrable (X i) P := hopt.1.2.1
  set u : Fin m → ℝ → ℝ := fun i => uOfMeasure (μ i) (pr.b i) with hu_def
  have hu : pr.UtilityAdmissible u := fun i => by
    have : IsFiniteMeasure (μ i) := ⟨hμfin i⟩
    exact SSDConstraint.Optimality.uOfMeasure_mem_U1 (pr.a i) (pr.b i) (μ i) this (hμsupp i)
  have huI : ∀ i {W : Ω → ℝ}, Integrable W P → Integrable (fun ω => u i (W ω)) P :=
    fun i _ hW => nl2_U1_integrable (hu i) hW
  have hslackU : ∀ i (W : Ω → ℝ), Integrable W P →
      (∫ η in Set.Icc (pr.a i) (pr.b i), (F2 P (pr.Y i) η - F2 P W η) ∂μ i) =
        (∫ ω, u i (W ω) ∂P) - ∫ ω, u i (pr.Y i ω) ∂P := fun i W hW =>
    nl2_slack_eq P (pr.a i) (pr.b i) (pr.interval_nonempty i) (μ i) (hμfin i) (hμsupp i)
      W (pr.Y i) hW (pr.Y_integrable i)
  have hΛU : ∀ z' (X' : Fin m → Ω → ℝ), (∀ i, Integrable (X' i) P) →
      pr.Lambda z' X' μ = (∫ ω, pr.H z' ω ∂P) +
        ∑ i : Fin m, ((∫ ω, u i (X' i ω) ∂P) - ∫ ω, u i (pr.Y i ω) ∂P) := by
    intro z' X' hX'
    unfold Problem.Lambda
    congr 1
    exact Finset.sum_congr rfl (fun i _ => hslackU i (X' i) (hX' i))
  -- (19)
  have h19 : ∀ i, (∫ ω, u i (X i ω) ∂P) = ∫ ω, u i (pr.Y i ω) ∂P := by
    intro i
    have := hslack i
    rw [hslackU i (X i) (hXi i)] at this
    linarith
  -- u(X) ≤ u(G z)
  have hXG : ∀ i, ∀ᵐ ω ∂P, u i (X i ω) ≤ u i (pr.G i z ω) := fun i => by
    filter_upwards [hopt.1.2.2.2 i] with ω hω
    exact (hu i).2.1 hω
  have hGI : ∀ i z', Integrable (fun ω => u i (pr.G i z' ω)) P :=
    fun i z' => huI i (pr.G_integrable i z')
  have hInCG : ∀ z' ∈ pr.Z, pr.InC z' (fun i => pr.G i z') := fun z' hz' =>
    ⟨hz', fun i => pr.G_integrable i z', fun i => Filter.EventuallyLE.refl _ _⟩
  have hΛG : ∀ z' ∈ pr.Z, (∫ ω, pr.H z' ω ∂P) + ∑ i : Fin m, ∫ ω, u i (pr.G i z' ω) ∂P ≤
      (∫ ω, pr.H z ω ∂P) + ∑ i : Fin m, ∫ ω, u i (X i ω) ∂P := by
    intro z' hz'
    have h1 := hΛmax z' (fun i => pr.G i z') (hInCG z' hz')
    rw [hΛU z' _ (fun i => pr.G_integrable i z'), hΛU z X hXi,
      Finset.sum_sub_distrib, Finset.sum_sub_distrib] at h1
    linarith
  -- u(X) = u(G z) a.e.
  have hXGeq : ∀ i, ∀ᵐ ω ∂P, u i (X i ω) = u i (pr.G i z ω) := by
    have h1 := hΛG z hopt.1.1
    have hle : ∀ i, (∫ ω, u i (X i ω) ∂P) ≤ ∫ ω, u i (pr.G i z ω) ∂P := fun i =>
      integral_mono_ae (huI i (hXi i)) (hGI i z) (hXG i)
    have hsum : ∑ i : Fin m, ((∫ ω, u i (pr.G i z ω) ∂P) - ∫ ω, u i (X i ω) ∂P) = 0 := by
      apply le_antisymm
      · rw [Finset.sum_sub_distrib]; linarith
      · exact Finset.sum_nonneg (fun i _ => sub_nonneg.2 (hle i))
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sub_nonneg.2 (hle i))] at hsum
    intro i
    have h0 : (∫ ω, (u i (pr.G i z ω) - u i (X i ω)) ∂P) = 0 := by
      rw [integral_sub (hGI i z) (huI i (hXi i))]; exact hsum i (Finset.mem_univ i)
    have hI0 : Integrable (fun ω => u i (pr.G i z ω) - u i (X i ω)) P :=
      (hGI i z).sub (huI i (hXi i))
    have hnn0 : 0 ≤ᵐ[P] (fun ω => u i (pr.G i z ω) - u i (X i ω)) := by
      filter_upwards [hXG i] with ω hω
      simp only [Pi.zero_apply]; linarith
    rw [integral_eq_zero_iff_of_nonneg_ae hnn0 hI0] at h0
    filter_upwards [h0] with ω hω
    simp only [Pi.zero_apply] at hω
    linarith
  -- Lipschitz constants
  have hlip : ∀ i, ∃ c : ℝ, 0 ≤ c ∧ (∀ s t, s < t → u i t - u i s ≤ c * (t - s)) :=
    fun i => by
      obtain ⟨c, hc, h1, -⟩ := nl2_U1_lip (hu i)
      exact ⟨c, hc, h1⟩
  choose c hc hcl using hlip
  -- Theorem 1 data
  set φ : 𝒵 → Ω → Fin (m + 1) → ℝ :=
    fun z ω => Fin.cons (pr.H z ω) (fun i => pr.G i z ω) with hφ_def
  set f : (Fin (m + 1) → ℝ) → ℝ := fun y => y 0 + ∑ i : Fin m, u i (y i.succ) with hf_def
  have hfφ : ∀ z' ω, f (φ z' ω) = pr.H z' ω + ∑ i : Fin m, u i (pr.G i z' ω) := fun _ _ => rfl
  have hφ_int : ∀ z', Integrable (φ z') P := by
    intro z'
    refine Integrable.of_eval (fun k => ?_)
    refine Fin.cases ?_ (fun i => ?_) k
    · exact pr.H_integrable z'
    · exact pr.G_integrable i z'
  have hφ_cont : ∀ z₀, Filter.Tendsto
      (fun z' => ∫ ω, ‖φ z' ω - φ z₀ ω‖ ∂P) (nhds z₀) (nhds 0) := by
    intro z₀
    have hT : Filter.Tendsto (fun z' => (∫ ω, |pr.H z' ω - pr.H z₀ ω| ∂P) +
        ∑ i : Fin m, ∫ ω, |pr.G i z' ω - pr.G i z₀ ω| ∂P) (nhds z₀) (nhds 0) := by
      have := (pr.H_L1_cont z₀).add (tendsto_finsetSum (Finset.univ : Finset (Fin m))
        (fun i _ => pr.G_L1_cont i z₀))
      simpa using this
    refine squeeze_zero (fun z' => integral_nonneg (fun ω => norm_nonneg _)) (fun z' => ?_) hT
    have hIH : Integrable (fun ω => |pr.H z' ω - pr.H z₀ ω|) P :=
      ((pr.H_integrable z').sub (pr.H_integrable z₀)).abs
    have hIG : ∀ i, Integrable (fun ω => |pr.G i z' ω - pr.G i z₀ ω|) P := fun i =>
      ((pr.G_integrable i z').sub (pr.G_integrable i z₀)).abs
    rw [← integral_finsetSum _ (fun i _ => hIG i), ← integral_add hIH
      (integrable_finsetSum _ (fun i _ => hIG i))]
    refine integral_mono_of_nonneg (ae_of_all _ (fun ω => norm_nonneg _))
      (hIH.add (integrable_finsetSum _ (fun i _ => hIG i))) (ae_of_all _ (fun ω => ?_))
    have hnn : 0 ≤ ∑ i : Fin m, |pr.G i z' ω - pr.G i z₀ ω| :=
      Finset.sum_nonneg (fun i _ => abs_nonneg _)
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun k => ?_)
    refine Fin.cases ?_ (fun i => ?_) k
    · simp only [φ, Pi.sub_apply, Fin.cons_zero, Real.norm_eq_abs]
      linarith
    · simp only [φ, Pi.sub_apply, Fin.cons_succ, Real.norm_eq_abs]
      have := Finset.single_le_sum (f := fun j => |pr.G j z' ω - pr.G j z₀ ω|)
        (fun j _ => abs_nonneg _) (Finset.mem_univ i)
      have := abs_nonneg (pr.H z' ω - pr.H z₀ ω)
      linarith
  have hφ_sample : ∀ᵐ ω ∂P, ConcaveOn ℝ Set.univ (fun z' => φ z' ω) ∧
      Continuous (fun z' => φ z' ω) := by
    filter_upwards [pr.H_sample, ae_all_iff.2 pr.G_sample] with ω hH hG
    refine ⟨⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa [φ] using hH.1.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
      · simpa [φ] using (hG i).1.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
    · refine continuous_pi (fun k => ?_)
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa [φ] using hH.2
      · simpa [φ] using (hG i).2
  have hf_concave : ConcaveOn ℝ Set.univ f := by
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [f, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
    have hci : ∀ i : Fin m, a * u i (x i.succ) + b * u i (y i.succ) ≤
        u i (a * x i.succ + b * y i.succ) := fun i => by
      simpa [smul_eq_mul] using (hu i).1.2 (Set.mem_univ (x i.succ)) (Set.mem_univ (y i.succ))
        ha hb hab
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hci i)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hs
    have e : a * (x 0 + ∑ i : Fin m, u i (x i.succ)) + b * (y 0 + ∑ i : Fin m, u i (y i.succ)) =
        (a * x 0 + b * y 0) + (a * ∑ i : Fin m, u i (x i.succ) + b * ∑ i : Fin m, u i (y i.succ)) := by
      ring
    rw [e]; linarith
  have hf_monotone : Monotone f := fun x y hxy =>
    add_le_add (hxy 0) (Finset.sum_le_sum (fun i _ => (hu i).2.1 (hxy i.succ)))
  -- superdifferential bounds
  have hsd : ∀ (y θ : Fin (m + 1) → ℝ), θ ∈ superdiff f y →
      θ 0 = 1 ∧ ∀ i : Fin m, (∀ t, u i t ≤ u i (y i.succ) + θ i.succ * (t - y i.succ)) ∧
        0 ≤ θ i.succ ∧ θ i.succ ≤ c i := by
    intro y θ hθ
    obtain ⟨h0, h1⟩ := nl2_superdiff_facts u y θ hθ
    refine ⟨h0, fun i => ⟨h1 i, nl2_supergrad_bounds (hu i).2.1 (hcl i) (h1 i)⟩⟩
  have hf_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ y (θ : Fin (m + 1) → ℝ), θ ∈ superdiff f y → ‖θ‖ ≤ C := by
    have hcs : 0 ≤ ∑ i : Fin m, c i := Finset.sum_nonneg (fun i _ => hc i)
    refine ⟨1 + ∑ i : Fin m, c i, by positivity, fun y θ hθ => ?_⟩
    obtain ⟨h0, h1⟩ := hsd y θ hθ
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 (fun k => ?_)
    refine Fin.cases ?_ (fun i => ?_) k
    · rw [h0]; simp; linarith
    · obtain ⟨-, hn, hcb⟩ := h1 i
      rw [Real.norm_eq_abs, abs_of_nonneg hn]
      have := Finset.single_le_sum (f := c) (fun j _ => hc j) (Finset.mem_univ i)
      linarith
  have hzmax : ∀ z' ∈ pr.Z, (∫ ω, f (φ z' ω) ∂P) ≤ ∫ ω, f (φ z ω) ∂P := by
    intro z' hz'
    simp only [hfφ]
    rw [integral_add (pr.H_integrable z') (integrable_finsetSum _ (fun i _ => hGI i z')),
      integral_add (pr.H_integrable z) (integrable_finsetSum _ (fun i _ => hGI i z)),
      integral_finsetSum _ (fun i _ => hGI i z'), integral_finsetSum _ (fun i _ => hGI i z)]
    have h1 := hΛG z' hz'
    have h2 : ∑ i : Fin m, (∫ ω, u i (X i ω) ∂P) ≤ ∑ i : Fin m, ∫ ω, u i (pr.G i z ω) ∂P :=
      Finset.sum_le_sum (fun i _ => integral_mono_ae (huI i (hXi i)) (hGI i z) (hXG i))
    linarith
  obtain ⟨θv, hθmem, hθsd, hθlin⟩ :=
    (theorem_1_subgradient P (m + 1) φ hφ_int hφ_cont hφ_sample f hf_concave hf_monotone
      hf_bound pr.Z pr.Z_convex z hopt.1.1).1 hzmax
  have hsdae := hθsd.mono (fun ω hω => hsd (φ z ω) (θv ω) hω)
  set θ : Fin m → Ω → ℝ := fun i ω => θv ω i.succ with hθ_def
  have hθ_bd : ∀ i, ∀ᵐ ω ∂P, 0 ≤ θ i ω ∧ θ i ω ≤ c i := fun i =>
    hsdae.mono (fun ω hω => ⟨(hω.2 i).2.1, (hω.2 i).2.2⟩)
  have hθsup : ∀ i, ∀ᵐ ω ∂P, ∀ t, u i t ≤ u i (pr.G i z ω) + θ i ω * (t - pr.G i z ω) :=
    fun i => hsdae.mono (fun ω hω => (hω.2 i).1)
  have hθmemi : ∀ i, MemLp (θ i) ⊤ P := fun i =>
    MemLp.of_le hθmem ((continuous_apply i.succ).comp_aestronglyMeasurable hθmem.1)
      (ae_of_all _ (fun ω => norm_le_pi_norm (θv ω) i.succ))
  have hθadm : pr.MultiplierAdmissible θ :=
    ⟨hθmemi, fun i => (hθ_bd i).mono (fun ω hω => hω.1)⟩
  -- (20)
  have h20 : ∀ i, ∀ᵐ ω ∂P, θ i ω * (X i ω - pr.G i z ω) = 0 := by
    intro i
    filter_upwards [hθ_bd i, hθsup i, hXGeq i, hopt.1.2.2.2 i] with ω hb hs he hle
    have h1 := hs (X i ω)
    have h2 : 0 ≤ θ i ω * (pr.G i z ω - X i ω) := mul_nonneg hb.1 (by linarith)
    nlinarith
  have hcompl : pr.Complementary z X u θ := ⟨h19, h20⟩
  refine ⟨u, θ, hu, hθadm, ⟨hopt.1.1, hXi, fun z' hz' X' hX' => ?_⟩, hcompl⟩
  -- (18)
  have hθG : ∀ i z', Integrable (fun ω => θ i ω * pr.G i z' ω) P := fun i z' =>
    nl2_mul_integrable (hθmemi i) (pr.G_integrable i z')
  have hθX : ∀ i (W : Ω → ℝ), Integrable W P → Integrable (fun ω => θ i ω * W ω) P :=
    fun i W hW => nl2_mul_integrable (hθmemi i) hW
  set A : 𝒵 → Ω → ℝ := fun z' ω => pr.H z' ω + ∑ i : Fin m, θ i ω * pr.G i z' ω with hA_def
  set B : Ω → ℝ := fun ω => ∑ i : Fin m,
    (u i (pr.G i z ω) - θ i ω * pr.G i z ω - u i (pr.Y i ω)) with hB_def
  have hAI : ∀ z', Integrable (A z') P := fun z' =>
    (pr.H_integrable z').add (integrable_finsetSum _ (fun i _ => hθG i z'))
  have hBI : Integrable B P := integrable_finsetSum _ (fun i _ =>
    ((hGI i z).sub (hθG i z)).sub (huI i (pr.Y_integrable i)))
  have hLI : ∀ z' (X' : Fin m → Ω → ℝ), (∀ i, Integrable (X' i) P) →
      Integrable (fun ω => pr.H z' ω + ∑ i : Fin m,
        (u i (X' i ω) - u i (pr.Y i ω) + θ i ω * (pr.G i z' ω - X' i ω))) P :=
    fun z' X' hX' => (pr.H_integrable z').add (integrable_finsetSum _ (fun i _ =>
      ((huI i (hX' i)).sub (huI i (pr.Y_integrable i))).add
        (hθX i _ ((pr.G_integrable i z').sub (hX' i)))))
  have hAle : (∫ ω, A z' ω ∂P) ≤ ∫ ω, A z ω ∂P := by
    have h0 : ∀ᵐ ω ∂P, θv ω 0 = 1 := hsdae.mono (fun ω hω => hω.1)
    have hAeq : ∀ z'', (fun ω => ∑ k : Fin (m + 1), θv ω k * φ z'' ω k) =ᵐ[P] A z'' := by
      intro z''
      filter_upwards [h0] with ω hω
      simp [Fin.sum_univ_succ, φ, A, θ, hω]
    have := hθlin z' hz'
    rwa [integral_congr_ae (hAeq z'), integral_congr_ae (hAeq z)] at this
  have hle1 : ∀ᵐ ω ∂P, (pr.H z' ω + ∑ i : Fin m,
      (u i (X' i ω) - u i (pr.Y i ω) + θ i ω * (pr.G i z' ω - X' i ω))) ≤ A z' ω + B ω := by
    filter_upwards [ae_all_iff.2 hθsup] with ω hω
    simp only [A, B, add_assoc, ← Finset.sum_add_distrib]
    refine add_le_add le_rfl (Finset.sum_le_sum (fun i _ => ?_))
    have := hω i (X' i ω)
    nlinarith
  have heq2 : (fun ω => pr.H z ω + ∑ i : Fin m,
      (u i (X i ω) - u i (pr.Y i ω) + θ i ω * (pr.G i z ω - X i ω))) =ᵐ[P]
      (fun ω => A z ω + B ω) := by
    filter_upwards [ae_all_iff.2 hXGeq, ae_all_iff.2 h20] with ω he h2
    simp only [A, B, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have := he i
    have := h2 i
    nlinarith
  calc pr.L z' X' u θ ≤ ∫ ω, (A z' ω + B ω) ∂P :=
        integral_mono_ae (hLI z' X' hX') ((hAI z').add hBI) hle1
    _ = (∫ ω, A z' ω ∂P) + ∫ ω, B ω ∂P := integral_add (hAI z') hBI
    _ ≤ (∫ ω, A z ω ∂P) + ∫ ω, B ω ∂P := by linarith
    _ = ∫ ω, (A z ω + B ω) ∂P := (integral_add (hAI z) hBI).symm
    _ = pr.L z X u θ := (integral_congr_ae heq2).symm

end

theorem solution
    {Ω 𝒵 : Type*} [MeasurableSpace Ω]
    [AddCommGroup 𝒵] [Module ℝ 𝒵] [TopologicalSpace 𝒵]
    [IsTopologicalAddGroup 𝒵] [ContinuousSMul ℝ 𝒵]
    [LocallyConvexSpace ℝ 𝒵] [T2Space 𝒵]
    [TopologicalSpace.SeparableSpace 𝒵]
    {P : Measure Ω} [IsProbabilityMeasure P] {m : ℕ}
    (pr : Problem Ω 𝒵 P m) (hdom : pr.UniformDominance) :
    (∀ z : 𝒵, ∀ X : Fin m → Ω → ℝ,
      pr.IsOptimal z X →
      ∃ u : Fin m → ℝ → ℝ, ∃ θ : Fin m → Ω → ℝ,
        pr.UtilityAdmissible u ∧ pr.MultiplierAdmissible θ ∧
        pr.MaximizesL z X u θ ∧ pr.Complementary z X u θ) ∧
    (∀ z : 𝒵, ∀ X : Fin m → Ω → ℝ,
      ∀ u : Fin m → ℝ → ℝ, ∀ θ : Fin m → Ω → ℝ,
      pr.UtilityAdmissible u → pr.MultiplierAdmissible θ →
      pr.MaximizesL z X u θ → pr.Dominates X →
      (∀ i, X i ≤ᵐ[P] pr.G i z) →
      pr.Complementary z X u θ → pr.IsOptimal z X) :=
  ⟨fun z X hopt => nl2_necessity pr hdom z X hopt,
   fun z X u θ hu hθ hmax hD hG hC => nl2_converse pr z X u θ hu hθ hmax hD hG hC⟩
