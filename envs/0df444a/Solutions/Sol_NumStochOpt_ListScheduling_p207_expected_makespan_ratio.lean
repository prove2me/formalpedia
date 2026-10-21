-- Prove2me | solution 1 for NumStochOpt.ListScheduling.p207_expected_makespan_ratio
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T00:41:43.043763+00:00
-- url     : https://prove2.me/submissions/618b0d8e-b771-48c2-b710-3353f5f03763

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open NumStochOpt.ListScheduling


lemma nls_load_sum {n m : ℕ} (p : ℕ → ℝ) (σ : Fin n → Fin m) :
    ∑ i : Fin m, machineLoad p σ i = ∑ j : Fin n, p j := by
  unfold machineLoad
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp

lemma nls_lower {n m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (σ : Fin n → Fin m) :
    (∑ j : Fin n, p j) / m ≤ makespan p σ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  rw [div_le_iff₀ hmpos, ← nls_load_sum p σ]
  have h : ∀ i, machineLoad p σ i ≤ makespan p σ := fun i =>
    le_ciSup (Set.finite_range (fun i : Fin m => machineLoad p σ i)).bddAbove i
  calc ∑ i, machineLoad p σ i ≤ ∑ _i : Fin m, makespan p σ := Finset.sum_le_sum (fun i _ => h i)
    _ = makespan p σ * m := by simp [mul_comm]

lemma nls_opt_lower {n m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) :
    (∑ j : Fin n, p j) / m ≤ optMakespan n m p := by
  haveI : Nonempty (Fin n → Fin m) := ⟨fun _ => ⟨0, hm⟩⟩
  exact le_ciInf (fun σ => nls_lower hm p σ)

lemma nls_greedy {m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (B : ℝ) (hB0 : 0 ≤ B) :
    ∀ n : ℕ, (∀ j < n, p j ≤ B) → ∃ σ : ℕ → Fin m, ∀ i : Fin m,
      ∑ j ∈ Finset.range n, (if σ j = i then p j else 0) ≤
        (∑ j ∈ Finset.range n, p j) / m + B := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨fun _ => ⟨0, hm⟩, fun i => ?_⟩
    simpa using hB0
  | succ n ih =>
    intro hB'
    obtain ⟨σ, hσ⟩ := ih (fun j hj => hB' j (by omega))
    set L : Fin m → ℝ := fun i => ∑ j ∈ Finset.range n, (if σ j = i then p j else 0) with hL
    obtain ⟨i0, -, hi0⟩ := Finset.exists_min_image Finset.univ L Finset.univ_nonempty
    have hsumL : ∑ i, L i = ∑ j ∈ Finset.range n, p j := by
      simp only [hL]; rw [Finset.sum_comm]; simp
    have hmin : L i0 ≤ (∑ j ∈ Finset.range n, p j) / m := by
      rw [le_div_iff₀ hmpos]
      calc L i0 * m = ∑ _i : Fin m, L i0 := by simp [mul_comm]
        _ ≤ ∑ i, L i := Finset.sum_le_sum (fun i _ => hi0 i (Finset.mem_univ i))
        _ = _ := hsumL
    refine ⟨Function.update σ n i0, fun i => ?_⟩
    have hrest : ∑ j ∈ Finset.range n, (if Function.update σ n i0 j = i then p j else 0) = L i := by
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Function.update_of_ne (Finset.mem_range.1 hj).ne]
    rw [Finset.sum_range_succ (fun j => if Function.update σ n i0 j = i then p j else 0) n,
      Finset.sum_range_succ p n, hrest, Function.update_self]
    have hpn := hp n
    have hpnB := hB' n (Nat.lt_succ_self n)
    have hdiv : 0 ≤ p n / m := by positivity
    have hadd : (∑ j ∈ Finset.range n, p j + p n) / m = (∑ j ∈ Finset.range n, p j) / m + p n / m := by
      rw [add_div]
    rw [hadd]
    by_cases h : i0 = i
    · subst h
      simp only [if_true]
      linarith
    · simp only [h, if_false, add_zero]
      have := hσ i
      linarith

lemma nls_opt_upper {n m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) :
    optMakespan n m p ≤ (∑ j : Fin n, p j) / m + maxProcTime n p := by
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hB0 : 0 ≤ maxProcTime n p := Real.iSup_nonneg (fun i => hp _)
  have hpB : ∀ j < n, p j ≤ maxProcTime n p := fun j hj =>
    le_ciSup (f := fun i : Fin n => p i) (Set.finite_range _).bddAbove ⟨j, hj⟩
  obtain ⟨σ, hσ⟩ := nls_greedy hm p hp _ hB0 n hpB
  have hSum : ∑ j : Fin n, p j = ∑ j ∈ Finset.range n, p j :=
    Fin.sum_univ_eq_sum_range (fun j => p j) n
  have hms : makespan p (fun j : Fin n => σ j) ≤ (∑ j : Fin n, p j) / m + maxProcTime n p := by
    refine Real.iSup_le (fun i => ?_) ?_
    · have : machineLoad p (fun j : Fin n => σ j) i =
          ∑ j ∈ Finset.range n, (if σ j = i then p j else 0) :=
        Fin.sum_univ_eq_sum_range (fun j => if σ j = i then p j else 0) n
      rw [this, hSum]
      exact hσ i
    · have : 0 ≤ (∑ j : Fin n, p j) / m := div_nonneg (Finset.sum_nonneg (fun j _ => hp _)) (by positivity)
      linarith
  refine le_trans ?_ hms
  refine ciInf_le (f := fun σ : Fin n → Fin m => makespan p σ) ⟨0, ?_⟩ (fun j : Fin n => σ j)
  rintro _ ⟨τ, rfl⟩
  exact Real.iSup_nonneg (fun i => Finset.sum_nonneg (fun j _ => by
    show (0 : ℝ) ≤ (if τ j = i then p (j : ℕ) else 0)
    split_ifs
    · exact hp _
    · exact le_rfl))


lemma nls_ii {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P) :
    Tendsto (fun n : ℕ => (∫ ω, maxProcTime n (fun j => p j ω) ∂P) / Real.sqrt n)
      atTop (𝓝 0) := by
  -- the truncated square
  set ind : ℝ → ℝ → ℝ := fun a x => Set.indicator (Set.Ioi a) (fun y : ℝ => y ^ 2) x with hind
  have hind_meas : ∀ a, Measurable (ind a) := fun a =>
    (measurable_id.pow_const 2).indicator measurableSet_Ioi
  have hind_le : ∀ a x, ind a x ≤ x ^ 2 := by
    intro a x
    simp only [hind, Set.indicator]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg x
  have hind_nn : ∀ a x, 0 ≤ ind a x := by
    intro a x
    simp only [hind, Set.indicator]
    split_ifs
    · exact sq_nonneg x
    · exact le_rfl
  have hint2 : ∀ j, Integrable (fun ω => p j ω ^ 2) P := fun j =>
    ((hident j).sq).symm.integrable_snd hsq
  have hint1 : ∀ j, Integrable (p j) P := by
    intro j
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hint2 j))
      (hmeas j).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg j ω)]
    show p j ω ≤ 1 + p j ω ^ 2
    nlinarith [sq_nonneg (p j ω - 1), hnonneg j ω]
  have hindint : ∀ a j, Integrable (fun ω => ind a (p j ω)) P := by
    intro a j
    refine Integrable.mono' (hint2 j) ((hind_meas a).comp (hmeas j)).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hind_nn _ _)]
    exact hind_le _ _
  -- the max
  set M : ℕ → Ω → ℝ := fun n ω => maxProcTime n (fun j => p j ω) with hM
  have hMmeas : ∀ n, Measurable (M n) := by
    intro n
    exact Measurable.iSup (fun i : Fin n => hmeas i)
  have hMnn : ∀ n ω, 0 ≤ M n ω := fun n ω =>
    Real.iSup_nonneg (fun i => hnonneg _ _)
  have hMle_sum : ∀ n ω, M n ω ≤ ∑ j : Fin n, p j ω := by
    intro n ω
    refine Real.iSup_le (fun i => ?_) (Finset.sum_nonneg (fun j _ => hnonneg _ _))
    exact Finset.single_le_sum (f := fun j : Fin n => p j ω) (fun j _ => hnonneg _ _) (Finset.mem_univ i)
  have hMint : ∀ n, Integrable (M n) P := by
    intro n
    have hsi : Integrable (fun ω => ∑ j : Fin n, p j ω) P :=
      integrable_finsetSum _ (fun j _ => hint1 j)
    refine Integrable.mono' hsi (hMmeas n).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hMnn n ω)]
    exact hMle_sum n ω
  -- truncation bound
  have hbound : ∀ n : ℕ, ∀ a : ℝ, 0 < a → ∀ ω, M n ω ≤ a + (1 / a) * ∑ j : Fin n, ind a (p j ω) := by
    intro n a ha ω
    have hs : 0 ≤ (1 / a) * ∑ j : Fin n, ind a (p j ω) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hind_nn _ _))
    refine Real.iSup_le (fun i => ?_) (by linarith)
    have hi : ind a (p i ω) ≤ ∑ j : Fin n, ind a (p j ω) :=
      Finset.single_le_sum (f := fun j : Fin n => ind a (p j ω)) (fun j _ => hind_nn _ _)
        (Finset.mem_univ i)
    have hpi := hnonneg i ω
    by_cases hc : p i ω ≤ a
    · linarith
    · push_neg at hc
      have h1 : ind a (p i ω) = p i ω ^ 2 := by simp [hind, hc]
      have h2 : p i ω ≤ (1 / a) * ind a (p i ω) := by
        rw [h1, one_div, inv_mul_eq_div, le_div_iff₀ ha]
        nlinarith
      have h3 : (1 / a) * ind a (p i ω) ≤ (1 / a) * ∑ j : Fin n, ind a (p j ω) :=
        mul_le_mul_of_nonneg_left hi (by positivity)
      linarith
  -- expectation of the truncation
  have hE : ∀ n : ℕ, ∀ a : ℝ, 0 < a →
      ∫ ω, M n ω ∂P ≤ a + (1 / a) * (n * ∫ ω, ind a (p 0 ω) ∂P) := by
    intro n a ha
    have hsumint : Integrable (fun ω => ∑ j : Fin n, ind a (p j ω)) P :=
      integrable_finsetSum _ (fun j _ => hindint a j)
    have h1 : ∫ ω, M n ω ∂P ≤ ∫ ω, (a + (1 / a) * ∑ j : Fin n, ind a (p j ω)) ∂P := by
      refine integral_mono (hMint n) ?_ (hbound n a ha)
      exact (integrable_const a).add (hsumint.const_mul _)
    have h2 : ∫ ω, (a + (1 / a) * ∑ j : Fin n, ind a (p j ω)) ∂P =
        a + (1 / a) * (n * ∫ ω, ind a (p 0 ω) ∂P) := by
      rw [integral_add (integrable_const a) (hsumint.const_mul _)]
      rw [integral_const, integral_const_mul]
      have h3 : ∀ j : Fin n, ∫ ω, ind a (p j ω) ∂P = ∫ ω, ind a (p 0 ω) ∂P := fun j =>
        ((hident j).comp (hind_meas a)).integral_eq
      rw [integral_finsetSum (Finset.univ : Finset (Fin n))
        (f := fun (j : Fin n) ω => ind a (p j ω)) (fun j _ => hindint a j)]
      simp [h3]
    linarith
  -- the main estimate
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun δ hδ => ?_⟩
  · refine Eventually.of_forall (fun n => lt_of_lt_of_le ha ?_)
    exact div_nonneg (integral_nonneg (hMnn n)) (Real.sqrt_nonneg _)
  · set ε : ℝ := δ / 2 with hε
    have hεpos : 0 < ε := by positivity
    -- G n → 0
    have hG : Tendsto (fun n : ℕ => ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) atTop (𝓝 0) := by
      have := tendsto_integral_of_dominated_convergence (μ := P)
        (F := fun (n : ℕ) ω => ind (ε * Real.sqrt n) (p 0 ω)) (f := fun _ => (0 : ℝ))
        (bound := fun ω => p 0 ω ^ 2)
        (fun n => ((hind_meas _).comp (hmeas 0)).aestronglyMeasurable) hsq
        (fun n => ae_of_all _ (fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hind_nn _ _)]; exact hind_le _ _))
        (ae_of_all _ (fun ω => ?_))
      · simpa using this
      · have hT : Tendsto (fun n : ℕ => ε * Real.sqrt n) atTop atTop :=
          Filter.Tendsto.const_mul_atTop hεpos
            (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
        have hev := hT.eventually_gt_atTop (p 0 ω)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        simp [hind, Set.indicator, not_lt.mpr hn.le]
    have hG' := (tendsto_order.1 hG).2 (ε ^ 2) (by positivity)
    have hn1 : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
    filter_upwards [hG', hn1] with n hGn hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hapos : 0 < ε * Real.sqrt n := by positivity
    have hEn := hE n (ε * Real.sqrt n) hapos
    have hsqsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    rw [div_lt_iff₀ hsq_pos]
    have e1 : (1 / (ε * Real.sqrt n)) * (n * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) =
        Real.sqrt n * ((1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) := by
      generalize Real.sqrt n = s at hsqsq hsq_pos hapos ⊢
      rw [← hsqsq]; field_simp
    have e2 : (1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P < ε := by
      rw [one_div, inv_mul_lt_iff₀ hεpos]
      nlinarith
    have : ∫ ω, M n ω ∂P < δ * Real.sqrt n := by
      have e3 : ε * Real.sqrt n + Real.sqrt n * ((1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P)
          < δ * Real.sqrt n := by
        have : Real.sqrt n * ((1 / ε) * ∫ ω, ind (ε * Real.sqrt n) (p 0 ω) ∂P) < Real.sqrt n * ε :=
          mul_lt_mul_of_pos_left e2 hsq_pos
        nlinarith
      linarith
    exact this


theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    Tendsto
      (fun n : ℕ => (∫ ω, optMakespan n (m n) (fun j => p j ω) ∂P) / (n * μ / m n))
      atTop (𝓝 1) := by
  have hint2 : ∀ j, Integrable (fun ω => p j ω ^ 2) P := fun j =>
    ((hident j).sq).symm.integrable_snd hsq
  have hint1 : ∀ j, Integrable (p j) P := by
    intro j
    refine Integrable.mono' ((integrable_const (1 : ℝ)).add (hint2 j))
      (hmeas j).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg j ω)]
    show p j ω ≤ 1 + p j ω ^ 2
    nlinarith [sq_nonneg (p j ω - 1), hnonneg j ω]
  set M : ℕ → Ω → ℝ := fun n ω => maxProcTime n (fun j => p j ω) with hM
  have hMmeas : ∀ n, Measurable (M n) := fun n => Measurable.iSup (fun i : Fin n => hmeas i)
  have hMnn : ∀ n ω, 0 ≤ M n ω := fun n ω => Real.iSup_nonneg (fun i => hnonneg _ _)
  have hMle_sum : ∀ n ω, M n ω ≤ ∑ j : Fin n, p j ω := by
    intro n ω
    refine Real.iSup_le (fun i => ?_) (Finset.sum_nonneg (fun j _ => hnonneg _ _))
    exact Finset.single_le_sum (f := fun j : Fin n => p j ω) (fun j _ => hnonneg _ _) (Finset.mem_univ i)
  have hSint : ∀ n, Integrable (fun ω => ∑ j : Fin n, p j ω) P := fun n =>
    integrable_finsetSum _ (fun j _ => hint1 j)
  have hMint : ∀ n, Integrable (M n) P := by
    intro n
    refine Integrable.mono' (hSint n) (hMmeas n).aestronglyMeasurable
      (ae_of_all _ (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hMnn n ω)]
    exact hMle_sum n ω
  have hSmean : ∀ n, ∫ ω, ∑ j : Fin n, p j ω ∂P = n * μ := by
    intro n
    rw [integral_finsetSum (Finset.univ : Finset (Fin n)) (f := fun (j : Fin n) ω => p j ω)
      (fun j _ => hint1 j)]
    have : ∀ j : Fin n, ∫ ω, p j ω ∂P = μ := fun j => by rw [(hident j).integral_eq, hmean]
    simp [this]
  -- the optimum
  set F : ℕ → Ω → ℝ := fun n ω => optMakespan n (m n) (fun j => p j ω) with hF
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    show Measurable (fun ω => ⨅ σ : Fin n → Fin (m n), makespan (fun j => p j ω) σ)
    refine Measurable.iInf (fun σ => ?_)
    show Measurable (fun ω => ⨆ i : Fin (m n), machineLoad (fun j => p j ω) σ i)
    refine Measurable.iSup (fun i => ?_)
    unfold machineLoad
    refine Finset.measurable_sum _ (fun j _ => ?_)
    by_cases h : σ j = i
    · simp only [h, if_true]; exact hmeas _
    · simp only [h, if_false]; exact measurable_const
  have hFlow : ∀ n ω, (∑ j : Fin n, p j ω) / (m n : ℝ) ≤ F n ω := fun n ω =>
    nls_opt_lower (n := n) (hm n) (fun j => p j ω)
  have hFup : ∀ n ω, F n ω ≤ (∑ j : Fin n, p j ω) / (m n : ℝ) + M n ω := fun n ω =>
    nls_opt_upper (n := n) (hm n) (fun j => p j ω) (fun j => hnonneg j ω)
  have hFint : ∀ n, Integrable (F n) P := by
    intro n
    have hg : Integrable (fun ω => (∑ j : Fin n, p j ω) / (m n : ℝ) + M n ω) P :=
      ((hSint n).div_const _).add (hMint n)
    refine Integrable.mono' hg (hFmeas n).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
    have h0 : 0 ≤ F n ω := le_trans (div_nonneg (Finset.sum_nonneg (fun j _ => hnonneg _ _))
      (by positivity)) (hFlow n ω)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact hFup n ω
  have hElow : ∀ n : ℕ, (n : ℝ) * μ / m n ≤ ∫ ω, F n ω ∂P := by
    intro n
    have := integral_mono ((hSint n).div_const (m n : ℝ)) (hFint n) (hFlow n)
    rw [integral_div, hSmean] at this
    exact this
  have hEup : ∀ n : ℕ, ∫ ω, F n ω ∂P ≤ (n : ℝ) * μ / m n + ∫ ω, M n ω ∂P := by
    intro n
    have hg : Integrable (fun ω => (∑ j : Fin n, p j ω) / (m n : ℝ) + M n ω) P :=
      ((hSint n).div_const _).add (hMint n)
    have := integral_mono (hFint n) hg (hFup n)
    rw [integral_add ((hSint n).div_const (m n : ℝ)) (hMint n), integral_div, hSmean] at this
    exact this
  -- (ii)
  have hii := nls_ii p hmeas hindep hident hnonneg hsq
  -- big-O
  obtain ⟨C, hC⟩ := hmO.bound
  have hC' : ∀ᶠ n : ℕ in atTop, (m n : ℝ) ≤ C * Real.sqrt n := by
    filter_upwards [hC] with n hn
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hn
    exact hn
  have hup : Tendsto (fun n : ℕ => 1 + (C / μ) * ((∫ ω, M n ω ∂P) / Real.sqrt n)) atTop (𝓝 1) := by
    have := (hii.const_mul (C / μ)).const_add 1
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hmpos : (0 : ℝ) < m n := by exact_mod_cast hm n
    rw [le_div_iff₀ (by positivity)]
    linarith [hElow n]
  · filter_upwards [hC', eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hmpos : (0 : ℝ) < m n := by exact_mod_cast hm n
    have hsq0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    have hsqsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    have hE0 : 0 ≤ ∫ ω, M n ω ∂P := integral_nonneg (hMnn n)
    rw [div_le_iff₀ (by positivity)]
    have h1 := hEup n
    -- target: ∫F ≤ (1 + C/μ * (E/√n)) * (nμ/m)
    have h2 : (∫ ω, M n ω ∂P) ≤ (C / μ * ((∫ ω, M n ω ∂P) / Real.sqrt n)) * (n * μ / m n) := by
      have : (C / μ * ((∫ ω, M n ω ∂P) / Real.sqrt n)) * (n * μ / m n) =
          (C * Real.sqrt n / m n) * (∫ ω, M n ω ∂P) := by
        generalize Real.sqrt n = s at hsq0 hsqsq ⊢
        rw [← hsqsq]; field_simp
      rw [this]
      have h3 : 1 ≤ C * Real.sqrt n / m n := by
        rw [le_div_iff₀ hmpos]; linarith
      nlinarith
    nlinarith
