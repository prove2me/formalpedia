-- Prove2me | solution 1 for NumStochOpt.ListScheduling.eq_8_13_optimal_makespan_ratio_ae
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T05:36:51.675114+00:00
-- url     : https://prove2.me/submissions/89a19df5-a925-46c4-b5d8-29085d2d9544

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan
import Definitions.Def_NumStochOpt_ListScheduling_ListSchedule

set_option autoImplicit false


open NumStochOpt.ListScheduling in
theorem L895fce75_fa_some {m : ℕ} (hm : 1 ≤ m) (ℓ : Fin m → ℝ) :
    ∃ i, firstAvailable ℓ = some i := by
  have hne : (Finset.univ.filter (fun i : Fin m => ∀ k, ℓ i ≤ ℓ k)).Nonempty := by
    obtain ⟨i, -, hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin m)) ℓ
      ⟨⟨0, hm⟩, Finset.mem_univ _⟩
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun k => hi k (Finset.mem_univ _)⟩⟩
  exact ⟨_, by unfold firstAvailable; rw [dif_pos hne]⟩

open NumStochOpt.ListScheduling in
theorem L895fce75_fa_min {m : ℕ} (ℓ : Fin m → ℝ) (i : Fin m) (h : firstAvailable ℓ = some i) :
    ∀ k, ℓ i ≤ ℓ k := by
  unfold firstAvailable at h
  split_ifs at h with hne
  · cases h
    have := Finset.min'_mem _ hne
    exact (Finset.mem_filter.1 this).2

open NumStochOpt.ListScheduling in
theorem L895fce75_sum_loads {m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (k : ℕ) :
    ∑ i, lsLoads m p k i = ∑ j ∈ Finset.range k, p j := by
  induction k with
  | zero => simp [lsLoads]
  | succ k ih =>
    obtain ⟨i0, hi0⟩ := L895fce75_fa_some hm (lsLoads m p k)
    have : ∀ i, lsLoads m p (k + 1) i = lsLoads m p k i + (if i0 = i then p k else 0) := by
      intro i
      simp only [lsLoads, hi0, Option.some.injEq]
      split_ifs <;> simp
    simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, ih,
      Finset.sum_range_succ]

open NumStochOpt.ListScheduling in
theorem L895fce75_upper {m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (M : ℝ) (n : ℕ)
    (hM : ∀ j, j < n → p j ≤ M) (hM0 : 0 ≤ M) :
    ∀ k, k ≤ n → ∀ i, lsLoads m p k i ≤ (∑ j ∈ Finset.range k, p j) / m + M := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  intro k
  induction k with
  | zero => intro _ i; simp [lsLoads, hM0]
  | succ k ih =>
    intro hk i
    have ih' := ih (by omega)
    obtain ⟨i0, hi0⟩ := L895fce75_fa_some hm (lsLoads m p k)
    have hmin := L895fce75_fa_min _ _ hi0
    have hS : ∑ j ∈ Finset.range (k+1), p j = ∑ j ∈ Finset.range k, p j + p k :=
      Finset.sum_range_succ _ _
    have hpk := hp k
    have hpkM := hM k (by omega)
    simp only [lsLoads, hi0, Option.some.injEq]
    split_ifs with h
    · subst h
      -- m * ℓ i0 ≤ ∑ ℓ = S_k
      have hsum := L895fce75_sum_loads hm p k
      have hle : (m : ℝ) * lsLoads m p k i0 ≤ ∑ j ∈ Finset.range k, p j := by
        rw [← hsum]
        have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin m)) (lsLoads m p k)
          (lsLoads m p k i0) (fun x _ => hmin x)
        simpa [nsmul_eq_mul] using this
      have h1 : lsLoads m p k i0 ≤ (∑ j ∈ Finset.range k, p j) / m := by
        rw [le_div_iff₀ hmpos]; linarith
      rw [hS]
      have : (∑ j ∈ Finset.range k, p j) / m ≤ (∑ j ∈ Finset.range k, p j + p k) / m := by
        apply div_le_div_of_nonneg_right _ hmpos.le; linarith
      linarith
    · rw [hS]
      have : (∑ j ∈ Finset.range k, p j) / m ≤ (∑ j ∈ Finset.range k, p j + p k) / m := by
        apply div_le_div_of_nonneg_right _ hmpos.le; linarith
      linarith [ih' i]

open NumStochOpt.ListScheduling in
theorem L895fce75_assign {m : ℕ} (hm : 1 ≤ m) (p : ℕ → ℝ) (k : ℕ) (i : Fin m) :
    lsLoads m p k i = ∑ j ∈ Finset.range k,
      (if (firstAvailable (lsLoads m p j)).getD ⟨0, hm⟩ = i then p j else 0) := by
  induction k with
  | zero => simp [lsLoads]
  | succ k ih =>
    obtain ⟨i0, hi0⟩ := L895fce75_fa_some hm (lsLoads m p k)
    rw [Finset.sum_range_succ, ← ih]
    simp only [lsLoads, hi0, Option.some.injEq, Option.getD_some]
    split_ifs <;> simp

open NumStochOpt.ListScheduling in
theorem L895fce75_bdd {α : Type} [Finite α] (f : α → ℝ) : BddAbove (Set.range f) ∧ BddBelow (Set.range f) :=
  ⟨(Set.finite_range f).bddAbove, (Set.finite_range f).bddBelow⟩

open NumStochOpt.ListScheduling in
theorem L895fce75_main (n m : ℕ) (p : ℕ → ℝ) (hp : ∀ j, 0 ≤ p j) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    (∑ j ∈ Finset.range n, p j) ≤ m * optMakespan n m p ∧
      optMakespan n m p ≤ listMakespan n m p ∧
      m * listMakespan n m p ≤ (∑ j ∈ Finset.range n, p j) + m * maxProcTime n p := by
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_⟩
  · -- averaging bound
    have key : ∀ σ : Fin n → Fin m, (∑ j ∈ Finset.range n, p j) ≤ m * makespan p σ := by
      intro σ
      have hsum : ∑ i, machineLoad p σ i = ∑ j ∈ Finset.range n, p j := by
        unfold machineLoad
        rw [Finset.sum_comm, ← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp
      rw [← hsum]
      have := Finset.sum_le_card_nsmul (Finset.univ : Finset (Fin m)) (machineLoad p σ)
        (makespan p σ) (fun i _ => le_ciSup (L895fce75_bdd _).1 i)
      simpa [nsmul_eq_mul] using this
    have h : (∑ j ∈ Finset.range n, p j) / m ≤ optMakespan n m p := by
      unfold optMakespan
      apply le_ciInf
      intro σ
      rw [div_le_iff₀ hmpos]; linarith [key σ]
    rw [div_le_iff₀ hmpos] at h; linarith
  · -- the list schedule is one assignment
    let σ : Fin n → Fin m := fun j => (firstAvailable (lsLoads m p j)).getD ⟨0, hm⟩
    have heq : makespan p σ = listMakespan n m p := by
      unfold makespan listMakespan
      congr 1; funext i
      unfold machineLoad
      rw [L895fce75_assign hm p n i, ← Fin.sum_univ_eq_sum_range
        (fun j => if (firstAvailable (lsLoads m p j)).getD ⟨0, hm⟩ = i then p j else 0)]
    rw [← heq]
    unfold optMakespan
    exact ciInf_le (L895fce75_bdd _).2 σ
  · -- Graham bound
    have hM : ∀ j, j < n → p j ≤ maxProcTime n p := fun j hj =>
      le_ciSup (f := fun j : Fin n => p (j : ℕ)) (L895fce75_bdd _).1 ⟨j, hj⟩
    have hM0 : 0 ≤ maxProcTime n p := le_trans (hp 0) (hM 0 (by omega))
    have hup := L895fce75_upper hm p hp (maxProcTime n p) n hM hM0 n le_rfl
    have : listMakespan n m p ≤ (∑ j ∈ Finset.range n, p j) / m + maxProcTime n p := by
      unfold listMakespan
      exact ciSup_le hup
    have h2 : (m : ℝ) * ((∑ j ∈ Finset.range n, p j) / m) = ∑ j ∈ Finset.range n, p j := by
      field_simp
    nlinarith

open NumStochOpt.ListScheduling in
theorem L895fce75_sandwich (n m : ℕ) (p : ℕ → ℝ) (μ : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hn : 1 ≤ n) (hm : 1 ≤ m) (hμ : 0 < μ) :
    ((∑ j ∈ Finset.range n, p j) - n * μ) / (n * μ) + 1
        ≤ optMakespan n m p / (n * μ / m) ∧
      optMakespan n m p / (n * μ / m) ≤ listMakespan n m p / (n * μ / m) ∧
      listMakespan n m p / (n * μ / m)
        ≤ ((∑ j ∈ Finset.range n, p j) - n * μ) / (n * μ) + 1
            + m * maxProcTime n p / (n * μ) := by
  obtain ⟨h1, h2, h3⟩ := L895fce75_main n m p hp hn hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnμ : (0 : ℝ) < n * μ := mul_pos hnpos hμ
  set S := ∑ j ∈ Finset.range n, p j
  have e1 : (S - n * μ) / (n * μ) + 1 = S / (n * μ) := by
    field_simp; ring
  have e2 : ∀ X : ℝ, X / (n * μ / m) = (m * X) / (n * μ) := by
    intro X; field_simp
  rw [e1, e2, e2]
  refine ⟨?_, ?_, ?_⟩
  · exact div_le_div_of_nonneg_right h1 hnμ.le
  · apply div_le_div_of_nonneg_right _ hnμ.le
    exact mul_le_mul_of_nonneg_left h2 hmpos.le
  · rw [← add_div]
    exact div_le_div_of_nonneg_right h3 hnμ.le



open MeasureTheory ProbabilityTheory Filter Topology Asymptotics

namespace L895fce75Aux

/-- If each term eventually satisfies `b j ≤ δ √j`, so does the running maximum. -/
lemma max_bound (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j)
    (h : ∀ δ > 0, ∀ᶠ j in atTop, b j ≤ δ * Real.sqrt j) :
    ∀ δ > 0, ∀ᶠ n in atTop, NumStochOpt.ListScheduling.maxProcTime n b ≤ δ * Real.sqrt n := by
  intro δ hδ
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h δ hδ)
  have hT : Tendsto (fun n : ℕ => δ * Real.sqrt n) atTop atTop :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop hδ
  filter_upwards [hT.eventually_ge_atTop (∑ j ∈ Finset.range N, b j)] with n hn
  unfold NumStochOpt.ListScheduling.maxProcTime
  apply Real.iSup_le
  · intro j
    by_cases hj : (j : ℕ) < N
    · calc b j ≤ ∑ j ∈ Finset.range N, b j :=
            Finset.single_le_sum (fun i _ => hb i) (Finset.mem_range.2 hj)
        _ ≤ δ * Real.sqrt n := hn
    · push Not at hj
      calc b j ≤ δ * Real.sqrt ((j : ℕ) : ℝ) := hN j hj
        _ ≤ δ * Real.sqrt n := by
          gcongr
          exact_mod_cast j.2.le
  · positivity

/-- From the strong law for the squares, `b j ≤ δ √j` eventually. -/
lemma term_bound (b : ℕ → ℝ) (hb : ∀ j, 0 ≤ b j) (E : ℝ)
    (hS : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, b i ^ 2) / n) atTop (𝓝 E)) :
    ∀ δ > 0, ∀ᶠ j in atTop, b j ≤ δ * Real.sqrt j := by
  have hA : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), b i ^ 2) / ((n + 1 : ℕ) : ℝ))
      atTop (𝓝 E) := hS.comp (tendsto_add_atTop_nat 1)
  have hB : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have h0 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h0
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    push_cast
    field_simp
  have h1 : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (n + 1), b i ^ 2) / n) atTop (𝓝 E) := by
    have := hA.mul hB
    rw [mul_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by positivity
    have hn'' : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have h2 : Tendsto (fun n : ℕ => b n ^ 2 / n) atTop (𝓝 0) := by
    have := h1.sub hS
    rw [sub_self] at this
    refine this.congr' (Eventually.of_forall fun n => ?_)
    simp only [Finset.sum_range_succ]
    ring
  intro δ hδ
  have hev := h2.eventually (gt_mem_nhds (show (0 : ℝ) < δ ^ 2 by positivity))
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
  have hsq : b n ^ 2 ≤ δ ^ 2 * n := by
    rw [div_lt_iff₀ hnpos] at hn
    linarith
  calc b n = Real.sqrt (b n ^ 2) := (Real.sqrt_sq (hb n)).symm
    _ ≤ Real.sqrt (δ ^ 2 * n) := Real.sqrt_le_sqrt hsq
    _ = δ * Real.sqrt n := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hδ.le]

end L895fce75Aux

open MeasureTheory ProbabilityTheory Filter Topology Asymptotics NumStochOpt.ListScheduling in
theorem L895fce75_e12 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (m n : ℝ) * maxProcTime n (fun j => p j ω) / (n * μ))
      atTop (𝓝 0) := by
  have hpow : Measurable (fun x : ℝ => x ^ 2) := measurable_id.pow_const 2
  have hSL := ProbabilityTheory.strong_law_ae_real (fun i ω => p i ω ^ 2) hsq
    (fun i j hij => (hindep.indepFun hij).comp hpow hpow)
    (fun i => (hident i).comp hpow)
  obtain ⟨C, hC⟩ := hmO.bound
  filter_upwards [hSL] with ω hω
  have hb : ∀ j, 0 ≤ p j ω := fun j => hnonneg j ω
  have h1 := L895fce75Aux.term_bound (fun j => p j ω) hb _ hω
  have h2 := L895fce75Aux.max_bound (fun j => p j ω) hb h1
  set C' : ℝ := max C 1 with hC'
  have hC'pos : 0 < C' := lt_of_lt_of_le one_pos (le_max_right C 1)
  refine tendsto_order.2 ⟨fun a ha => ?_, fun a ha => ?_⟩
  · refine Eventually.of_forall fun n => lt_of_lt_of_le ha ?_
    have hp0 : 0 ≤ maxProcTime n (fun j => p j ω) := by
      unfold maxProcTime
      exact Real.iSup_nonneg fun j => hb j
    positivity
  · have hδ : 0 < a * μ / (2 * C') := by positivity
    filter_upwards [h2 _ hδ, hC, eventually_gt_atTop 0] with n hn hCn hn0
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn0
    have hp0 : 0 ≤ maxProcTime n (fun j => p j ω) := by
      unfold maxProcTime
      exact Real.iSup_nonneg fun j => hb j
    have hm' : (m n : ℝ) ≤ C' * Real.sqrt n := by
      simp only [Real.norm_eq_abs, Nat.abs_cast, abs_of_nonneg (Real.sqrt_nonneg _)] at hCn
      exact le_trans hCn (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.sqrt_nonneg _))
    have hCδ : C' * (a * μ / (2 * C')) = a * μ / 2 := by
      field_simp
    rw [div_lt_iff₀ (by positivity)]
    calc (m n : ℝ) * maxProcTime n (fun j => p j ω)
        ≤ (C' * Real.sqrt n) * (a * μ / (2 * C') * Real.sqrt n) :=
          mul_le_mul hm' hn hp0 (by positivity)
      _ = C' * (a * μ / (2 * C')) * (Real.sqrt n * Real.sqrt n) := by ring
      _ = a * μ / 2 * n := by rw [hCδ, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      _ < a * (n * μ) := by nlinarith [mul_pos (mul_pos ha hμ) hnpos]


open MeasureTheory ProbabilityTheory Filter Topology Asymptotics NumStochOpt.ListScheduling in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P)
    (μ : ℝ) (hmean : ∫ ω, p 0 ω ∂P = μ) (hμ : 0 < μ)
    (m : ℕ → ℕ) (hm : ∀ n, 1 ≤ m n)
    (hmO : (fun n : ℕ => (m n : ℝ)) =O[atTop] (fun n : ℕ => Real.sqrt n)) :
    ∀ᵐ ω ∂P, Tendsto
      (fun n : ℕ => optMakespan n (m n) (fun j => p j ω) / (n * μ / m n))
      atTop (𝓝 1) := by
  have hint : Integrable (p 0) P := by
    refine Integrable.mono' (hsq.add (integrable_const (1 : ℝ)))
      (hmeas 0).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    have h0 := hnonneg 0 ω
    rw [Real.norm_of_nonneg h0]
    show p 0 ω ≤ p 0 ω ^ 2 + 1
    nlinarith [sq_nonneg (p 0 ω - 1)]
  have hSL := ProbabilityTheory.strong_law_ae_real p hint
    (fun i j hij => hindep.indepFun hij) hident
  have hE := L895fce75_e12 p hmeas hindep hident hnonneg hsq μ hmean hμ m hm hmO
  filter_upwards [hSL, hE] with ω hω hTω
  rw [hmean] at hω
  set S : ℕ → ℝ := fun n => ∑ i ∈ Finset.range n, p i ω with hSdef
  have hL : Tendsto (fun n : ℕ => (S n - n * μ) / (n * μ) + 1) atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (S n / n) / μ) atTop (𝓝 (μ / μ)) := hω.div_const μ
    rw [div_self hμ.ne'] at h1
    refine h1.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    field_simp
    ring
  have hU : Tendsto (fun n : ℕ => (S n - n * μ) / (n * μ) + 1
      + (m n : ℝ) * maxProcTime n (fun j => p j ω) / (n * μ)) atTop (𝓝 1) := by
    have := hL.add hTω
    rwa [add_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hL hU ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (L895fce75_sandwich n (m n) (fun j => p j ω) μ (fun j => hnonneg j ω) hn (hm n) hμ).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have h := L895fce75_sandwich n (m n) (fun j => p j ω) μ (fun j => hnonneg j ω) hn (hm n) hμ
    exact h.2.1.trans h.2.2
