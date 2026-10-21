-- Prove2me | solution 1 for LargeForkJoin.FluidLimit.theorem_2_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T13:08:01.747396+00:00
-- url     : https://prove2.me/submissions/25a4e878-355a-4e06-b778-a6b54946ef3a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LargeForkJoin_FluidLimit_Model
import Theorems.Thm_LargeForkJoin_FluidLimit_theorem_4_1
import Theorems.Thm_LargeForkJoin_FluidLimit_corollary_4_1

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace FJThm21Aux
open LargeForkJoin.FluidLimit

/-- Pointwise convergence in probability on `[0,T]` + the tightness modulus bound + uniform
continuity of the limit give uniform convergence in probability on `[0,T]`. -/
lemma unif_conv {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (Z : ℕ → ℝ → Ω → ℝ) (q : ℝ → ℝ) (T : ℝ) (hT : 0 < T)
    (hq : ∀ ε > 0, ∃ ρ > 0, ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T,
      |x - y| < ρ → |q x - q y| < ε)
    (hpt : ∀ t ∈ Icc (0 : ℝ) T, ∀ ε > 0,
      Tendsto (fun N => P {ω | ε < |Z N t ω - q t|}) atTop (𝓝 0))
    (htight : ∀ ε > 0, ∀ η > 0, ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ N₁ : ℕ, ∀ N ≥ N₁,
      ∀ t ∈ Icc (0 : ℝ) T,
      1 / δ * (P {ω | ∃ s ∈ Icc t (t + δ), ε < |Z N s ω - Z N t ω|}).toReal ≤ η) :
    ∀ ε > 0, Tendsto (fun N => P {ω | ∃ t ∈ Icc (0 : ℝ) T, ε < |Z N t ω - q t|})
      atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨ε', hε', rfl⟩ : ∃ ε', 0 < ε' ∧ ε = 4 * ε' := ⟨ε / 4, by positivity, by ring⟩
  rw [ENNReal.tendsto_nhds_zero]
  intro γ hγ
  obtain ⟨e, he, heγ⟩ : ∃ e : ℝ, 0 < e ∧ ENNReal.ofReal e ≤ γ := by
    by_cases hγt : γ = ⊤
    · exact ⟨1, one_pos, by simp [hγt]⟩
    · exact ⟨γ.toReal, ENNReal.toReal_pos hγ.ne' hγt, by rw [ENNReal.ofReal_toReal hγt]⟩
  obtain ⟨ρ, hρ, hqρ⟩ := hq ε' hε'
  set η := e / (2 * (T + 1)) with hηdef
  have hη : 0 < η := by positivity
  obtain ⟨δ, hδ, hδ1, N₁, hN₁⟩ := htight ε' hε' η hη
  set h := ρ / 2 with hhdef
  have hh : 0 < h := by positivity
  set K₁ := ⌊T / δ⌋₊ with hK₁
  set K₂ := ⌊T / h⌋₊ with hK₂
  set c : ℕ → ℝ := fun i => i * δ with hc
  set f : ℕ → ℝ := fun j => j * h with hf
  set Tight : ℕ → ℕ → Set Ω := fun N i =>
    {ω | ∃ s ∈ Icc (c i) (c i + δ), ε' < |Z N s ω - Z N (c i) ω|} with hTight
  set Pt : ℕ → ℝ → Set Ω := fun N r => {ω | ε' < |Z N r ω - q r|} with hPt
  have hK₁δ : (K₁ : ℝ) * δ ≤ T := by
    have : (K₁ : ℝ) ≤ T / δ := Nat.floor_le (by positivity)
    rwa [le_div_iff₀ hδ] at this
  have hK₂h : (K₂ : ℝ) * h ≤ T := by
    have : (K₂ : ℝ) ≤ T / h := Nat.floor_le (by positivity)
    rwa [le_div_iff₀ hh] at this
  have hc_mem : ∀ i ∈ Finset.range (K₁ + 1), c i ∈ Icc (0 : ℝ) T := by
    intro i hi
    have hi' : (i : ℝ) ≤ K₁ := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    refine ⟨by positivity, ?_⟩
    simp only [hc]; nlinarith
  have hf_mem : ∀ j ∈ Finset.range (K₂ + 1), f j ∈ Icc (0 : ℝ) T := by
    intro j hj
    have hj' : (j : ℝ) ≤ K₂ := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    refine ⟨by positivity, ?_⟩
    simp only [hf]; nlinarith
  -- covering
  have hsub : ∀ N, {ω | ∃ t ∈ Icc (0 : ℝ) T, 4 * ε' < |Z N t ω - q t|} ⊆
      (⋃ i ∈ Finset.range (K₁ + 1), Tight N i) ∪
      ((⋃ i ∈ Finset.range (K₁ + 1), Pt N (c i)) ∪
        (⋃ j ∈ Finset.range (K₂ + 1), Pt N (f j))) := by
    intro N ω hω
    obtain ⟨t, ht, hlt⟩ := hω
    set i := ⌊t / δ⌋₊ with hi
    set j := ⌊t / h⌋₊ with hj
    have hiK : i ∈ Finset.range (K₁ + 1) := by
      refine Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono ?_))
      exact div_le_div_of_nonneg_right ht.2 hδ.le
    have hjK : j ∈ Finset.range (K₂ + 1) := by
      refine Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.floor_mono ?_))
      exact div_le_div_of_nonneg_right ht.2 hh.le
    have hci1 : c i ≤ t := by
      have : (i : ℝ) ≤ t / δ := Nat.floor_le (div_nonneg ht.1 hδ.le)
      simp only [hc]; rwa [le_div_iff₀ hδ] at this
    have hci2 : t < c i + δ := by
      have : t / δ < (i : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hδ] at this
      simp only [hc]; linarith
    have hfj1 : f j ≤ t := by
      have : (j : ℝ) ≤ t / h := Nat.floor_le (div_nonneg ht.1 hh.le)
      simp only [hf]; rwa [le_div_iff₀ hh] at this
    have hfj2 : t < f j + h := by
      have : t / h < (j : ℝ) + 1 := Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hh] at this
      simp only [hf]; linarith
    by_cases h1 : ω ∈ Tight N i
    · exact Or.inl (Set.mem_biUnion hiK h1)
    by_cases h2 : ω ∈ Pt N (c i)
    · exact Or.inr (Or.inl (Set.mem_biUnion hiK h2))
    by_cases h3 : ω ∈ Pt N (f j)
    · exact Or.inr (Or.inr (Set.mem_biUnion hjK h3))
    exfalso
    simp only [hTight, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at h1
    simp only [hPt, Set.mem_ofPred_eq, not_lt] at h2 h3
    have hts := h1 t ⟨hci1, hci2.le⟩
    rcases lt_abs.mp hlt with hl | hl
    · by_cases hcf : c i ≤ f j
      · have h4 := h1 (f j) ⟨hcf, by linarith⟩
        have hqq := hqρ t ht (f j) (hf_mem j hjK)
          (by rw [abs_lt]; constructor <;> linarith)
        obtain ⟨a1, a2⟩ := abs_le.mp hts
        obtain ⟨b1, b2⟩ := abs_le.mp h4
        obtain ⟨c1, c2⟩ := abs_le.mp h3
        obtain ⟨d1, d2⟩ := abs_lt.mp hqq
        linarith
      · push Not at hcf
        have hqq := hqρ t ht (c i) (hc_mem i hiK)
          (by rw [abs_lt]; constructor <;> linarith)
        obtain ⟨a1, a2⟩ := abs_le.mp hts
        obtain ⟨c1, c2⟩ := abs_le.mp h2
        obtain ⟨d1, d2⟩ := abs_lt.mp hqq
        linarith
    · by_cases hcf : c i ≤ f j
      · have h4 := h1 (f j) ⟨hcf, by linarith⟩
        have hqq := hqρ t ht (f j) (hf_mem j hjK)
          (by rw [abs_lt]; constructor <;> linarith)
        obtain ⟨a1, a2⟩ := abs_le.mp hts
        obtain ⟨b1, b2⟩ := abs_le.mp h4
        obtain ⟨c1, c2⟩ := abs_le.mp h3
        obtain ⟨d1, d2⟩ := abs_lt.mp hqq
        linarith
      · push Not at hcf
        have hqq := hqρ t ht (c i) (hc_mem i hiK)
          (by rw [abs_lt]; constructor <;> linarith)
        obtain ⟨a1, a2⟩ := abs_le.mp hts
        obtain ⟨c1, c2⟩ := abs_le.mp h2
        obtain ⟨d1, d2⟩ := abs_lt.mp hqq
        linarith
  -- tightness part
  have hsumT : ∀ N ≥ N₁, P (⋃ i ∈ Finset.range (K₁ + 1), Tight N i) ≤ ENNReal.ofReal (e / 2) := by
    intro N hN
    refine le_trans (measure_biUnion_finset_le _ _) ?_
    have hone : ∀ i ∈ Finset.range (K₁ + 1), P (Tight N i) ≤ ENNReal.ofReal (η * δ) := by
      intro i hi
      have := hN₁ N hN (c i) (hc_mem i hi)
      rw [one_div_mul_eq_div, div_le_iff₀ hδ] at this
      rw [← ENNReal.ofReal_toReal (measure_ne_top P (Tight N i))]
      exact ENNReal.ofReal_le_ofReal this
    refine le_trans (Finset.sum_le_sum hone) ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    have : ((K₁ : ℝ) + 1) * δ ≤ T + 1 := by nlinarith
    have hη2 : η * (T + 1) = e / 2 := by
      rw [hηdef]; field_simp
    nlinarith
  -- pointwise part
  have hsumP : ∀ᶠ N in atTop, P (⋃ i ∈ Finset.range (K₁ + 1), Pt N (c i)) +
      P (⋃ j ∈ Finset.range (K₂ + 1), Pt N (f j)) ≤ ENNReal.ofReal (e / 2) := by
    have hA : Tendsto (fun N => ∑ i ∈ Finset.range (K₁ + 1), P (Pt N (c i))) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range (K₁ + 1))
        (fun i hi => hpt (c i) (hc_mem i hi) ε' hε')
      simpa using this
    have hB : Tendsto (fun N => ∑ j ∈ Finset.range (K₂ + 1), P (Pt N (f j))) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.range (K₂ + 1))
        (fun j hj => hpt (f j) (hf_mem j hj) ε' hε')
      simpa using this
    have hAB := hA.add hB
    rw [add_zero] at hAB
    filter_upwards [ENNReal.tendsto_nhds_zero.1 hAB _ (ENNReal.ofReal_pos.mpr (half_pos he))] with N hN
    exact le_trans (add_le_add (measure_biUnion_finset_le _ _) (measure_biUnion_finset_le _ _)) hN
  filter_upwards [eventually_ge_atTop N₁, hsumP] with N hN hP
  calc P {ω | ∃ t ∈ Icc (0 : ℝ) T, 4 * ε' < |Z N t ω - q t|}
      ≤ P ((⋃ i ∈ Finset.range (K₁ + 1), Tight N i) ∪
      ((⋃ i ∈ Finset.range (K₁ + 1), Pt N (c i)) ∪
        (⋃ j ∈ Finset.range (K₂ + 1), Pt N (f j)))) := measure_mono (hsub N)
    _ ≤ P (⋃ i ∈ Finset.range (K₁ + 1), Tight N i) +
        (P (⋃ i ∈ Finset.range (K₁ + 1), Pt N (c i)) +
          P (⋃ j ∈ Finset.range (K₂ + 1), Pt N (f j))) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 2) := add_le_add (hsumT N hN) hP
    _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    _ ≤ γ := heγ

lemma ciSup_max_fin {ι : Type*} [Finite ι] [Nonempty ι] (u v : ι → ℝ) :
    (⨆ i, max (u i) (v i)) = max (⨆ i, u i) (⨆ i, v i) := by
  have b1 : BddAbove (Set.range u) := (Set.finite_range _).bddAbove
  have b2 : BddAbove (Set.range v) := (Set.finite_range _).bddAbove
  have b3 : BddAbove (Set.range fun i => max (u i) (v i)) := (Set.finite_range _).bddAbove
  apply le_antisymm
  · exact ciSup_le fun i => max_le_max (le_ciSup b1 i) (le_ciSup b2 i)
  · exact max_le (ciSup_le fun i => (le_max_left _ _).trans (le_ciSup b3 i))
      (ciSup_le fun i => (le_max_right _ _).trans (le_ciSup b3 i))

lemma maxQueue_zero {Ω : Type*} (M : ForkJoin Ω) (N : ℕ) (ω : Ω) (hN : 0 < N) :
    maxQueue M N 0 ω = max 0 (maxInit M N ω) := by
  have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
  have hq : ∀ i : ℕ, queueLen M N i 0 ω = max 0 (initLen M N i ω) := by
    intro i
    simp [queueLen, queueEmpty, arr, srv]
  unfold maxQueue maxInit
  rw [show (fun i : Fin N => queueLen M N i 0 ω) = fun i : Fin N => max 0 (initLen M N i ω) from
    funext fun i => hq i]
  rw [ciSup_max_fin, ciSup_const]

lemma fluidEmpty_zero (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) : fluidEmpty α β 0 = 0 := by
  unfold fluidEmpty
  rw [if_pos (by positivity)]
  simp

lemma continuous_fluidEmpty (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    Continuous (fluidEmpty α β) := by
  have heq : fluidEmpty α β = fun t => if α / (2 * β ^ 2) ≤ t then α / (2 * β)
      else Real.sqrt (2 * α * t) - β * t := by
    funext t
    unfold fluidEmpty
    by_cases h : t < α / (2 * β ^ 2)
    · rw [if_pos h, if_neg (not_le.mpr h)]
    · rw [if_neg h, if_pos (not_lt.mp h)]
  rw [heq]
  refine Continuous.if_le continuous_const ?_ continuous_const continuous_id ?_
  · fun_prop
  · intro t ht
    rw [show t = α / (2 * β ^ 2) from ht.symm]
    have h1 : 2 * α * (α / (2 * β ^ 2)) = (α / β) ^ 2 := by field_simp
    rw [h1, Real.sqrt_sq (by positivity)]
    field_simp
    ring

lemma unifCont_of_cont (q : ℝ → ℝ) (hq : Continuous q) (T : ℝ) :
    ∀ ε > 0, ∃ ρ > 0, ∀ x ∈ Icc (0 : ℝ) T, ∀ y ∈ Icc (0 : ℝ) T,
      |x - y| < ρ → |q x - q y| < ε := by
  have hu := (isCompact_Icc (a := (0 : ℝ)) (b := T)).uniformContinuousOn_of_continuous
    hq.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hu
  intro ε hε
  obtain ⟨ρ, hρ, H⟩ := hu ε hε
  exact ⟨ρ, hρ, fun x hx y hy hxy => by
    have := H x hx y hy (by rwa [Real.dist_eq]); rwa [Real.dist_eq] at this⟩

/-- `G a = sup {a u + q v | (u,v) feasible}`; it is 1-Lipschitz in `a`. -/
noncomputable def Gfun (h : ℝ → ℝ) (qInit a : ℝ) : ℝ :=
  sSup {x : ℝ | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ u ^ 2 + h v ≤ 1 ∧
    x = a * u + qInit * v}

lemma Gfun_le (h : ℝ → ℝ) (qInit : ℝ) (h1 : h 1 ≤ 1) (a b : ℝ) :
    Gfun h qInit a ≤ Gfun h qInit b + dist a b := by
  have hne : ∀ c : ℝ, {x : ℝ | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧ u ^ 2 + h v ≤ 1 ∧
      x = c * u + qInit * v}.Nonempty :=
    fun c => ⟨c * 0 + qInit * 1, 0, 1, le_rfl, zero_le_one, zero_le_one, le_rfl, by simpa using h1,
      rfl⟩
  have hbdd : ∀ c : ℝ, BddAbove {x : ℝ | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      u ^ 2 + h v ≤ 1 ∧ x = c * u + qInit * v} := by
    intro c
    refine ⟨|c| + |qInit|, ?_⟩
    rintro x ⟨u, v, hu0, hu1, hv0, hv1, -, rfl⟩
    have e1 : c * u ≤ |c| := by
      calc c * u ≤ |c * u| := le_abs_self _
        _ = |c| * u := by rw [abs_mul, abs_of_nonneg hu0]
        _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left hu1 (abs_nonneg _)
        _ = |c| := mul_one _
    have e2 : qInit * v ≤ |qInit| := by
      calc qInit * v ≤ |qInit * v| := le_abs_self _
        _ = |qInit| * v := by rw [abs_mul, abs_of_nonneg hv0]
        _ ≤ |qInit| * 1 := mul_le_mul_of_nonneg_left hv1 (abs_nonneg _)
        _ = |qInit| := mul_one _
    linarith
  unfold Gfun
  rw [← sub_le_iff_le_add]
  refine sub_le_iff_le_add.mpr (csSup_le (hne a) ?_)
  rintro x ⟨u, v, hu0, hu1, hv0, hv1, huv, rfl⟩
  have hmem : b * u + qInit * v ∈ {x : ℝ | ∃ u v : ℝ, 0 ≤ u ∧ u ≤ 1 ∧ 0 ≤ v ∧ v ≤ 1 ∧
      u ^ 2 + h v ≤ 1 ∧ x = b * u + qInit * v} := ⟨u, v, hu0, hu1, hv0, hv1, huv, rfl⟩
  have := le_csSup (hbdd b) hmem
  have hd : (a - b) * u ≤ dist a b := by
    rw [Real.dist_eq]
    calc (a - b) * u ≤ |(a - b) * u| := le_abs_self _
      _ = |a - b| * u := by rw [abs_mul, abs_of_nonneg hu0]
      _ ≤ |a - b| * 1 := mul_le_mul_of_nonneg_left hu1 (abs_nonneg _)
      _ = |a - b| := mul_one _
  nlinarith

lemma gGumbel_eq (α : ℝ) (h : ℝ → ℝ) (qInit t : ℝ) :
    gGumbel α h qInit t = Gfun h qInit (Real.sqrt (2 * α * t)) := rfl

lemma h_one_le {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (h : ℝ → ℝ) (hU : Measurable (M.U 0)) (h25 : Assumption25 P M h) :
    h 1 ≤ 1 := by
  obtain ⟨-, hpos, hlim⟩ := h25
  have hl := hlim 1 ⟨zero_le_one, le_rfl⟩
  simp only [one_mul] at hl
  -- P(t < U) → 0
  have hT : Tendsto (fun t : ℝ => P {ω | t < M.U 0 ω}) atTop (𝓝 0) := by
    have := tendsto_measure_iInter_atTop (μ := P) (s := fun t : ℝ => {ω | t < M.U 0 ω})
      (fun t => (measurableSet_lt measurable_const hU).nullMeasurableSet)
      (fun a b hab => fun ω (hω : b < M.U 0 ω) => show a < M.U 0 ω from lt_of_le_of_lt hab hω)
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ t : ℝ, {ω | t < M.U 0 ω}) = ∅ := by
      ext ω
      simp only [Set.mem_iInter, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_forall, not_lt]
      exact ⟨M.U 0 ω, le_rfl⟩
    rw [hempty, measure_empty] at this
    exact this
  have hev : ∀ᶠ t : ℝ in atTop, P {ω | t < M.U 0 ω} < 1 :=
    (tendsto_order.1 hT).2 1 one_pos
  have hconst : ∀ᶠ t : ℝ in atTop,
      -Real.log (P {ω | t < M.U 0 ω}).toReal / -Real.log (P {ω | t < M.U 0 ω}).toReal = 1 := by
    filter_upwards [hev] with t ht
    have h0 : 0 < (P {ω | t < M.U 0 ω}).toReal :=
      ENNReal.toReal_pos (hpos t).ne' (measure_ne_top _ _)
    have h1 : (P {ω | t < M.U 0 ω}).toReal < 1 := by
      have := ENNReal.toReal_strict_mono ENNReal.one_ne_top ht
      simpa using this
    have hlog : Real.log (P {ω | t < M.U 0 ω}).toReal < 0 := Real.log_neg h0 h1
    exact div_self (by linarith)
  have : h 1 = 1 := tendsto_nhds_unique hl (tendsto_const_nhds.congr' (hconst.mono fun _ h => h.symm))
  exact this.le

end FJThm21Aux

open LargeForkJoin.FluidLimit FJThm21Aux in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ForkJoin Ω) (α β qInit : ℝ) (N₀ : ℕ)
    (hM : IsModel P M α β N₀) (h23 : Assumption23 P M qInit) :
    (Assumption24 P M → ∀ T > 0, ∀ ε > 0,
        Tendsto (fun N : ℕ => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          ε < |maxQueue M N (tau N t) ω / scale N - fluid α β (gFinite α qInit) t|}) atTop (𝓝 0)) ∧
    (∀ h : ℝ → ℝ, Assumption25 P M h → ∀ T > 0, ∀ ε > 0,
        Tendsto (fun N : ℕ => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          ε < |maxQueue M N (tau N t) ω / scale N - fluid α β (gGumbel α h qInit) t|}) atTop (𝓝 0)) := by
  have hα : 0 < α := hM.1
  have hβ : 0 < β := hM.2.1
  have hq0 : 0 ≤ qInit := h23.1
  have h41 := theorem_4_1 P M α β qInit N₀ hM h23
  have key : ∀ g : ℝ → ℝ,
      (∀ t > 0, ∀ ε > 0, Tendsto (fun N : ℕ => P {ω | ε <
        |maxQueue M N (tau N t) ω / scale N - fluid α β g t|}) atTop (𝓝 0)) →
      Continuous g → g 0 = qInit → ∀ T > 0, ∀ ε > 0,
        Tendsto (fun N : ℕ => P {ω | ∃ t ∈ Set.Icc (0 : ℝ) T,
          ε < |maxQueue M N (tau N t) ω / scale N - fluid α β g t|}) atTop (𝓝 0) := by
    intro g hpos hg hg0 T hT
    refine unif_conv P (fun N t ω => maxQueue M N (tau N t) ω / scale N) (fluid α β g) T hT
      ?_ ?_ ((corollary_4_1 P M α β qInit N₀ hM h23 T hT).2)
    · refine unifCont_of_cont _ ?_ T
      unfold fluid
      exact (continuous_fluidEmpty α β hα hβ).max (hg.sub (continuous_const.mul continuous_id))
    · intro t ht
      rcases ht.1.eq_or_lt with h0 | h0
      · subst h0
        have hf0 : fluid α β g 0 = qInit := by
          unfold fluid; rw [fluidEmpty_zero α β hα hβ, hg0]; simp [hq0]
        intro ε hε
        simp only [hf0]
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (h23.2 ε hε)
          (Eventually.of_forall fun _ => bot_le) ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        refine measure_mono fun ω hω => ?_
        simp only [Set.mem_ofPred_eq] at hω ⊢
        have htau : tau N 0 = 0 := by simp [tau]
        rw [htau, maxQueue_zero M N ω hN] at hω
        have hD : 0 ≤ scale N := by
          unfold scale; have := Real.log_natCast_nonneg N; positivity
        rw [← max_div_div_right hD, zero_div] at hω
        refine lt_of_lt_of_le hω ?_
        rcases le_total 0 (maxInit M N ω / scale N) with hx | hx
        · rw [max_eq_right hx]
        · rw [max_eq_left hx, zero_sub, abs_neg, abs_of_nonneg hq0]
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
      · exact hpos t h0
  constructor
  · intro h24
    refine key (gFinite α qInit) (fun t ht => (h41 t ht).1 h24) ?_ (by simp [gFinite])
    unfold gFinite
    fun_prop
  · intro h h25
    have h1 := h_one_le P M h (hM.2.2.2.2.1 0) h25
    refine key (gGumbel α h qInit) (fun t ht => (h41 t ht).2 h h25) ?_ ?_
    · have hL : LipschitzWith 1 (Gfun h qInit) := LipschitzWith.of_le_add (Gfun_le h qInit h1)
      have : gGumbel α h qInit = Gfun h qInit ∘ fun t => Real.sqrt (2 * α * t) := by
        funext t; rfl
      rw [this]
      exact hL.continuous.comp (by fun_prop)
    · rw [gGumbel_eq]
      simp only [mul_zero, Real.sqrt_zero]
      unfold Gfun
      apply le_antisymm
      · refine csSup_le ⟨qInit * 1, 0, 1, le_rfl, zero_le_one, zero_le_one, le_rfl,
          by simpa using h1, by ring⟩ ?_
        rintro x ⟨u, v, -, -, hv0, hv1, -, rfl⟩
        nlinarith
      · refine le_csSup ⟨qInit, ?_⟩ ⟨0, 1, le_rfl, zero_le_one, zero_le_one, le_rfl,
          by simpa using h1, by ring⟩
        rintro x ⟨u, v, -, -, hv0, hv1, -, rfl⟩
        nlinarith
