-- Prove2me | solution 1 for ManyServerQED.Scheduling.poisson_polygonal_interpolation_uniform_error
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:06:58.468293+00:00
-- url     : https://prove2.me/submissions/6dd07c2d-d4e0-4561-9f59-f335d201143a

import Definitions.Def_DurrettProbability_Donsker

open Set MeasureTheory Filter Topology Finset DurrettProbability ProbabilityTheory

private theorem interp_segment (N : ℝ → ℝ) {n j : ℕ} (hj : j < n) {u : ℝ}
    (hu : u ∈ Icc (j:ℝ) ((j:ℝ)+1)) :
    walkInterp (Ω := Unit) (fun l _ => N ((l:ℝ)+1) - N l - 1) n () u =
      (N j - N 0 - j) + (N ((j:ℝ)+1) - N j - 1) * (u-j) := by
  let a (l : ℕ) := N ((l:ℝ)+1) - N l - 1
  let c (l : ℕ) := max 0 (min 1 (u - (l:ℝ)))
  have hC (l : ℕ) (hl : l < j) : c l = 1 := by
    have hl' : (l:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt hl
    have hh : 1 ≤ u - (l:ℝ) := by linarith [hu.1]
    simp [c, min_eq_left hh]
  have hJ : c j = u-j := by
    have h0 : 0 ≤ u-(j:ℝ) := sub_nonneg.mpr hu.1
    have h1 : u-(j:ℝ) ≤ 1 := by linarith [hu.2]
    simp [c, min_eq_right h1, max_eq_right h0]
  have hZ (l : ℕ) (hl : j+1 ≤ l) : c l = 0 := by
    have hl' : (j:ℝ)+1 ≤ l := by exact_mod_cast hl
    have hh : u-(l:ℝ) ≤ 0 := by linarith [hu.2]
    have hh' : u-(l:ℝ) ≤ 1 := by linarith
    simp [c, min_eq_right hh', max_eq_left hh]
  have ht (m : ℕ) : ∑ l ∈ range m, a l = N m - N 0 - m := by
    induction m with
    | zero => simp
    | succ m ih =>
      rw [sum_range_succ, ih]
      push_cast
      unfold a
      ring
  change (∑ l ∈ range n, a l * c l) = _
  have hp := sum_range_add_sum_Ico (fun l => a l * c l) (Nat.succ_le_of_lt hj)
  rw [← hp]
  have hz : (∑ l ∈ Finset.Ico (j+1) n, a l * c l) = 0 :=
    Finset.sum_eq_zero (fun l hl => by rw [hZ l (mem_Ico.1 hl).1,mul_zero])
  rw [hz, add_zero, sum_range_succ,hJ]
  have he : ∑ l ∈ range j, a l * c l = ∑ l ∈ range j, a l :=
    Finset.sum_congr rfl (fun l hl => by rw [hC l (mem_range.1 hl),mul_one])
  rw [he, ht]

private theorem interpolation_bound (N : ℝ → ℝ) (hmono : MonotoneOn N (Ici 0)) (h0 : N 0 = 0)
    (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : u ∈ Icc (0:ℝ) (n:ℝ)) :
    ∃ j < n, |(N u - u) -
      walkInterp (Ω := Unit) (fun l _ => N ((l:ℝ)+1) - N l - 1) n () u| ≤
        N ((j:ℝ)+1) - N j := by
  have hbr : ∃ j < n, u ∈ Icc (j:ℝ) ((j:ℝ)+1) := by
    rcases (mem_Icc.1 hu).2.lt_or_eq with hlt | heq
    · let j := ⌊u⌋₊
      have hj : j < n := Nat.floor_lt (by exact hu.1) |>.2 hlt
      exact ⟨j,hj,Nat.floor_le hu.1,(Nat.lt_floor_add_one u).le⟩
    · have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
      have hEq : ((n-1:ℕ):ℝ)+1 = n := by rw [Nat.cast_sub hn]; simp
      refine ⟨n-1,by omega,?_⟩
      rw [heq,hEq]
      exact ⟨by linarith,rfl.le⟩
  obtain ⟨j,hj,hu'⟩ := hbr
  refine ⟨j,hj,?_⟩
  rw [interp_segment N hj hu']
  have hleft : N j ≤ N u := hmono (mem_Ici.2 (by positivity)) (mem_Ici.2 hu.1) hu'.1
  have hright : N u ≤ N ((j:ℝ)+1) := hmono (mem_Ici.2 hu.1) (mem_Ici.2 (by positivity)) hu'.2
  have hm : 0 ≤ N ((j:ℝ)+1)-N j := sub_nonneg.mpr (hleft.trans hright)
  have hp : 0 ≤ u-j := sub_nonneg.mpr hu'.1
  have hp' : u-j ≤ (1:ℝ) := by linarith [hu'.2]
  have hl : N j ≤ N j + (N ((j:ℝ)+1)-N j)*(u-j) := le_add_of_nonneg_right (mul_nonneg hm hp)
  have hr : N j + (N ((j:ℝ)+1)-N j)*(u-j) ≤ N ((j:ℝ)+1) := by
    have h := mul_le_mul_of_nonneg_left hp' hm
    linarith
  rw [h0]
  apply abs_le.mpr
  constructor <;> nlinarith

open scoped ENNReal

private theorem square_tail_small {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (hXm : Measurable X) (hX2 : Integrable (fun ω => X ω ^ 2) P)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (n:ℝ≥0∞) * P {ω | ε * Real.sqrt n ≤ X ω}) atTop (𝓝 0) := by
  let S (n : ℕ) : Set Ω := {ω | ε*Real.sqrt n ≤ X ω}
  let f (n : ℕ) (ω : Ω) := Set.indicator (S n) (fun ω => ENNReal.ofReal (X ω^2)) ω
  let e : ℝ≥0∞ := ENNReal.ofReal (ε^2)
  have hm (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const hXm
  have hXsq : Measurable (fun ω => ENNReal.ofReal (X ω^2)) := (hXm.pow_const _).ennreal_ofReal
  have hXle : (∫⁻ ω, ENNReal.ofReal (X ω^2) ∂P) ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hX2.hasFiniteIntegral).ne
  have hfs : ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
    apply ae_of_all
    intro ω
    have h := Real.tendsto_sqrt_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [(tendsto_atTop.1 h) (X ω/ε + 1)] with n hn
    have h' : X ω < ε*Real.sqrt n := by
      change X ω/ε+1 ≤ Real.sqrt (n:ℝ) at hn
      have hh := mul_le_mul_of_nonneg_left hn hε.le
      rw [mul_add, mul_one, mul_div_cancel₀ _ hε.ne'] at hh
      linarith
    have hnot : ω ∉ S n := not_le_of_gt h'
    exact (Set.indicator_of_notMem hnot _).symm
  have ht := tendsto_lintegral_of_dominated_convergence (fun ω => ENNReal.ofReal (X ω^2))
    (fun n => hXsq.indicator (hm n)) (fun n => ae_of_all _ (fun ω => by
      by_cases hw : ω ∈ S n <;> simp [f,hw]))
    hXle hfs
  simp only [lintegral_zero] at ht
  have he0 : e ≠ 0 := by dsimp [e]; exact (ENNReal.ofReal_pos.2 (sq_pos_of_pos hε)).ne'
  have heT : e ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB (n : ℕ) : e * ((n:ℝ≥0∞) * P (S n)) ≤ ∫⁻ ω, f n ω ∂P := by
    rw [← mul_assoc, ← lintegral_indicator_const (hm n)]
    apply lintegral_mono
    intro ω
    by_cases hω : ω ∈ S n
    · simp only [f, Set.indicator_of_mem hω]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (sq_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      have hh : ε * Real.sqrt n ≤ X ω := hω
      calc
        _ = (ε * Real.sqrt n)^2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
        _ ≤ _ := by gcongr <;> positivity
    · simp [f,hω]
  have hBn (n : ℕ) : (n:ℝ≥0∞) * P (S n) ≤ e⁻¹ * ∫⁻ ω, f n ω ∂P := by
    have h := mul_le_mul_right (hB n) e⁻¹
    rw [← mul_assoc, ENNReal.inv_mul_cancel he0 heT, one_mul] at h
    exact h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le) hBn
  have hei : e⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 he0
  simpa only [mul_zero] using (ENNReal.Tendsto.const_mul (a := e⁻¹) ht (Or.inr hei))

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (N : Ω → ℝ → ℝ) (hN : ∀ ω, MonotoneOn (N ω) (Ici 0)) (h0 : ∀ ω, N ω 0 = 0)
    (hM : ∀ t, Measurable (fun ω => N ω t))
    (hid : ∀ j : ℕ, IdentDistrib (fun ω => N ω ((j:ℝ)+1) - N ω j) (fun ω => N ω 1) P P)
    (h2 : Integrable (fun ω => (N ω 1)^2) P) :
    ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => P {ω |
      ∃ t ∈ Icc (0:ℝ) 1,
        ε ≤ |(N ω ((n:ℝ)*t) - (n:ℝ)*t)/Real.sqrt n -
          walkInterp (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n ω ((n:ℝ)*t)/Real.sqrt n|})
      atTop (𝓝 0) := by
  intro ε hε
  let b (n : ℕ) := (n:ℝ≥0∞) * P {ω | ε*Real.sqrt n ≤ N ω 1}
  have hb := square_tail_small P (fun ω => N ω 1) (hM 1) h2 ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  let E (j : Fin n) := {ω | ε*Real.sqrt n ≤ N ω ((j:ℝ)+1) - N ω j}
  have hsub : {ω | ∃ t ∈ Icc (0:ℝ) 1,
        ε ≤ |(N ω ((n:ℝ)*t) - (n:ℝ)*t)/Real.sqrt n -
          walkInterp (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n ω ((n:ℝ)*t)/Real.sqrt n|}
        ⊆ ⋃ j, E j := by
    rintro ω ⟨t,ht,hω⟩
    have hs : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
    have hu : (n:ℝ)*t ∈ Icc (0:ℝ) n := by
      refine ⟨mul_nonneg (Nat.cast_nonneg _) ht.1, ?_⟩
      simpa using mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n)
    obtain ⟨j,hj,hjB⟩ := interpolation_bound (N ω) (hN ω) (h0 ω) n hn _ hu
    have hX : walkInterp (fun j ω => N ω ((j:ℝ)+1) - N ω j - 1) n ω ((n:ℝ)*t) =
      walkInterp (Ω := Unit) (fun j _ => N ω ((j:ℝ)+1)-N ω j-1) n () ((n:ℝ)*t) := rfl
    rw [← sub_div, abs_div, abs_of_pos hs, hX, le_div_iff₀ hs] at hω
    exact mem_iUnion.2 ⟨⟨j,hj⟩,hω.trans hjB⟩
  refine (measure_mono hsub).trans ((measure_iUnion_le E).trans_eq ?_)
  have hEq (j : Fin n) : P (E j) = P {ω | ε*Real.sqrt n ≤ N ω 1} := by
    exact (hid j).measure_mem_eq (measurableSet_Ici (a := ε*Real.sqrt n))
  simp [hEq,b,nsmul_eq_mul]
