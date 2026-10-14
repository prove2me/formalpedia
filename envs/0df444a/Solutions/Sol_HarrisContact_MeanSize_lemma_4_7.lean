-- Prove2me | solution 1 for HarrisContact.MeanSize.lemma_4_7
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-12T22:50:19.64489+00:00
-- url     : https://prove2.me/submissions/43b0204a-6383-44f5-9287-9ff4aa0aeb5d

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal


namespace HarrisContact.MeanSize
open HarrisContact.Extinction

theorem hc_card_nbrs_le {d : ℕ} (x : Site d) : (nbrs x).card ≤ 2 * d := by
  classical
  let g : Fin d × Bool → Site d := fun p => Function.update x p.1 (x p.1 + if p.2 then 1 else -1)
  have hsub : nbrs x ⊆ Finset.univ.image g := by
    intro y hy
    simp only [nbrs, Finset.mem_filter] at hy
    obtain ⟨-, hy2⟩ := hy
    have hex : ∃ i, x i ≠ y i := by
      by_contra hc
      push_neg at hc
      simp [hc] at hy2
    obtain ⟨i, hi⟩ := hex
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => |x j - y j|) (Finset.mem_univ i)
    rw [hy2] at hsplit
    have hge : 1 ≤ |x i - y i| := by
      have : x i - y i ≠ 0 := sub_ne_zero.mpr hi
      rcases lt_or_gt_of_ne this with h | h
      · rw [abs_of_neg h]; omega
      · rw [abs_of_pos h]; omega
    have hrest : ∑ j ∈ Finset.univ.erase i, |x j - y j| = 0 := by
      have h0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, |x j - y j| :=
        Finset.sum_nonneg (fun j _ => abs_nonneg _)
      linarith
    have hi1 : |x i - y i| = 1 := by linarith
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg _)] at hrest
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    refine ⟨(i, decide (y i = x i + 1)), ?_⟩
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [g, Function.update_self]
      rcases abs_eq (zero_le_one) |>.mp hi1 with h | h
      · have : y j ≠ x j + 1 := by omega
        simp [this]; omega
      · have : y j = x j + 1 := by omega
        simp [this]
    · have := hrest j (by simp [hj])
      simp only [g, Function.update_of_ne hj]
      rw [abs_eq_zero, sub_eq_zero] at this
      exact this
  calc (nbrs x).card ≤ (Finset.univ.image g).card := Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fin d × Bool)).card := Finset.card_image_le
    _ = 2 * d := by simp [Finset.card_univ]; ring

theorem hc_occ_le {d : ℕ} (ξ : Config d) (x : Site d) : occ ξ x ≤ 2 * d :=
  (Finset.card_le_card Finset.inter_subset_right).trans (hc_card_nbrs_le x)

theorem hc_card_bdry_le {d : ℕ} (ξ : Config d) : (bdry ξ).card ≤ 2 * d * ξ.card := by
  calc (bdry ξ).card ≤ (ξ.biUnion nbrs).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ ∑ y ∈ ξ, (nbrs y).card := Finset.card_biUnion_le
    _ ≤ ∑ y ∈ ξ, 2 * d := Finset.sum_le_sum fun y _ => hc_card_nbrs_le y
    _ = 2 * d * ξ.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

theorem hc_succ_sum {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (ξ : Config d) (hμ : 0 ≤ μ)
    (hl : ∀ x ∈ bdry ξ, 0 ≤ lam (occ ξ x)) (F : Config d → ℝ≥0∞) :
    ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * F ζ =
      ∑ x ∈ ξ, ENNReal.ofReal μ * F (ξ.erase x) +
        ∑ x ∈ bdry ξ, ENNReal.ofReal (lam (occ ξ x)) * F (insert x ξ) := by
  have h1 : ∀ ζ, ENNReal.ofReal (rate μ lam ξ ζ) =
      (∑ x ∈ ξ, if ζ = ξ.erase x then ENNReal.ofReal μ else 0) +
        ∑ x ∈ bdry ξ, if ζ = insert x ξ then ENNReal.ofReal (lam (occ ξ x)) else 0 := by
    intro ζ
    unfold rate
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun x _ => by split_ifs <;> simp [hμ])
        (Finset.sum_nonneg fun x hx => by split_ifs <;> simp [hl x hx]),
      ENNReal.ofReal_sum_of_nonneg (fun x _ => by split_ifs <;> simp [hμ]),
      ENNReal.ofReal_sum_of_nonneg (fun x hx => by split_ifs <;> simp [hl x hx])]
    congr 1
    · exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
    · exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
  simp_rw [h1, add_mul, Finset.sum_mul, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos]
    exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hx)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    simp_rw [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq', if_pos]
    exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hx)

theorem hc_transN_mono {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) :
    ∀ n t (ξ η : Config d), transN μ lam n t ξ η ≤ transN μ lam (n + 1) t ξ η := by
  intro n
  induction n with
  | zero => intro t ξ η; simp only [transN.eq_2]; exact le_add_right (le_refl _)
  | succ n ih =>
    intro t ξ η
    simp only [transN.eq_2]
    refine add_le_add le_rfl (lintegral_mono fun s => ?_)
    gcongr with ζ hζ
    have := ih (t - s) ζ η
    simp only [transN.eq_2] at this
    exact this

theorem hc_tsum_lintegral_le {α ι : Type*} [MeasurableSpace α] (ν : Measure α)
    (f : ι → α → ℝ≥0∞) : ∑' i, ∫⁻ a, f i a ∂ν ≤ ∫⁻ a, ∑' i, f i a ∂ν := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have h : ∀ s : Finset ι, ∑ i ∈ s, ∫⁻ a, f i a ∂ν ≤ ∫⁻ a, ∑ i ∈ s, f i a ∂ν := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      simp_rw [Finset.sum_insert hj]
      exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)
  exact (h s).trans (lintegral_mono fun a => ENNReal.sum_le_tsum s)

theorem hc_tsum_iSup_le {ι : Type*} (a : ℕ → ι → ℝ≥0∞) (hmono : ∀ i, Monotone (fun n => a n i))
    (B : ℝ≥0∞) (h : ∀ n, ∑' i, a n i ≤ B) : ∑' i, ⨆ n, a n i ≤ B := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  rw [ENNReal.finsetSum_iSup_of_monotone hmono]
  exact iSup_le fun n => (ENNReal.sum_le_tsum s).trans (h n)

theorem hc_int (q c N t : ℝ) (ht : 0 ≤ t) (hN : 0 ≤ N) (hK : 0 ≤ (q + c) * N) :
    ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal N +
      ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal ((q + c) * N * Real.exp (c * (t - s))) ≤
      ENNReal.ofReal (N * Real.exp (c * t)) := by
  have hg : ∀ s, Real.exp (-(q * s)) * ((q + c) * N * Real.exp (c * (t - s))) =
      (q + c) * N * Real.exp (c * t) * Real.exp (-(q + c) * s) := by
    intro s
    have : Real.exp (-(q * s)) * Real.exp (c * (t - s)) = Real.exp (c * t) * Real.exp (-(q + c) * s) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    linear_combination ((q + c) * N) * this
  have hcont : Continuous (fun s => (q + c) * N * Real.exp (c * t) * Real.exp (-(q + c) * s)) := by
    fun_prop
  have hnn : ∀ s, 0 ≤ (q + c) * N * Real.exp (c * t) * Real.exp (-(q + c) * s) := fun s => by
    have := Real.exp_pos (c * t); have := Real.exp_pos (-(q + c) * s); positivity
  have hlin : ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal ((q + c) * N * Real.exp (c * (t - s))) =
      ENNReal.ofReal (∫ s in Set.Icc 0 t, (q + c) * N * Real.exp (c * t) * Real.exp (-(q + c) * s)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc)
      (Filter.Eventually.of_forall hnn)]
    refine lintegral_congr fun s => ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, hg]
  have hval : ∫ s in Set.Icc 0 t, (q + c) * N * Real.exp (c * t) * Real.exp (-(q + c) * s) =
      N * Real.exp (c * t) - N * Real.exp (-(q * t)) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
    have hd : ∀ s ∈ Set.uIcc 0 t, HasDerivAt (fun s => -(N * Real.exp (c * t) * Real.exp (-(q + c) * s)))
        ((q + c) * N * Real.exp (c * t) * Real.exp (-(q + c) * s)) s := by
      intro s _
      have h1 : HasDerivAt (fun s => -(q + c) * s) (-(q + c)) s := by
        simpa using (hasDerivAt_id s).const_mul (-(q + c))
      exact ((h1.exp.const_mul (N * Real.exp (c * t))).neg).congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable _ _)]
    have : Real.exp (c * t) * Real.exp (-(q + c) * t) = Real.exp (-(q * t)) := by
      rw [← Real.exp_add]; ring_nf
    simp only [mul_zero, Real.exp_zero, mul_one]
    linear_combination (-N) * this
  have hpos : 0 ≤ N * Real.exp (c * t) - N * Real.exp (-(q * t)) := by
    rw [← hval]; exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun s _ => hnn s
  rw [hlin, hval, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← ENNReal.ofReal_add (by positivity) hpos]
  apply ENNReal.ofReal_le_ofReal
  linarith

theorem hc_bound {d : ℕ} (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (Λ : ℝ) (hΛ0 : 0 ≤ Λ)
    (hlamΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ) (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ n, ∀ t : ℝ, 0 ≤ t → ∀ ξ : Config d,
      ∑' η, transN μ lam n t ξ η * (η.card : ℝ≥0∞) ≤
        ENNReal.ofReal (ξ.card * Real.exp ((2 * d * Λ - μ) * t)) := by
  set c := 2 * (d : ℝ) * Λ - μ with hc
  -- facts about ξ
  have hfacts : ∀ ξ : Config d, 0 ≤ ∑ x ∈ bdry ξ, lam (occ ξ x) ∧
      ∑ x ∈ bdry ξ, lam (occ ξ x) ≤ 2 * d * Λ * ξ.card := by
    intro ξ
    refine ⟨Finset.sum_nonneg fun x _ => hlam _ (hc_occ_le ξ x), ?_⟩
    calc ∑ x ∈ bdry ξ, lam (occ ξ x) ≤ ∑ x ∈ bdry ξ, Λ :=
          Finset.sum_le_sum fun x _ => hlamΛ _ (hc_occ_le ξ x)
      _ = (bdry ξ).card * Λ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * d * ξ.card : ℕ) : ℝ) * Λ :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast hc_card_bdry_le ξ) hΛ0
      _ = 2 * d * Λ * ξ.card := by push_cast; ring
  have hK : ∀ ξ : Config d, 0 ≤ (exitRate μ lam ξ + c) * ξ.card := by
    intro ξ
    obtain ⟨hL0, hL⟩ := hfacts ξ
    unfold exitRate
    rcases Nat.eq_zero_or_pos ξ.card with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ ξ.card := by exact_mod_cast h
      have : 0 ≤ μ * ξ.card + ∑ x ∈ bdry ξ, lam (occ ξ x) + c := by
        rw [hc]; nlinarith
      positivity
  have hbase : ∀ t : ℝ, 0 ≤ t → ∀ ξ : Config d,
      (ξ.card : ℝ) * Real.exp (-(exitRate μ lam ξ * t)) ≤ ξ.card * Real.exp (c * t) := by
    intro t ht ξ
    obtain ⟨hL0, hL⟩ := hfacts ξ
    rcases Nat.eq_zero_or_pos ξ.card with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ ξ.card := by exact_mod_cast h
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      unfold exitRate
      rw [hc]
      have hdΛ : 0 ≤ 2 * (d : ℝ) * Λ := by positivity
      have : 0 ≤ μ * ξ.card + ∑ x ∈ bdry ξ, lam (occ ξ x) + (2 * d * Λ - μ) := by
        nlinarith [mul_nonneg hμ (sub_nonneg.mpr h1)]
      nlinarith [mul_nonneg this ht]
  have hti : ∀ (ξ : Config d) (a : ℝ≥0∞),
      ∑' η : Config d, (if ξ = η then a * η.card else 0) = a * ξ.card := by
    intro ξ a
    rw [tsum_eq_single ξ (fun η h => if_neg (Ne.symm h))]
    simp
  intro n
  induction n with
  | zero =>
    intro t ht ξ
    simp only [transN.eq_1, ite_mul, zero_mul]
    rw [hti]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    linarith [hbase t ht ξ]
  | succ n ih =>
    intro t ht ξ
    set q := exitRate μ lam ξ with hq
    simp only [transN.eq_2, transN.eq_1, add_mul, ite_mul, zero_mul]
    rw [ENNReal.tsum_add, hti]
    have hpt : ∀ s ∈ Set.Icc 0 t,
        ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
          ∑' η, transN μ lam n (t - s) ζ η * (η.card : ℝ≥0∞) ≤
        ENNReal.ofReal ((q + c) * ξ.card * Real.exp (c * (t - s))) := by
      intro s hs
      have hts : 0 ≤ t - s := by linarith [hs.2]
      have hlb : ∀ x ∈ bdry ξ, 0 ≤ lam (occ ξ x) := fun x _ => hlam _ (hc_occ_le ξ x)
      calc _ ≤ ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
              ENNReal.ofReal (ζ.card * Real.exp (c * (t - s))) := by
            gcongr with ζ hζ
            exact ih (t - s) hts ζ
        _ = ∑ x ∈ ξ, ENNReal.ofReal μ * ENNReal.ofReal ((ξ.erase x).card * Real.exp (c * (t - s))) +
              ∑ x ∈ bdry ξ, ENNReal.ofReal (lam (occ ξ x)) *
                ENNReal.ofReal ((insert x ξ).card * Real.exp (c * (t - s))) :=
            hc_succ_sum μ lam ξ hμ hlb _
        _ = ENNReal.ofReal (∑ x ∈ ξ, μ * ((ξ.erase x).card * Real.exp (c * (t - s))) +
              ∑ x ∈ bdry ξ, lam (occ ξ x) * ((insert x ξ).card * Real.exp (c * (t - s)))) := by
            rw [ENNReal.ofReal_add (Finset.sum_nonneg fun x _ => by positivity)
              (Finset.sum_nonneg fun x hx => mul_nonneg (hlb x hx) (by positivity)),
              ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity),
              ENNReal.ofReal_sum_of_nonneg (fun x hx => mul_nonneg (hlb x hx) (by positivity))]
            congr 1
            · exact Finset.sum_congr rfl fun x _ => (ENNReal.ofReal_mul hμ).symm
            · exact Finset.sum_congr rfl fun x hx => (ENNReal.ofReal_mul (hlb x hx)).symm
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            have he : 0 < Real.exp (c * (t - s)) := Real.exp_pos _
            set E := Real.exp (c * (t - s))
            have h1 : ∑ x ∈ ξ, μ * ((ξ.erase x).card * E) = ξ.card * (μ * ((ξ.card - 1) * E)) := by
              rw [← nsmul_eq_mul, ← Finset.sum_const]
              refine Finset.sum_congr rfl fun x hx => ?_
              rw [Finset.card_erase_of_mem hx, Nat.cast_sub (Finset.card_pos.mpr ⟨x, hx⟩)]
              simp
            have h2 : ∑ x ∈ bdry ξ, lam (occ ξ x) * ((insert x ξ).card * E) =
                (∑ x ∈ bdry ξ, lam (occ ξ x)) * ((ξ.card + 1) * E) := by
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun x hx => ?_
              have hx' : x ∉ ξ := (Finset.mem_sdiff.mp hx).2
              rw [Finset.card_insert_of_notMem hx']
              push_cast; ring
            rw [h1, h2, hq]
            unfold exitRate
            obtain ⟨hL0, hL⟩ := hfacts ξ
            rw [hc]
            nlinarith [mul_le_mul_of_nonneg_right hL he.le]
    calc ENNReal.ofReal (Real.exp (-(q * t))) * (ξ.card : ℝ≥0∞) +
          ∑' η, (∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s))) *
            ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t - s) ζ η) *
              (η.card : ℝ≥0∞)
        = ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (ξ.card : ℝ) +
          ∑' η, ∫⁻ s in Set.Icc 0 t, (ENNReal.ofReal (Real.exp (-(q * s))) *
            ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t - s) ζ η) *
              (η.card : ℝ≥0∞) := by
          rw [ENNReal.ofReal_natCast]
          congr 1
          refine tsum_congr fun η => ?_
          rw [← lintegral_mul_const' _ _ (ENNReal.natCast_ne_top _)]
      _ ≤ ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (ξ.card : ℝ) +
          ∫⁻ s in Set.Icc 0 t, ∑' η, (ENNReal.ofReal (Real.exp (-(q * s))) *
            ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) * transN μ lam n (t - s) ζ η) *
              (η.card : ℝ≥0∞) := add_le_add le_rfl (hc_tsum_lintegral_le _ _)
      _ = ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (ξ.card : ℝ) +
          ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s))) *
            ∑ ζ ∈ succ ξ, ENNReal.ofReal (rate μ lam ξ ζ) *
              ∑' η, transN μ lam n (t - s) ζ η * (η.card : ℝ≥0∞) := by
          congr 1
          refine lintegral_congr fun s => ?_
          simp only [mul_assoc, Finset.sum_mul]
          rw [ENNReal.tsum_mul_left, Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
          congr 1
          refine Finset.sum_congr rfl fun ζ _ => ?_
          rw [ENNReal.tsum_mul_left]
      _ ≤ ENNReal.ofReal (Real.exp (-(q * t))) * ENNReal.ofReal (ξ.card : ℝ) +
          ∫⁻ s in Set.Icc 0 t, ENNReal.ofReal (Real.exp (-(q * s))) *
            ENNReal.ofReal ((q + c) * ξ.card * Real.exp (c * (t - s))) :=
          add_le_add le_rfl (setLIntegral_mono' measurableSet_Icc fun s hs => by
            gcongr
            exact hpt s hs)
      _ ≤ _ := hc_int q c ξ.card t ht (by positivity) (hK ξ)

theorem lemma_4_7_core {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (t : ℝ) (ht : 0 ≤ t) (ξ : HarrisContact.Extinction.Config d) :
    HarrisContact.Extinction.meanSize μ lam t ξ ≤ (ξ.card : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp ((2 * (d : ℝ) * (Finset.range (2 * d + 1)).sup' (by simp) lam - μ) * t)) := by
  set Λ := (Finset.range (2 * d + 1)).sup' (by simp) lam with hΛ
  have hlamΛ : ∀ k, k ≤ 2 * d → lam k ≤ Λ := fun k hk =>
    Finset.le_sup' lam (Finset.mem_range.mpr (by omega))
  have hΛ0 : 0 ≤ Λ := h0 ▸ hlamΛ 0 (Nat.zero_le _)
  unfold meanSize Extinction.trans
  simp_rw [ENNReal.iSup_mul]
  refine hc_tsum_iSup_le (fun n η => transN μ lam n t ξ η * (η.card : ℝ≥0∞)) ?_ _ ?_
  · intro η
    exact monotone_nat_of_le_succ fun n => by gcongr; exact hc_transN_mono μ lam n t ξ η
  · intro n
    refine (hc_bound μ lam hμ Λ hΛ0 hlamΛ hlam n t ht ξ).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]

end HarrisContact.MeanSize

open HarrisContact.MeanSize


theorem solution {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (t : ℝ) (ht : 0 ≤ t) (ξ : HarrisContact.Extinction.Config d) :
    HarrisContact.Extinction.meanSize μ lam t ξ ≤ (ξ.card : ℝ≥0∞) *
      ENNReal.ofReal (Real.exp ((2 * (d : ℝ) * (Finset.range (2 * d + 1)).sup' (by simp) lam - μ) * t)) := by
  exact lemma_4_7_core hd μ lam hμ h0 hlam t ht ξ
