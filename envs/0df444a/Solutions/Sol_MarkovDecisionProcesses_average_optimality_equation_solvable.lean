-- Prove2me | solution 1 for MarkovDecisionProcesses.average_optimality_equation_solvable
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T06:36:04.503758+00:00
-- url     : https://prove2.me/submissions/b26cc1f8-ec22-45ff-8002-8f32edcf6982

import Definitions.Def_MarkovDecisionProcesses_AverageReward



namespace MarkovDecisionProcesses

open Filter

variable {S A : Type*} [Fintype S] [Fintype A]

lemma avg_le {ι : Type*} (s : Finset ι) (w X : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (Y : ℝ) (h : ∀ i ∈ s, X i ≤ Y) : ∑ i ∈ s, w i * X i ≤ Y := by
  calc ∑ i ∈ s, w i * X i ≤ ∑ i ∈ s, w i * Y :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (hw i hi)
    _ = Y := by rw [← Finset.sum_mul, hs, one_mul]

lemma le_avg {ι : Type*} (s : Finset ι) (w X : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hs : ∑ i ∈ s, w i = 1) (Y : ℝ) (h : ∀ i ∈ s, Y ≤ X i) : Y ≤ ∑ i ∈ s, w i * X i := by
  calc Y = ∑ i ∈ s, w i * Y := by rw [← Finset.sum_mul, hs, one_mul]
    _ ≤ ∑ i ∈ s, w i * X i :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (h i hi) (hw i hi)

/-- A bound on all rewards. -/
noncomputable def Rm (M : StationaryMDP S A) : ℝ := ∑ s, ∑ a, |M.reward s a|

lemma abs_reward_le (M : StationaryMDP S A) (s : S) (a : A) : |M.reward s a| ≤ Rm M := by
  unfold Rm
  calc |M.reward s a| ≤ ∑ a', |M.reward s a'| :=
        Finset.single_le_sum (f := fun a' => |M.reward s a'|) (fun _ _ => abs_nonneg _)
          (Finset.mem_univ a)
    _ ≤ ∑ s', ∑ a', |M.reward s' a'| :=
        Finset.single_le_sum (f := fun s' => ∑ a', |M.reward s' a'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ s)

lemma Rm_nonneg (M : StationaryMDP S A) : 0 ≤ Rm M :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma tr_bound {M : StationaryMDP S A} (π : AvgHRPolicy M) :
    ∀ k t hist s, |totalReward π k t hist s| ≤ k * Rm M := by
  intro k
  induction k with
  | zero => intro t hist s; simp [totalReward]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    rw [abs_le]
    push_cast
    constructor
    · apply le_avg _ _ _ (fun a _ => π.nonneg _ _ _ _) (π.sum_one _ _ _)
      intro a _
      have h1 : -(k * Rm M) ≤ ∑ j, M.trans s a j * totalReward π k (t + 1) (hist ++ [(s, a)]) j :=
        le_avg _ _ _ (fun j _ => M.trans_nonneg _ _ _) (M.trans_sum _ _) _
          (fun j _ => (abs_le.mp (ih _ _ _)).1)
      have h2 := (abs_le.mp (abs_reward_le M s a)).1
      linarith
    · apply avg_le _ _ _ (fun a _ => π.nonneg _ _ _ _) (π.sum_one _ _ _)
      intro a _
      have h1 : ∑ j, M.trans s a j * totalReward π k (t + 1) (hist ++ [(s, a)]) j ≤ k * Rm M :=
        avg_le _ _ _ (fun j _ => M.trans_nonneg _ _ _) (M.trans_sum _ _) _
          (fun j _ => (abs_le.mp (ih _ _ _)).2)
      have h2 := (abs_le.mp (abs_reward_le M s a)).2
      linarith

noncomputable def hc (h : S → ℝ) : ℝ := ∑ s, |h s|

lemma abs_h_le (h : S → ℝ) (s : S) : |h s| ≤ hc h :=
  Finset.single_le_sum (f := fun s => |h s|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

lemma tr_upper {M : StationaryMDP S A} (π : AvgHRPolicy M) (g : ℝ) (h : S → ℝ)
    (hB : ∀ s, ∀ a ∈ M.admissible s, M.reward s a - g + ∑ j, M.trans s a j * h j - h s ≤ 0) :
    ∀ k t hist s, totalReward π k t hist s ≤ k * g + h s + hc h := by
  intro k
  induction k with
  | zero =>
    intro t hist s
    simp only [totalReward, Nat.cast_zero, zero_mul, zero_add]
    linarith [(abs_le.mp (abs_h_le h s)).1]
  | succ k ih =>
    intro t hist s
    simp only [totalReward]
    apply avg_le _ _ _ (fun a _ => π.nonneg _ _ _ _) (π.sum_one _ _ _)
    intro a ha
    have h1 : ∑ j, M.trans s a j * totalReward π k (t + 1) (hist ++ [(s, a)]) j ≤
        ∑ j, M.trans s a j * (k * g + h j + hc h) :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _ _ _) (M.trans_nonneg _ _ _)
    have h2 : ∑ j, M.trans s a j * (k * g + h j + hc h) =
        (k * g + hc h) + ∑ j, M.trans s a j * h j := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.trans_sum, one_mul]
      ring
    have h3 := hB s a ha
    push_cast
    linarith

lemma tr_lower_stat [DecidableEq A] {M : StationaryMDP S A} (d : S → A)
    (hd : ∀ s, d s ∈ M.admissible s) (g : ℝ) (h : S → ℝ)
    (hB : ∀ s, 0 ≤ M.reward s (d s) - g + ∑ j, M.trans s (d s) j * h j - h s) :
    ∀ k t hist s, k * g + h s - hc h ≤ totalReward (stationaryPolicy M d hd) k t hist s := by
  intro k
  induction k with
  | zero =>
    intro t hist s
    simp only [totalReward, Nat.cast_zero, zero_mul, zero_add]
    linarith [(abs_le.mp (abs_h_le h s)).2]
  | succ k ih =>
    intro t hist s
    have hq : ∀ t' hist' s' a, (stationaryPolicy M d hd).q t' hist' s' a =
        if a = d s' then 1 else 0 := fun _ _ _ _ => rfl
    simp only [totalReward, hq]
    rw [Finset.sum_eq_single_of_mem (d s) (hd s) (fun b _ hb => by simp [hb])]
    simp only [if_true, one_mul]
    have h1 : ∑ j, M.trans s (d s) j * (k * g + h j - hc h) ≤
        ∑ j, M.trans s (d s) j *
          totalReward (stationaryPolicy M d hd) k (t + 1) (hist ++ [(s, d s)]) j :=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (ih _ _ _) (M.trans_nonneg _ _ _)
    have h2 : ∑ j, M.trans s (d s) j * (k * g + h j - hc h) =
        (k * g - hc h) + ∑ j, M.trans s (d s) j * h j := by
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_mul, M.trans_sum, one_mul]
      ring
    have h3 := hB s
    push_cast
    linarith

lemma limsup_le_of_bounds (u : ℕ → ℝ) (g C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hu : ∀ N, u N ≤ N * g + C) (hb : ∀ N, |u N| ≤ N * R) :
    limsup (fun N : ℕ => u N / N) atTop ≤ g := by
  have hlow : ∀ N : ℕ, -R ≤ u N / N := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp [hR]
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [le_div_iff₀ hN]
      linarith [(abs_le.mp (hb N)).1]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  refine limsup_le_of_le (isCoboundedUnder_le_of_le atTop hlow) ?_
  filter_upwards [eventually_ge_atTop (⌈C / ε⌉₊ + 1)] with N hN
  have hNpos : (0 : ℝ) < N := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hN
    linarith
  have hCN : C / ε ≤ N := by
    have := Nat.le_ceil (C / ε)
    have h2 : (⌈C / ε⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_right _ 1) hN
    linarith
  rw [div_le_iff₀ hNpos]
  have : C ≤ ε * N := by rwa [div_le_iff₀ hε, mul_comm] at hCN
  nlinarith [hu N]

lemma le_liminf_of_bounds (u : ℕ → ℝ) (g C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hu : ∀ N, N * g - C ≤ u N) (hb : ∀ N, |u N| ≤ N * R) :
    g ≤ liminf (fun N : ℕ => u N / N) atTop := by
  have hup : ∀ N : ℕ, u N / N ≤ R := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp [hR]
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [div_le_iff₀ hN]
      linarith [(abs_le.mp (hb N)).2]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have key : g - ε ≤ liminf (fun N : ℕ => u N / N) atTop := by
    refine le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hup) ?_
    filter_upwards [eventually_ge_atTop (⌈C / ε⌉₊ + 1)] with N hN
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_left 1 _) hN
      linarith
    have hCN : C / ε ≤ N := by
      have := Nat.le_ceil (C / ε)
      have h2 : (⌈C / ε⌉₊ : ℝ) ≤ N := by exact_mod_cast le_trans (Nat.le_add_right _ 1) hN
      linarith
    rw [le_div_iff₀ hNpos]
    have : C ≤ ε * N := by rwa [div_le_iff₀ hε, mul_comm] at hCN
    nlinarith [hu N]
  linarith

lemma gain_bounds {M : StationaryMDP S A} (π : AvgHRPolicy M) (s : S) :
    gainInf π s ≤ gainSup π s ∧ gainSup π s ≤ Rm M ∧ -Rm M ≤ gainInf π s := by
  have hR := Rm_nonneg M
  have hb := fun N => tr_bound π N 0 [] s
  have hup : ∀ N : ℕ, totalReward π N 0 [] s / N ≤ Rm M := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp [hR]
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [div_le_iff₀ hN]; linarith [(abs_le.mp (hb N)).2]
  have hlow : ∀ N : ℕ, -Rm M ≤ totalReward π N 0 [] s / N := by
    intro N
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · subst h0; simp [hR]
    · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
      rw [le_div_iff₀ hN]; linarith [(abs_le.mp (hb N)).1]
  have bU : IsBoundedUnder (· ≤ ·) atTop (fun N : ℕ => totalReward π N 0 [] s / N) :=
    isBoundedUnder_of ⟨Rm M, hup⟩
  have bL : IsBoundedUnder (· ≥ ·) atTop (fun N : ℕ => totalReward π N 0 [] s / N) :=
    isBoundedUnder_of ⟨-Rm M, hlow⟩
  refine ⟨liminf_le_limsup bU bL, ?_, ?_⟩
  · exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop hlow) (Eventually.of_forall hup)
  · exact le_liminf_of_le (isCoboundedUnder_ge_of_le atTop hup) (Eventually.of_forall hlow)


lemma bdd_sup {M : StationaryMDP S A} (s : S) :
    BddAbove (Set.range fun π : AvgHRPolicy M => gainSup π s) :=
  ⟨Rm M, by rintro _ ⟨π, rfl⟩; exact (gain_bounds π s).2.1⟩

lemma bdd_inf {M : StationaryMDP S A} (s : S) :
    BddAbove (Set.range fun π : AvgHRPolicy M => gainInf π s) :=
  ⟨Rm M, by rintro _ ⟨π, rfl⟩; exact (gain_bounds π s).1.trans (gain_bounds π s).2.1⟩

lemma part_a [DecidableEq A] (M : StationaryMDP S A) (g : ℝ) (h : S → ℝ)
    (hB : ∀ s, optimalityResidual M g h s ≤ 0) : ∀ s, optGainSup M s ≤ g := by
  have hB' : ∀ s, ∀ a ∈ M.admissible s,
      M.reward s a - g + ∑ j, M.trans s a j * h j - h s ≤ 0 := by
    intro s a ha
    have := Finset.le_sup' (fun a => M.reward s a - g + ∑ j, M.trans s a j * h j - h s) ha
    exact this.trans (hB s)
  intro s
  haveI : Nonempty (AvgHRPolicy M) :=
    ⟨stationaryPolicy M (fun s => (M.admissible_nonempty s).choose)
      (fun s => (M.admissible_nonempty s).choose_spec)⟩
  refine ciSup_le fun π => ?_
  have hC : 0 ≤ h s + hc h := by linarith [(abs_le.mp (abs_h_le h s)).1]
  exact limsup_le_of_bounds (fun N => totalReward π N 0 [] s) g (h s + hc h) (Rm M) hC
    (Rm_nonneg M) (fun N => by have := tr_upper π g h hB' N 0 [] s; linarith)
    (fun N => tr_bound π N 0 [] s)

lemma stat_gain_ge [DecidableEq A] {M : StationaryMDP S A} (d : S → A)
    (hd : ∀ s, d s ∈ M.admissible s) (g : ℝ) (h : S → ℝ)
    (hB : ∀ s, 0 ≤ M.reward s (d s) - g + ∑ j, M.trans s (d s) j * h j - h s) (s : S) :
    g ≤ gainInf (stationaryPolicy M d hd) s := by
  have hC : 0 ≤ hc h - h s := by linarith [(abs_le.mp (abs_h_le h s)).2]
  exact le_liminf_of_bounds (fun N => totalReward (stationaryPolicy M d hd) N 0 [] s) g
    (hc h - h s) (Rm M) hC (Rm_nonneg M)
    (fun N => by have := tr_lower_stat d hd g h hB N 0 [] s; linarith)
    (fun N => tr_bound _ N 0 [] s)

lemma part_b [DecidableEq A] (M : StationaryMDP S A) (g : ℝ) (h : S → ℝ)
    (hB : ∀ s, 0 ≤ optimalityResidual M g h s) :
    ∀ s, g ≤ (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
                  gainInf (stationaryPolicy M d.1 d.2) s) ∧
        (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
            gainInf (stationaryPolicy M d.1 d.2) s) ≤ optGainInf M s := by
  have hex : ∀ s, ∃ a ∈ M.admissible s, optimalityResidual M g h s =
      M.reward s a - g + ∑ j, M.trans s a j * h j - h s := fun s =>
    Finset.exists_mem_eq_sup' (M.admissible_nonempty s) _
  choose d hd hdeq using hex
  have hBd : ∀ s, 0 ≤ M.reward s (d s) - g + ∑ j, M.trans s (d s) j * h j - h s := by
    intro s; rw [← hdeq s]; exact hB s
  intro s
  haveI : Nonempty {d : S → A // ∀ s, d s ∈ M.admissible s} := ⟨⟨d, hd⟩⟩
  have hbddD : BddAbove (Set.range fun d' : {d : S → A // ∀ s, d s ∈ M.admissible s} =>
      gainInf (stationaryPolicy M d'.1 d'.2) s) :=
    ⟨Rm M, by rintro _ ⟨π, rfl⟩; exact (gain_bounds _ s).1.trans (gain_bounds _ s).2.1⟩
  constructor
  · exact le_ciSup_of_le hbddD ⟨d, hd⟩ (stat_gain_ge d hd g h hBd s)
  · exact ciSup_le fun d' => le_ciSup (bdd_inf s) (stationaryPolicy M d'.1 d'.2)

theorem bounds_main {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (g : ℝ) (h : S → ℝ) :
    ((∀ s, optimalityResidual M g h s ≤ 0) → ∀ s, optGainSup M s ≤ g) ∧
    ((∀ s, 0 ≤ optimalityResidual M g h s) →
      ∀ s, g ≤ (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
                  gainInf (stationaryPolicy M d.1 d.2) s) ∧
        (⨆ d : {d : S → A // ∀ s, d s ∈ M.admissible s},
            gainInf (stationaryPolicy M d.1 d.2) s) ≤ optGainInf M s) ∧
    ((∀ s, optimalityResidual M g h s = 0) →
      ∀ s, optGainSup M s = g ∧ optGainInf M s = g) := by
  refine ⟨part_a M g h, part_b M g h, ?_⟩
  intro h0 s
  have ha := part_a M g h (fun s => (h0 s).le) s
  have hb := part_b M g h (fun s => (h0 s).ge) s
  haveI : Nonempty (AvgHRPolicy M) :=
    ⟨stationaryPolicy M (fun s => (M.admissible_nonempty s).choose)
      (fun s => (M.admissible_nonempty s).choose_spec)⟩
  have hc : optGainInf M s ≤ optGainSup M s :=
    ciSup_mono (bdd_sup s) fun π => (gain_bounds π s).1
  constructor <;> linarith [hb.1, hb.2]

theorem improving_main {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (gstar : ℝ) (hstar : S → ℝ)
    (hB : ∀ s, optimalityResidual M gstar hstar s = 0)
    (d : S → A) (hd : IsImproving M hstar d) :
    IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1)) := by
  intro π s
  haveI : Nonempty (AvgHRPolicy M) := ⟨π⟩
  have hup : gainSup π s ≤ gstar :=
    (le_ciSup (bdd_sup s) π).trans (part_a M gstar hstar (fun s => (hB s).le) s)
  have hBd : ∀ s, 0 ≤ M.reward s (d s) - gstar + ∑ j, M.trans s (d s) j * hstar j - hstar s := by
    intro s
    obtain ⟨a, ha, haeq⟩ := Finset.exists_mem_eq_sup' (M.admissible_nonempty s)
      (fun a => M.reward s a - gstar + ∑ j, M.trans s a j * hstar j - hstar s)
    have h0 : M.reward s a - gstar + ∑ j, M.trans s a j * hstar j - hstar s = 0 := by
      rw [← haeq]; exact hB s
    have hle := Finset.le_sup' (fun a => M.reward s a + ∑ j, M.trans s a j * hstar j) ha
    rw [← (hd s).2] at hle
    linarith
  exact hup.trans (stat_gain_ge d (fun s => (hd s).1) gstar hstar hBd s)


/-! ## Existence for unichain models -/

lemma sup'_shift {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f : ι → ℝ) (c : ℝ) :
    s.sup' hs (fun a => f a + c) = s.sup' hs f + c := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun a ha => by linarith [Finset.le_sup' f ha]
  · obtain ⟨a, ha, hfa⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hfa]
    exact Finset.le_sup' (fun a => f a + c) ha

lemma sup'_le_sup'_add {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (f g : ι → ℝ) (c : ℝ)
    (h : ∀ a ∈ s, f a ≤ g a + c) : s.sup' hs f ≤ s.sup' hs g + c :=
  Finset.sup'_le _ _ fun a ha => (h a ha).trans (by linarith [Finset.le_sup' g ha])

/-- every state reaches a recurrent state -/
lemma exists_recurrent_reach [DecidableEq S] (P : S → S → ℝ) (i : S) :
    ∃ j, Accessible P i j ∧ IsRecurrent P j := by
  classical
  let R : S → Finset S := fun j => Finset.univ.filter (fun k => Accessible P j k)
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image (Finset.univ.filter (fun k => Accessible P i k))
    (fun j => (R j).card) ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj hmin
  refine ⟨j, hj, fun k hk => ?_⟩
  have hsub : R k ⊆ R j := by
    intro l hl
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
    exact hk.trans hl
  have hcard := hmin k (hj.trans hk)
  have heq : R k = R j := Finset.eq_of_subset_of_card_le hsub hcard
  have : j ∈ R k := by rw [heq]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Relation.ReflTransGen.refl⟩
  simpa [R] using this

lemma unichain_center [Nonempty S] (P : S → S → ℝ) (hU : IsUnichainMatrix P) :
    ∃ c, ∀ s, Accessible P s c := by
  classical
  obtain ⟨c, -, hc⟩ := exists_recurrent_reach P (Classical.arbitrary S)
  refine ⟨c, fun s => ?_⟩
  obtain ⟨j, hsj, hj⟩ := exists_recurrent_reach P s
  exact hsj.trans (hU j c hj hc)

/-- the key span estimate for a single transition matrix -/
lemma span_bound [Nonempty S] (P : S → S → ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (c : S) (hreach : ∀ s, Accessible P s c) (F : ℝ) (hF : 0 ≤ F) :
    ∃ C : ℝ, ∀ β : ℝ, 0 ≤ β → β ≤ 1 → ∀ w : S → ℝ, w c = 0 →
      (∀ s, |w s - β * ∑ j, P s j * w j| ≤ F) → ∀ s, |w s| ≤ C := by
  classical
  -- local claim along a path to `c`
  have claim : ∀ s, Accessible P s c → ∃ ρ K : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 0 ≤ K ∧
      ∀ β : ℝ, 0 ≤ β → β ≤ 1 → ∀ w : S → ℝ, w c = 0 →
        (∀ s, |w s - β * ∑ j, P s j * w j| ≤ F) → ∀ W : ℝ, (∀ i, |w i| ≤ W) →
          |w s| ≤ (1 - ρ) * W + K := by
    intro s hs
    induction hs using Relation.ReflTransGen.head_induction_on with
    | refl =>
      refine ⟨1, 0, one_pos, le_rfl, le_rfl, fun β _ _ w hw _ W _ => ?_⟩
      rw [hw]; simp
    | @head a b hsj _ ih =>
      obtain ⟨ρ, K, hρ, hρ1, hK, hb⟩ := ih
      set p := P a b with hp
      have hp1 : p ≤ 1 := by
        rw [← hP1 a]
        exact Finset.single_le_sum (f := fun i => P a i) (fun i _ => hP0 a i)
          (Finset.mem_univ b)
      refine ⟨p * ρ, F + p * K, mul_pos hsj hρ, by nlinarith, by positivity,
        fun β hβ0 hβ1 w hw hF' W hW => ?_⟩
      have h1 := hF' a
      have hwj := hb β hβ0 hβ1 w hw hF' W hW
      have hsum : |β * ∑ i, P a i * w i| ≤ p * |w b| + (1 - p) * W := by
        rw [abs_mul, abs_of_nonneg hβ0]
        have hs1 : |∑ i, P a i * w i| ≤ ∑ i, P a i * |w i| := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
          congr 1; funext i; rw [abs_mul, abs_of_nonneg (hP0 a i)]
        have hs2 : ∑ i, P a i * |w i| ≤ p * |w b| + (1 - p) * W := by
          rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b)]
          have : ∑ i ∈ Finset.univ.erase b, P a i * |w i| ≤
              ∑ i ∈ Finset.univ.erase b, P a i * W :=
            Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hW i) (hP0 a i)
          have e : ∑ i ∈ Finset.univ.erase b, P a i = 1 - p := by
            rw [← hP1 a, ← Finset.add_sum_erase _ _ (Finset.mem_univ b)]; ring
          rw [← Finset.sum_mul, e] at this
          linarith
        have hW0 : 0 ≤ W := (abs_nonneg _).trans (hW b)
        have hsum_nn : 0 ≤ ∑ i, P a i * |w i| :=
          Finset.sum_nonneg fun i _ => mul_nonneg (hP0 a i) (abs_nonneg _)
        calc β * |∑ i, P a i * w i| ≤ 1 * |∑ i, P a i * w i| :=
              mul_le_mul_of_nonneg_right hβ1 (abs_nonneg _)
          _ ≤ p * |w b| + (1 - p) * W := by rw [one_mul]; exact hs1.trans hs2
      have h2 : |w a| ≤ F + |β * ∑ i, P a i * w i| := by
        have := abs_sub_abs_le_abs_sub (w a) (β * ∑ b, P a b * w b)
        linarith
      have hp0 : 0 ≤ p := hP0 a b
      nlinarith [mul_le_mul_of_nonneg_left hwj hp0]
  choose ρ K hρ hρ1 hK hb using fun s => claim s (hreach s)
  refine ⟨∑ s, K s / ρ s, fun β hβ0 hβ1 w hw hF' s => ?_⟩
  obtain ⟨s0, -, hs0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |w i|)
  set W := Finset.univ.sup' Finset.univ_nonempty (fun i => |w i|) with hWdef
  have hW : ∀ i, |w i| ≤ W := fun i => Finset.le_sup' (fun i => |w i|) (Finset.mem_univ i)
  have h0 := hb s0 β hβ0 hβ1 w hw hF' W hW
  rw [← hs0] at h0
  have hWle : W ≤ K s0 / ρ s0 := by
    rw [le_div_iff₀ (hρ s0)]; nlinarith
  have hsum : K s0 / ρ s0 ≤ ∑ s, K s / ρ s :=
    Finset.single_le_sum (f := fun s => K s / ρ s)
      (fun s _ => div_nonneg (hK s) (hρ s).le) (Finset.mem_univ s0)
  linarith [hW s]

/-- c-free span bound -/
lemma span_bound2 [Nonempty S] (P : S → S → ℝ) (hP0 : ∀ i j, 0 ≤ P i j)
    (hP1 : ∀ i, ∑ j, P i j = 1) (hU : IsUnichainMatrix P) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → β < 1 → ∀ v e : S → ℝ,
      (∀ s, v s = e s + β * ∑ j, P s j * v j) → (∀ s, |e s| ≤ R) →
      (∀ s, |v s| ≤ R / (1 - β)) → ∀ s t, |v s - v t| ≤ C := by
  classical
  obtain ⟨c, hc⟩ := unichain_center P hU
  obtain ⟨C0, hC0⟩ := span_bound P hP0 hP1 c hc (2 * R) (by positivity)
  refine ⟨2 * max C0 0, by positivity, fun β hβ0 hβ1 v e hv he hvb s t => ?_⟩
  set w : S → ℝ := fun i => v i - v c with hw
  have hwc : w c = 0 := by simp [w]
  have hres : ∀ s, |w s - β * ∑ j, P s j * w j| ≤ 2 * R := by
    intro s
    have e1 : w s - β * ∑ j, P s j * w j = e s - (1 - β) * v c := by
      have : ∑ j, P s j * w j = ∑ j, P s j * v j - v c := by
        simp only [w, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP1 s, one_mul]
      rw [this]; simp only [w]; rw [hv s]; ring
    rw [e1]
    have h1 : |(1 - β) * v c| ≤ R := by
      rw [abs_mul, abs_of_pos (by linarith : (0:ℝ) < 1 - β)]
      have := hvb c
      rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - β)] at this
      linarith
    calc |e s - (1 - β) * v c| ≤ |e s| + |(1 - β) * v c| := by
          simpa using abs_sub_le (e s) 0 ((1 - β) * v c)
      _ ≤ 2 * R := by linarith [he s]
  have hs := hC0 β hβ0 hβ1.le w hwc hres s
  have ht := hC0 β hβ0 hβ1.le w hwc hres t
  have : v s - v t = w s - w t := by simp [w]
  rw [this]
  calc |w s - w t| ≤ |w s| + |w t| := by simpa using abs_sub_le (w s) 0 (w t)
    _ ≤ 2 * max C0 0 := by linarith [le_max_left C0 0]

/-- the discounted Bellman operator -/
noncomputable def bellman (M : StationaryMDP S A) (β : ℝ) (v : S → ℝ) : S → ℝ :=
  fun s => (M.admissible s).sup' (M.admissible_nonempty s)
    (fun a => M.reward s a + β * ∑ j, M.trans s a j * v j)

lemma bellman_le (M : StationaryMDP S A) (β : ℝ) (hβ : 0 ≤ β) (u v : S → ℝ) (D : ℝ)
    (hD : ∀ j, |u j - v j| ≤ D) (s : S) :
    bellman M β u s ≤ bellman M β v s + β * D := by
  apply sup'_le_sup'_add
  intro a _
  have h1 : ∑ j, M.trans s a j * u j ≤ ∑ j, M.trans s a j * (v j + D) :=
    Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (by linarith [(abs_le.mp (hD j)).2]) (M.trans_nonneg _ _ _)
  have h2 : ∑ j, M.trans s a j * (v j + D) = ∑ j, M.trans s a j * v j + D := by
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, M.trans_sum, one_mul]
  rw [h2] at h1
  have := mul_le_mul_of_nonneg_left h1 hβ
  linarith

lemma bellman_contracting (M : StationaryMDP S A) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ContractingWith (Real.toNNReal β) (bellman M β) := by
  refine ⟨by rw [Real.toNNReal_lt_one]; exact hβ1, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  rw [Real.coe_toNNReal _ hβ0]
  refine (dist_pi_le_iff (by positivity)).2 fun s => ?_
  have hD : ∀ j, |u j - v j| ≤ dist u v := fun j => by
    have := dist_le_pi_dist u v j; rwa [Real.dist_eq] at this
  have hD' : ∀ j, |v j - u j| ≤ dist u v := fun j => by rw [abs_sub_comm]; exact hD j
  rw [Real.dist_eq, abs_le]
  constructor
  · linarith [bellman_le M β hβ0 v u _ hD' s]
  · linarith [bellman_le M β hβ0 u v _ hD s]

lemma exists_disc_fixed (M : StationaryMDP S A) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ v : S → ℝ, bellman M β v = v :=
  ⟨_, (bellman_contracting M hβ0 hβ1).fixedPoint_isFixedPt⟩

lemma fixed_bound [Nonempty S] (M : StationaryMDP S A) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (v : S → ℝ) (hv : bellman M β v = v) : ∀ s, |v s| ≤ Rm M / (1 - β) := by
  obtain ⟨s0, -, hs0⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => |v i|)
  set W := Finset.univ.sup' Finset.univ_nonempty (fun i => |v i|) with hWdef
  have hW : ∀ i, |v i| ≤ W := fun i => Finset.le_sup' (fun i => |v i|) (Finset.mem_univ i)
  have key : ∀ s, |v s| ≤ Rm M + β * W := by
    intro s
    rw [← congrFun hv s]
    obtain ⟨a, ha, hae⟩ := Finset.exists_mem_eq_sup' (M.admissible_nonempty s)
      (fun a => M.reward s a + β * ∑ j, M.trans s a j * v j)
    show |(M.admissible s).sup' _ _| ≤ _
    rw [hae]
    have hl : -W ≤ ∑ j, M.trans s a j * v j :=
      le_avg _ _ _ (fun j _ => M.trans_nonneg _ _ _) (M.trans_sum _ _) _
        (fun j _ => (abs_le.mp (hW j)).1)
    have hu : ∑ j, M.trans s a j * v j ≤ W :=
      avg_le _ _ _ (fun j _ => M.trans_nonneg _ _ _) (M.trans_sum _ _) _
        (fun j _ => (abs_le.mp (hW j)).2)
    have hr := abs_le.mp (abs_reward_le M s a)
    rw [abs_le]
    constructor <;> nlinarith
  have h0 := key s0
  rw [← hs0] at h0
  intro s
  rw [le_div_iff₀ (by linarith : (0:ℝ) < 1 - β)]
  nlinarith [hW s]

lemma uniform_span [Nonempty S] (M : StationaryMDP S A) (hM : IsUnichain M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ β : ℝ, 0 ≤ β → β < 1 → ∀ v : S → ℝ, bellman M β v = v →
      ∀ s t, |v s - v t| ≤ C := by
  classical
  have hd : ∀ d : S → A, ∃ C : ℝ, 0 ≤ C ∧ ((∀ s, d s ∈ M.admissible s) →
      ∀ β : ℝ, 0 ≤ β → β < 1 → ∀ v e : S → ℝ,
      (∀ s, v s = e s + β * ∑ j, transMatrix M d s j * v j) → (∀ s, |e s| ≤ Rm M) →
      (∀ s, |v s| ≤ Rm M / (1 - β)) → ∀ s t, |v s - v t| ≤ C) := by
    intro d
    by_cases had : ∀ s, d s ∈ M.admissible s
    · obtain ⟨C, hC, h⟩ := span_bound2 (transMatrix M d) (fun i j => M.trans_nonneg _ _ _)
        (fun i => M.trans_sum _ _) (hM d had) (Rm M) (Rm_nonneg M)
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h had⟩
  choose C hC0 hC using hd
  refine ⟨∑ d, C d, Finset.sum_nonneg fun d _ => hC0 d, fun β hβ0 hβ1 v hv s t => ?_⟩
  have hex : ∀ s, ∃ a ∈ M.admissible s,
      bellman M β v s = M.reward s a + β * ∑ j, M.trans s a j * v j :=
    fun s => Finset.exists_mem_eq_sup' (M.admissible_nonempty s) _
  choose d hdA hdeq using hex
  have h1 := hC d hdA β hβ0 hβ1 v (fun s => M.reward s (d s))
    (fun s => by
      show v s = M.reward s (d s) + β * ∑ j, M.trans s (d s) j * v j
      rw [← hdeq s, congrFun hv s])
    (fun s => abs_reward_le M s (d s)) (fixed_bound M hβ0 hβ1 v hv) s t
  exact h1.trans (Finset.single_le_sum (f := C) (fun d _ => hC0 d) (Finset.mem_univ d))

theorem aoe_exists [Nonempty S] (M : StationaryMDP S A) (hM : IsUnichain M) :
    ∃ (g : ℝ) (h : S → ℝ), ∀ s, optimalityResidual M g h s = 0 := by
  obtain ⟨C, hC0, hC⟩ := uniform_span M hM
  let s0 : S := Classical.arbitrary S
  let β : ℕ → ℝ := fun k => 1 - 1 / ((k:ℝ) + 1)
  have hβ0 : ∀ k, 0 ≤ β k := by
    intro k; simp only [β]; rw [sub_nonneg, div_le_one (by positivity)]
    linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hβ1 : ∀ k, β k < 1 := by
    intro k; simp only [β]; have : (0:ℝ) < 1 / ((k:ℝ)+1) := by positivity
    linarith
  have hβlim : Tendsto β atTop (nhds 1) := by
    have := (tendsto_const_nhds (x := (1:ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
    rw [sub_zero] at this
    exact this
  choose v hv using fun k => exists_disc_fixed M (hβ0 k) (hβ1 k)
  let g : ℕ → ℝ := fun k => (1 - β k) * v k s0
  let h : ℕ → S → ℝ := fun k s => v k s - v k s0
  have hg : ∀ k, |g k| ≤ Rm M := by
    intro k
    have := fixed_bound M (hβ0 k) (hβ1 k) (v k) (hv k) s0
    have hp : (0:ℝ) < 1 - β k := by linarith [hβ1 k]
    rw [le_div_iff₀ hp] at this
    simp only [g]; rw [abs_mul, abs_of_pos hp]; linarith
  have hh : ∀ k s, |h k s| ≤ C := fun k s => hC _ (hβ0 k) (hβ1 k) _ (hv k) s s0
  have heq : ∀ k s, h k s + g k = (M.admissible s).sup' (M.admissible_nonempty s)
      (fun a => M.reward s a + β k * ∑ j, M.trans s a j * h k j) := by
    intro k s
    have e1 : (fun a => M.reward s a + β k * ∑ j, M.trans s a j * h k j) =
        fun a => (M.reward s a + β k * ∑ j, M.trans s a j * v k j) + (-(β k * v k s0)) := by
      funext a
      have : ∑ j, M.trans s a j * h k j = ∑ j, M.trans s a j * v k j - v k s0 := by
        simp only [h, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, M.trans_sum, one_mul]
      rw [this]; ring
    rw [e1, sup'_shift]
    have := congrFun (hv k) s
    simp only [bellman] at this
    rw [this]; simp only [h, g]; ring
  let x : ℕ → ℝ × (S → ℝ) := fun k => (g k, h k)
  have hx : ∀ k, x k ∈ Metric.closedBall (0 : ℝ × (S → ℝ)) (Rm M + C) := by
    intro k
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    apply max_le
    · rw [Real.norm_eq_abs]; linarith [hg k]
    · refine (pi_norm_le_iff_of_nonneg (by linarith [Rm_nonneg M])).2 fun s => ?_
      rw [Real.norm_eq_abs]; linarith [hh k s, Rm_nonneg M]
  obtain ⟨⟨gs, hs⟩, -, φ, hφ, hlim⟩ :=
    tendsto_subseq_of_bounded Metric.isBounded_closedBall hx
  have hgl : Tendsto (fun n => g (φ n)) atTop (nhds gs) :=
    (continuous_fst.tendsto _).comp hlim
  have hhl : ∀ s, Tendsto (fun n => h (φ n) s) atTop (nhds (hs s)) := fun s =>
    (((continuous_apply s).comp continuous_snd).tendsto _).comp hlim
  have hβφ : Tendsto (fun n => β (φ n)) atTop (nhds 1) := hβlim.comp hφ.tendsto_atTop
  refine ⟨gs, hs, fun s => ?_⟩
  have hr : Tendsto (fun n => (M.admissible s).sup' (M.admissible_nonempty s)
      (fun a => M.reward s a + β (φ n) * ∑ j, M.trans s a j * h (φ n) j)) atTop
      (nhds ((M.admissible s).sup' (M.admissible_nonempty s)
        (fun a => M.reward s a + 1 * ∑ j, M.trans s a j * hs j))) :=
    Tendsto.finset_sup'_nhds_apply (f := fun a n => M.reward s a + β (φ n) *
        ∑ j, M.trans s a j * h (φ n) j) _
      (fun a _ => tendsto_const_nhds.add
        (hβφ.mul (tendsto_finset_sum _ fun j _ => (hhl j).const_mul _)))
  have hl : Tendsto (fun n => h (φ n) s + g (φ n)) atTop (nhds (hs s + gs)) :=
    (hhl s).add hgl
  have hr' := hr.congr (fun n => (heq (φ n) s).symm)
  have hu := tendsto_nhds_unique hl hr'
  unfold optimalityResidual
  have e2 : (fun a => M.reward s a - gs + ∑ j, M.trans s a j * hs j - hs s) =
      fun a => (M.reward s a + 1 * ∑ j, M.trans s a j * hs j) + (-gs - hs s) := by
    funext a; ring
  rw [e2, sup'_shift, ← hu]
  ring

theorem aoe_main {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] (M : StationaryMDP S A) (hM : IsUnichain M) :
    (∃ (g : ℝ) (h : S → ℝ), ∀ s, optimalityResidual M g h s = 0) ∧
      ∀ (g : ℝ) (h : S → ℝ) (g' : ℝ) (h' : S → ℝ),
        (∀ s, optimalityResidual M g h s = 0) →
          (∀ s, optimalityResidual M g' h' s = 0) → g = g' := by
  refine ⟨aoe_exists M hM, fun g h g' h' h1 h2 => ?_⟩
  classical
  have a := ((bounds_main M g h).2.2 h1 (Classical.arbitrary S)).1
  have b := ((bounds_main M g' h').2.2 h2 (Classical.arbitrary S)).1
  linarith

end MarkovDecisionProcesses

open MarkovDecisionProcesses

theorem solution {S A : Type*} [Fintype S] [Nonempty S]
    [Fintype A] (M : StationaryMDP S A) (hM : IsUnichain M) :
    (∃ (g : ℝ) (h : S → ℝ), ∀ s, optimalityResidual M g h s = 0) ∧
      ∀ (g : ℝ) (h : S → ℝ) (g' : ℝ) (h' : S → ℝ),
        (∀ s, optimalityResidual M g h s = 0) →
          (∀ s, optimalityResidual M g' h' s = 0) → g = g' := by
  exact aoe_main M hM
