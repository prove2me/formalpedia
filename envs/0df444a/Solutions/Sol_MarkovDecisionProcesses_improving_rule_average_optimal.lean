-- Prove2me | solution 1 for MarkovDecisionProcesses.improving_rule_average_optimal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T00:37:53.338115+00:00
-- url     : https://prove2.me/submissions/8be5a858-f645-4f32-96bf-95f820495068

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

end MarkovDecisionProcesses

open MarkovDecisionProcesses

theorem solution {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]
    (M : StationaryMDP S A) (gstar : ℝ) (hstar : S → ℝ)
    (hB : ∀ s, optimalityResidual M gstar hstar s = 0)
    (d : S → A) (hd : IsImproving M hstar d) :
    IsAverageOptimal (stationaryPolicy M d (fun s => (hd s).1)) := by
  exact improving_main M gstar hstar hB d hd
