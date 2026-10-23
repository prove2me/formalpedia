-- Prove2me | solution 1 for MNLBandit.WellSeparated.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:17:05.293528+00:00
-- url     : https://prove2.me/submissions/0f9b3033-4f57-465a-b9eb-5a258b20669a

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting



namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

/-- revenue is at most 1 and nonnegative. -/
theorem g58_rev_bounds {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin N)) :
    0 ≤ revenue v r S ∧ revenue v r S < 1 := by
  unfold revenue mnlObjective
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => (hv j).1)
  have hA : 0 ≤ ∑ j ∈ S, r j * v j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hr j).1 (hv j).1)
  have hAV : ∑ j ∈ S, r j * v j ≤ ∑ j ∈ S, v j :=
    Finset.sum_le_sum (fun j _ => by
      have := (hr j).2; have := (hv j).1; nlinarith)
  refine ⟨div_nonneg hA (by linarith), ?_⟩
  rw [div_lt_one (by linarith)]
  linarith

theorem g58_gap_pos_le {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) :
    0 < gap v r 𝒮 h𝒮 ∧ gap v r 𝒮 h𝒮 ≤ 1 := by
  classical
  unfold gap
  split_ifs with hne
  · obtain ⟨S0, hS0, hS0eq⟩ := Finset.exists_mem_eq_inf' hne
      (fun S => MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r S)
    rw [hS0eq]
    have hmem := Finset.mem_filter.1 hS0
    have hle : revenue v r S0 ≤ MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by
      unfold MNLBandit.UCB.optRevenue
      exact Finset.le_sup' (fun S => mnlObjective v r 1 S) hmem.1
    have hne' := hmem.2
    obtain ⟨S1, hS1, hS1eq⟩ := Finset.exists_mem_eq_sup' h𝒮 (fun S => mnlObjective v r 1 S)
    have hopt : MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 = revenue v r S1 := hS1eq
    have b0 := g58_rev_bounds v r hv hr S0
    have b1 := g58_rev_bounds v r hv hr S1
    constructor
    · exact sub_pos.2 (lt_of_le_of_ne hle hne')
    · rw [hopt] at hle ⊢; linarith
  · exact ⟨one_pos, le_rfl⟩

/-- Optimism plus small UCB excess forces optimality. -/
theorem g58_opt_of_small {N : ℕ} (v r u : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin N)) (hS : S ∈ 𝒮)
    (hmax : ∀ S' ∈ 𝒮, mnlObjective u r 1 S' ≤ mnlObjective u r 1 S)
    (huv : ∀ i, v i ≤ u i)
    (hsum : ∑ i ∈ S, (u i - v i) < gap v r 𝒮 h𝒮 * (1 + ∑ i ∈ S, v i)) :
    revenue v r S = MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by
  classical
  set R := MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 with hRdef
  obtain ⟨Ss, hSs, hSseq⟩ := Finset.exists_mem_eq_sup' h𝒮 (fun S => mnlObjective v r 1 S)
  have hR : R = mnlObjective v r 1 Ss := hSseq
  have hu0 : ∀ i, 0 ≤ u i := fun i => le_trans (hv i).1 (huv i)
  -- optimism
  set S' := Ss.filter (fun i => R ≤ r i) with hS'def
  have hS'mem : S' ∈ 𝒮 := hdown Ss hSs S' (Finset.filter_subset _ _)
  have hopt : R ≤ mnlObjective u r 1 S' := by
    unfold mnlObjective
    have hB : 0 < ∑ j ∈ S', u j + 1 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ S') => hu0 j); linarith
    rw [le_div_iff₀ hB]
    have hVs : 0 < ∑ j ∈ Ss, v j + 1 := by
      have := Finset.sum_nonneg (fun j (_ : j ∈ Ss) => (hv j).1); linarith
    have hReq : R * (∑ j ∈ Ss, v j + 1) = ∑ j ∈ Ss, r j * v j := by
      rw [hR]; unfold mnlObjective; field_simp
    have e1 : ∑ j ∈ S', (r j - R) * v j ≤ ∑ j ∈ S', (r j - R) * u j :=
      Finset.sum_le_sum (fun j hj => by
        have := (Finset.mem_filter.1 hj).2
        exact mul_le_mul_of_nonneg_left (huv j) (by linarith))
    have e2 : ∑ j ∈ Ss, (r j - R) * v j ≤ ∑ j ∈ S', (r j - R) * v j := by
      rw [← Finset.sum_filter_add_sum_filter_not Ss (fun i => R ≤ r i)]
      have : ∑ j ∈ Ss.filter (fun i => ¬ R ≤ r i), (r j - R) * v j ≤ 0 :=
        Finset.sum_nonpos (fun j hj => by
          have := (Finset.mem_filter.1 hj).2
          exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (hv j).1)
      linarith
    have e3 : ∑ j ∈ Ss, (r j - R) * v j = ∑ j ∈ Ss, r j * v j - R * ∑ j ∈ Ss, v j := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    have e4 : ∑ j ∈ S', (r j - R) * u j = ∑ j ∈ S', r j * u j - R * ∑ j ∈ S', u j := by
      simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    have e5 : ∑ j ∈ S', r j * u j = ∑ j ∈ S', u j * r j :=
      Finset.sum_congr rfl (fun j _ => by ring)
    nlinarith
  have hRt : R ≤ mnlObjective u r 1 S := le_trans hopt (hmax S' hS'mem)
  -- deviation
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => (hv j).1)
  have hU : ∑ j ∈ S, v j ≤ ∑ j ∈ S, u j := Finset.sum_le_sum (fun j _ => huv j)
  have hA : 0 ≤ ∑ j ∈ S, u j * r j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hu0 j) (hr j).1)
  have hdev : (1 + ∑ j ∈ S, v j) * (mnlObjective u r 1 S - revenue v r S)
      ≤ ∑ i ∈ S, (u i - v i) := by
    unfold revenue mnlObjective
    have h1 : (1 + ∑ j ∈ S, v j) * ((∑ j ∈ S, r j * u j) / (∑ j ∈ S, u j + 1))
        ≤ ∑ j ∈ S, r j * u j := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]
      have : 0 ≤ ∑ j ∈ S, r j * u j :=
        Finset.sum_nonneg (fun j _ => mul_nonneg (hr j).1 (hu0 j))
      nlinarith
    have h2 : (1 + ∑ j ∈ S, v j) * ((∑ j ∈ S, r j * v j) / (∑ j ∈ S, v j + 1))
        = ∑ j ∈ S, r j * v j := by
      field_simp; ring
    have h3 : ∑ j ∈ S, r j * u j - ∑ j ∈ S, r j * v j ≤ ∑ i ∈ S, (u i - v i) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_le_sum (fun j _ => by
        have := (hr j).2; have := (hr j).1; have := huv j
        nlinarith)
    rw [mul_sub, h2]
    linarith
  have hgp := g58_gap_pos_le v r 𝒮 h𝒮 hv hr
  have hlt : R - revenue v r S < gap v r 𝒮 h𝒮 := by
    by_contra hcon
    push_neg at hcon
    have : (1 + ∑ j ∈ S, v j) * gap v r 𝒮 h𝒮 ≤ (1 + ∑ j ∈ S, v j) * (mnlObjective u r 1 S - revenue v r S) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hle : revenue v r S ≤ R := by
    rw [hRdef]; unfold MNLBandit.UCB.optRevenue
    exact Finset.le_sup' (fun S => mnlObjective v r 1 S) hS
  by_contra hne
  have hgle : gap v r 𝒮 h𝒮 ≤ R - revenue v r S := by
    unfold gap
    have hmem : S ∈ 𝒮.filter (fun S => revenue v r S ≠ MNLBandit.UCB.optRevenue v r 𝒮 h𝒮) :=
      Finset.mem_filter.2 ⟨hS, hne⟩
    rw [dif_pos ⟨S, hmem⟩]
    exact Finset.inf'_le (fun S => MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r S) hmem
  linarith


theorem g58_consts : 0 < C₁ ∧ C₁ ^ 2 ≤ Cmax ∧ C₂ ≤ Cmax ∧ 0 < C₂ := by
  refine ⟨?_, le_max_left _ _, le_max_right _ _, by norm_num [C₂]⟩
  unfold C₁; positivity

theorem g58_term (N : ℕ) (hN : 0 < N) (vi L lam Ti Δ : ℝ) (hvi : 0 ≤ vi) (hL0 : 0 ≤ L)
    (hL : L ≤ lam) (hTi : 1 ≤ Ti) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1)
    (hτ : tau N 0 Δ = tau N 0 Δ → 4 * N * Cmax * lam / Δ ^ 2 / 2 ≤ Ti) :
    C₁ * Real.sqrt (vi * L / Ti) + C₂ * L / Ti ≤ Δ * (vi / 2 + 3 / (4 * N)) := by
  obtain ⟨hC1, hC1sq, hC2, hC2p⟩ := g58_consts
  have hCp : 0 < Cmax := lt_of_lt_of_le hC2p hC2
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hτ' := hτ rfl
  have hk : 2 * N * Cmax * lam ≤ Ti * Δ ^ 2 := by
    rw [div_div, div_le_iff₀ (by positivity)] at hτ'
    linarith
  set q := L / Ti with hq
  have hq0 : 0 ≤ q := div_nonneg hL0 (by linarith)
  have hqk : q * (2 * N * Cmax) ≤ Δ ^ 2 := by
    rw [hq, div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    have : L * (2 * N * Cmax) ≤ lam * (2 * N * Cmax) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    nlinarith
  have hpart2 : C₂ * L / Ti ≤ Δ / (2 * N) := by
    rw [mul_div_assoc, ← hq, le_div_iff₀ (by positivity)]
    have : C₂ * q ≤ Cmax * q := mul_le_mul_of_nonneg_right hC2 hq0
    have hΔ2 : Δ ^ 2 ≤ Δ := by nlinarith
    nlinarith
  have hpart1 : C₁ * Real.sqrt (vi * L / Ti) ≤ Δ * (vi / 2 + 1 / (4 * N)) := by
    rw [mul_div_assoc, ← hq]
    have hy : 0 ≤ Δ * (vi / 2 + 1 / (4 * N)) := by positivity
    rw [show C₁ * Real.sqrt (vi * q) = Real.sqrt (C₁ ^ 2 * (vi * q)) by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hC1.le]]
    apply (Real.sqrt_le_left hy).mpr
    have h1 : C₁ ^ 2 * (vi * q) ≤ Cmax * (vi * q) :=
      mul_le_mul_of_nonneg_right hC1sq (mul_nonneg hvi hq0)
    have h2 : Cmax * (vi * q) * (2 * N) ≤ vi * Δ ^ 2 := by nlinarith
    have h3 : vi * Δ ^ 2 ≤ (Δ * (vi / 2 + 1 / (4 * N))) ^ 2 * (2 * N) := by
      have e : (Δ * (vi / 2 + 1 / (4 * N))) ^ 2 * (2 * N)
          = vi * Δ ^ 2 + Δ ^ 2 * (vi / 2 - 1 / (4 * N)) ^ 2 * (2 * N) := by
        field_simp; ring
      rw [e]
      have : 0 ≤ Δ ^ 2 * (vi / 2 - 1 / (4 * N)) ^ 2 * (2 * N) := by positivity
      linarith
    have h4 : C₁ ^ 2 * (vi * q) * (2 * N) ≤ (Δ * (vi / 2 + 1 / (4 * N))) ^ 2 * (2 * N) := by
      nlinarith
    exact le_of_mul_le_mul_right h4 (by positivity)
  have : Δ * (vi / 2 + 1 / (4 * N)) + Δ / (2 * N) = Δ * (vi / 2 + 3 / (4 * N)) := by
    field_simp; ring
  linarith

theorem g58_count_none {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs : List (Option (Fin N))) (s : MNLBandit.UCB.AlgState N) :
    (cs.foldl (MNLBandit.UCB.step r sel) s).past.length = s.past.length + cs.count none := by
  induction cs generalizing s with
  | nil => simp
  | cons a cs ih =>
    rw [List.foldl_cons, ih]
    cases a with
    | none => simp [MNLBandit.UCB.step, List.count_cons]; omega
    | some i => simp [MNLBandit.UCB.step, List.count_cons]

theorem g58_epochsDone_eq {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    epochsDone r sel h = (List.ofFn h).count none := by
  unfold epochsDone completedEpochs MNLBandit.UCB.runAlg
  rw [g58_count_none]
  simp [MNLBandit.UCB.initState]

theorem g58_started_le {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    epochsStarted r sel h ≤ T := by
  unfold epochsStarted
  rw [g58_epochsDone_eq]
  have hlen : (List.ofFn h).length = T := List.length_ofFn
  generalize List.ofFn h = l at hlen ⊢
  subst hlen
  rcases List.eq_nil_or_concat' l with rfl | ⟨l', a, rfl⟩
  · simp
  · rw [List.getLast?_concat]
    rcases a with _ | a
    · simp [List.count_append]
      exact List.count_le_length
    · simp [List.count_append]
      exact List.count_le_length

theorem g58_log_le (N T ℓ : ℕ) (hN : 0 < N) (hℓ : ℓ < T) :
    Real.log (Real.sqrt N * ℓ + 1) ≤ Real.log (N * T) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt N ≤ N := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hl : (ℓ : ℝ) + 1 ≤ T := by exact_mod_cast hℓ
  apply Real.log_le_log (by positivity)
  have : Real.sqrt N * ℓ ≤ N * ℓ := mul_le_mul_of_nonneg_right hs (by positivity)
  nlinarith

theorem lemma_6_1_gen (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) (ℓ : ℕ)
    (hℓ : ℓ < epochsStarted r sel h) (hgood : IsGood v r sel h ℓ)
    (hcount : ∀ i ∈ epochSet r sel h (ℓ + 1),
      1 ≤ Tcount r sel h i ℓ ∧ tau N T (gap v r 𝒮 h𝒮) / 2 ≤ Tcount r sel h i ℓ) :
    revenue v r (epochSet r sel h (ℓ + 1)) = MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by
  set u : Fin N → ℝ := fun j => vUCB r sel h j ℓ with hu
  set f : Finset (Fin N) → ℝ := fun S => mnlObjective u r 1 S with hf
  have hS : epochSet r sel h (ℓ + 1) = sel f := by
    simp only [epochSet, MNLBandit.UCB.optimisticSet, Nat.add_sub_cancel, hf, hu, vUCB]
  have hT : ℓ < T := lt_of_lt_of_le hℓ (g58_started_le r sel h)
  obtain ⟨hgp, hg1⟩ := g58_gap_pos_le v r 𝒮 h𝒮 hv hr
  rw [hS] at hcount ⊢
  apply g58_opt_of_small v r u 𝒮 h𝒮 hdown hv hr (sel f) (hsel f).1 (hsel f).2
    (fun i => (hgood i).1)
  set S := sel f
  set Δ := gap v r 𝒮 h𝒮
  have hterm : ∀ i ∈ S, u i - v i ≤ Δ * (v i / 2 + 3 / (4 * N)) := by
    intro i hi
    have hN : 0 < N := Fin.pos i
    obtain ⟨c1, c2⟩ := hcount i hi
    have hg := (hgood i).2 c1
    refine le_trans hg ?_
    apply g58_term N hN (v i) _ (Real.log (N * T)) _ Δ (hv i).1 _ (g58_log_le N T ℓ hN hT)
      (by exact_mod_cast c1) hgp hg1
    · intro _; simpa [tau] using c2
    · apply Real.log_nonneg; have : (0:ℝ) ≤ Real.sqrt N * ℓ := by positivity
      linarith
  calc ∑ i ∈ S, (u i - v i) ≤ ∑ i ∈ S, Δ * (v i / 2 + 3 / (4 * N)) := Finset.sum_le_sum hterm
    _ = Δ * ((∑ i ∈ S, v i) / 2 + S.card * (3 / (4 * N))) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
        nsmul_eq_mul]
    _ < Δ * (1 + ∑ i ∈ S, v i) := by
      apply mul_lt_mul_of_pos_left _ hgp
      have hV : 0 ≤ ∑ i ∈ S, v i := Finset.sum_nonneg (fun j _ => (hv j).1)
      have hc : (S.card : ℝ) * (3 / (4 * N)) ≤ 3 / 4 := by
        rcases Nat.eq_zero_or_pos N with h0 | hN
        · subst h0; norm_num
        · have hn : (0 : ℝ) < N := by exact_mod_cast hN
          have : (S.card : ℝ) ≤ N := by
            have := Finset.card_le_univ S
            simp only [Fintype.card_fin] at this
            exact_mod_cast this
          rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
      linarith

theorem lemma_6_1_core (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) (ℓ : ℕ)
    (hℓ : ℓ < epochsStarted r sel h) (hgood : IsGood v r sel h ℓ)
    (hcount : ∀ i ∈ epochSet r sel h (ℓ + 1),
      1 ≤ Tcount r sel h i ℓ ∧ tau N T (gap v r 𝒮 h𝒮) ≤ Tcount r sel h i ℓ) :
    revenue v r (epochSet r sel h (ℓ + 1)) = MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by
  apply lemma_6_1_gen N v r 𝒮 h𝒮 sel hdown hv hr hsel T h ℓ hℓ hgood
  intro i hi
  obtain ⟨c1, c2⟩ := hcount i hi
  refine ⟨c1, ?_⟩
  have : 0 ≤ tau N T (gap v r 𝒮 h𝒮) := by
    have hl : 0 ≤ Real.log (N * T) := by exact_mod_cast Real.log_natCast_nonneg (N * T)
    have := (g58_consts).2.2.1
    have := (g58_consts).2.2.2
    unfold tau; apply div_nonneg _ (sq_nonneg _)
    have : 0 ≤ Cmax := by linarith
    positivity
  linarith


theorem g58_Tcount_step {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : Fin T → Option (Fin N)) (i : Fin N) (ℓ m ℓ' : ℕ) (h1 : ℓ < m) (h2 : m ≤ ℓ')
    (hi : i ∈ epochSet r sel h m) :
    Tcount r sel h i ℓ + 1 ≤ Tcount r sel h i ℓ' := by
  classical
  unfold Tcount
  have hm : m ∉ (Finset.Icc 1 ℓ).filter (fun τ => i ∈ epochSet r sel h τ) := by
    simp only [Finset.mem_filter, Finset.mem_Icc]; omega
  rw [← Finset.card_insert_of_notMem hm]
  convert Finset.card_le_card (s := insert m ((Finset.Icc 1 ℓ).filter (fun τ => i ∈ epochSet r sel h τ)))
    (t := (Finset.Icc 1 ℓ').filter (fun τ => i ∈ epochSet r sel h τ)) ?_
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_Icc] at hx ⊢
  rcases hx with rfl | ⟨⟨a, b⟩, c⟩
  · exact ⟨⟨by omega, h2⟩, hi⟩
  · exact ⟨⟨a, by omega⟩, c⟩


theorem g58_N1 {N : ℕ} (hN : N ≤ 1) (v r u : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin N)) (hS : S ∈ 𝒮)
    (hmax : ∀ S' ∈ 𝒮, mnlObjective u r 1 S' ≤ mnlObjective u r 1 S)
    (huv : ∀ i, v i ≤ u i) :
    revenue v r S = MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by
  classical
  have hsub : Subsingleton (Fin N) := by
    constructor; intro a b; ext; have := a.2; have := b.2; omega
  have huniv : ∀ S' : Finset (Fin N), S' = ∅ ∨ S' = Finset.univ := by
    intro S'
    rcases Finset.eq_empty_or_nonempty S' with h0 | ⟨j, hj⟩
    · exact Or.inl h0
    · right; exact Finset.eq_univ_iff_forall.2 (fun x => by rwa [Subsingleton.elim x j])
  apply le_antisymm
  · unfold MNLBandit.UCB.optRevenue
    exact Finset.le_sup' (fun S => mnlObjective v r 1 S) hS
  · unfold MNLBandit.UCB.optRevenue
    apply Finset.sup'_le
    intro S' hS'
    have b0 := (g58_rev_bounds v r hv hr S).1
    rcases huniv S' with rfl | rfl
    · simp [mnlObjective]; exact b0
    · rcases huniv S with rfl | rfl
      · have hm := hmax _ hS'
        have hz : mnlObjective v r 1 Finset.univ ≤ 0 := by
          simp only [mnlObjective, Finset.sum_empty, zero_add, div_one] at hm ⊢
          have hu0 : ∀ i, 0 ≤ u i := fun i => le_trans (hv i).1 (huv i)
          have hU : 0 < ∑ j, u j + 1 := by
            have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hu0 j); linarith
          have hA : ∑ j, r j * u j ≤ 0 := by
            have := (div_le_iff₀ hU).1 hm; linarith
          have hB : ∑ j, r j * v j ≤ ∑ j, r j * u j :=
            Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (huv j) (hr j).1)
          apply div_nonpos_of_nonpos_of_nonneg (by linarith)
          have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => (hv j).1); linarith
        exact le_trans hz b0
      · exact le_rfl

open Classical in
theorem lemma_6_2_core (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.range (epochsStarted r sel h)).filter (fun ℓ =>
        IsGood v r sel h ℓ ∧
          revenue v r (epochSet r sel h (ℓ + 1)) < MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).card : ℝ)
      ≤ N * tau N T (gap v r 𝒮 h𝒮) := by
  classical
  set Δ := gap v r 𝒮 h𝒮 with hΔ
  set τ := tau N T Δ with hτ
  obtain ⟨hgp, hg1⟩ := g58_gap_pos_le v r 𝒮 h𝒮 hv hr
  obtain ⟨hC1, hC1sq, hC2, hC2p⟩ := g58_consts
  have hτ0 : 0 ≤ τ := by
    have hl : 0 ≤ Real.log (N * T) := by exact_mod_cast Real.log_natCast_nonneg (N * T)
    rw [hτ]; unfold tau; apply div_nonneg _ (sq_nonneg _)
    have : 0 ≤ Cmax := by linarith
    positivity
  set F := (Finset.range (epochsStarted r sel h)).filter (fun ℓ =>
        IsGood v r sel h ℓ ∧
          revenue v r (epochSet r sel h (ℓ + 1)) < MNLBandit.UCB.optRevenue v r 𝒮 h𝒮) with hF
  -- the selected set is argmax of the UCB objective
  have hSel : ∀ ℓ, epochSet r sel h (ℓ + 1) =
      sel (fun S => mnlObjective (fun j => vUCB r sel h j ℓ) r 1 S) := by
    intro ℓ
    simp only [epochSet, MNLBandit.UCB.optimisticSet, Nat.add_sub_cancel, vUCB]
  -- small cases: F empty
  by_cases hsmall : N ≤ 1 ∨ T = 0
  · have : F = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro ℓ hℓ
      simp only [hF, Finset.mem_filter, Finset.mem_range] at hℓ
      obtain ⟨hlt, hgood, hrev⟩ := hℓ
      rcases hsmall with hN1 | hT0
      · have := g58_N1 hN1 v r (fun j => vUCB r sel h j ℓ) 𝒮 h𝒮 hv hr _
          (hsel _).1 (hsel _).2 (fun i => (hgood i).1)
        rw [hSel ℓ] at hrev
        linarith
      · have := g58_started_le r sel h
        omega
    rw [this]; simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  rw [not_or, not_le] at hsmall
  obtain ⟨hN2, hT1⟩ := hsmall
  have hT1' : 1 ≤ T := Nat.one_le_iff_ne_zero.2 hT1
  have hτ1 : 1 ≤ τ := by
    have hNT : (2 : ℝ) ≤ N * T := by
      have : 2 ≤ N * T := by nlinarith
      exact_mod_cast this
    have hl : Real.log 2 ≤ Real.log (N * T) := Real.log_le_log (by norm_num) hNT
    have hl2 := Real.log_two_gt_d9
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    have hC : 144 ≤ Cmax := by have := hC2; simpa [C₂] using this
    rw [hτ]; unfold tau
    rw [le_div_iff₀ (by positivity)]
    have : Δ ^ 2 ≤ 1 := by nlinarith
    have h1 : 4 * 2 * 144 * (0.69 : ℝ) ≤ 4 * N * Cmax * Real.log (N * T) := by
      have a1 : (0:ℝ) ≤ 4 * N := by positivity
      have a2 : 4 * 2 ≤ 4 * (N:ℝ) := by linarith
      have a3 : 4 * 2 * 144 ≤ 4 * (N:ℝ) * Cmax := by nlinarith
      have a4 : (0.69:ℝ) ≤ Real.log (N * T) := by linarith
      nlinarith
    nlinarith
  have hsub : F ⊆ Finset.univ.biUnion (fun i : Fin N =>
      (Finset.range (epochsStarted r sel h)).filter (fun ℓ =>
        i ∈ epochSet r sel h (ℓ + 1) ∧
          (Tcount r sel h i ℓ = 0 ∨ (Tcount r sel h i ℓ : ℝ) < τ / 2))) := by
    intro ℓ hℓ
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hℓ
    obtain ⟨hlt, hgood, hrev⟩ := hℓ
    by_contra hcon
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
      Finset.mem_range, not_exists, not_and, not_or, not_lt] at hcon
    have := lemma_6_1_gen N v r 𝒮 h𝒮 sel hdown hv hr hsel T h ℓ hlt hgood (by
      intro i hi
      obtain ⟨a, b⟩ := hcon i hlt hi
      exact ⟨Nat.one_le_iff_ne_zero.2 a, b⟩)
    linarith
  set M := max 1 ⌈τ / 2⌉₊ with hM
  have hfib : ∀ i : Fin N, ((Finset.range (epochsStarted r sel h)).filter (fun ℓ =>
        i ∈ epochSet r sel h (ℓ + 1) ∧
          (Tcount r sel h i ℓ = 0 ∨ (Tcount r sel h i ℓ : ℝ) < τ / 2))).card ≤
        (Finset.range M).card := by
    intro i
    apply Finset.card_le_card_of_injOn (fun ℓ => Tcount r sel h i ℓ)
    · intro ℓ hℓ
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hℓ
      simp only [Finset.coe_range, Set.mem_Iio, hM]
      rcases hℓ.2.2 with h0 | h0
      · rw [h0]; exact lt_max_of_lt_left one_pos
      · exact lt_max_of_lt_right (Nat.lt_ceil.2 h0)
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
      simp only at hab
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := g58_Tcount_step r sel h i a (a + 1) b (by omega) (by omega) ha.2.1
        omega
      · have := g58_Tcount_step r sel h i b (b + 1) a (by omega) (by omega) hb.2.1
        omega
  have hcard : F.card ≤ N * M := by
    calc F.card ≤ _ := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_biUnion_le
      _ ≤ ∑ _i : Fin N, (Finset.range M).card := Finset.sum_le_sum (fun i _ => hfib i)
      _ = _ := by simp
  have hMτ : (M : ℝ) ≤ τ := by
    rw [hM]; push_cast
    apply max_le hτ1
    by_cases h2 : τ ≤ 2
    · have : ⌈τ / 2⌉₊ ≤ 1 := Nat.ceil_le.2 (by push_cast; linarith)
      have : (⌈τ / 2⌉₊ : ℝ) ≤ 1 := by exact_mod_cast this
      linarith
    · have := Nat.ceil_lt_add_one (show 0 ≤ τ / 2 by linarith)
      linarith
  calc (F.card : ℝ) ≤ ((N * M : ℕ) : ℝ) := by exact_mod_cast hcard
    _ ≤ N * τ := by
      push_cast
      exact mul_le_mul_of_nonneg_left hMτ (by positivity)

end MNLBandit.WellSeparated

open MNLBandit.WellSeparated
open ChoiceCDLP.MNL Classical

theorem solution (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) :
    (((Finset.range (epochsStarted r sel h)).filter (fun ℓ =>
        IsGood v r sel h ℓ ∧
          revenue v r (epochSet r sel h (ℓ + 1)) < MNLBandit.UCB.optRevenue v r 𝒮 h𝒮)).card : ℝ)
      ≤ N * tau N T (gap v r 𝒮 h𝒮) := by
  exact lemma_6_2_core N v r 𝒮 h𝒮 sel hdown hv hr hsel T h
