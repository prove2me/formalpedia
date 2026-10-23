-- Prove2me | solution 1 for MNLBandit.WellSeparated.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:13:28.237003+00:00
-- url     : https://prove2.me/submissions/89430216-d293-490f-85de-8b6f0634ec9e

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

end MNLBandit.WellSeparated

open MNLBandit.WellSeparated
open ChoiceCDLP.MNL

theorem solution (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (h : Fin T → Option (Fin N)) (ℓ : ℕ)
    (hℓ : ℓ < epochsStarted r sel h) (hgood : IsGood v r sel h ℓ)
    (hcount : ∀ i ∈ epochSet r sel h (ℓ + 1),
      1 ≤ Tcount r sel h i ℓ ∧ tau N T (gap v r 𝒮 h𝒮) ≤ Tcount r sel h i ℓ) :
    revenue v r (epochSet r sel h (ℓ + 1)) = MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by
  exact lemma_6_1_core N v r 𝒮 h𝒮 sel hdown hv hr hsel T h ℓ hℓ hgood hcount
