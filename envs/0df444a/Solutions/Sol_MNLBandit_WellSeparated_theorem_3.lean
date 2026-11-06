-- Prove2me | solution 1 for MNLBandit.WellSeparated.theorem_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T04:39:59.833175+00:00
-- url     : https://prove2.me/submissions/4da5fa3f-6dc1-4fc9-87ec-468b5df10a44
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_WellSeparated_Setting
import Theorems.Thm_MNLBandit_WellSeparated_lemma_4_1
import Theorems.Thm_MNLBandit_WellSeparated_lemma_6_2
import Theorems.Thm_MNLBandit_WellSeparated_corollary_C_1
import Theorems.Thm_MNLBandit_WellSeparated_display_C_5

namespace MNLBandit.WellSeparated

open ChoiceCDLP.MNL

theorem m3_rev_bounds {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
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

theorem m3_gap_pos_le {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
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
    have b0 := m3_rev_bounds v r hv hr S0
    have b1 := m3_rev_bounds v r hv hr S1
    constructor
    · exact sub_pos.2 (lt_of_le_of_ne hle hne')
    · rw [hopt] at hle ⊢; linarith
  · exact ⟨one_pos, le_rfl⟩

theorem m3_consts : 0 < C₁ ∧ C₁ ^ 2 ≤ Cmax ∧ C₂ ≤ Cmax ∧ 0 < C₂ := by
  refine ⟨?_, le_max_left _ _, le_max_right _ _, by norm_num [C₂]⟩
  unfold C₁; positivity

theorem m3_count_none {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs : List (Option (Fin N))) (s : MNLBandit.UCB.AlgState N) :
    (cs.foldl (MNLBandit.UCB.step r sel) s).past.length = s.past.length + cs.count none := by
  induction cs generalizing s with
  | nil => simp
  | cons a cs ih =>
    rw [List.foldl_cons, ih]
    cases a with
    | none => simp [MNLBandit.UCB.step, List.count_cons]; omega
    | some i => simp [MNLBandit.UCB.step, List.count_cons]

theorem m3_epochsDone_eq {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    epochsDone r sel h = (List.ofFn h).count none := by
  unfold epochsDone completedEpochs MNLBandit.UCB.runAlg
  rw [m3_count_none]
  simp [MNLBandit.UCB.initState]

theorem m3_started_le {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    epochsStarted r sel h ≤ T := by
  unfold epochsStarted
  rw [m3_epochsDone_eq]
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

theorem m3_log_le (N T ℓ : ℕ) (hN : 0 < N) (hℓ : ℓ < T) :
    Real.log (Real.sqrt N * ℓ + 1) ≤ Real.log (N * T) := by
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hs : Real.sqrt N ≤ N := (Real.sqrt_le_left (by linarith)).mpr (by nlinarith)
  have hl : (ℓ : ℝ) + 1 ≤ T := by exact_mod_cast hℓ
  apply Real.log_le_log (by positivity)
  have : Real.sqrt N * ℓ ≤ N * ℓ := mul_le_mul_of_nonneg_right hs (by positivity)
  nlinarith

theorem m3_Tcount_step {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
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

theorem m3_sum_snoc {α : Type} [Fintype α] (T : ℕ) (f : (Fin (T+1) → α) → ℝ) :
    ∑ h, f h = ∑ h' : Fin T → α, ∑ o, f (Fin.snoc h' o) := by
  classical
  rw [← (Fin.snocEquiv (fun _ => α)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  rfl

theorem m3_prefix_castSucc {N T : ℕ} (h' : Fin T → Option (Fin N)) (o : Option (Fin N)) (i : Fin T) :
    histPrefix (Fin.snoc h' o : Fin (T+1) → Option (Fin N)) (Fin.castSucc i) = histPrefix h' i := by
  funext u
  simp only [histPrefix]
  have : Fin.castLE (Fin.castSucc i).isLt.le u = Fin.castSucc (Fin.castLE i.isLt.le u) :=
    Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

theorem m3_prefix_last {N T : ℕ} (h' : Fin T → Option (Fin N)) (o : Option (Fin N)) :
    histPrefix (Fin.snoc h' o : Fin (T+1) → Option (Fin N)) (Fin.last T) = h' := by
  funext u
  simp only [histPrefix]
  have : Fin.castLE (Fin.last T).isLt.le u = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

theorem m3_hp_snoc {N : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (T : ℕ) (h' : Fin T → Option (Fin N)) (o : Option (Fin N)) :
    histProb v (alg1 r sel) (T+1) (Fin.snoc h' o) =
      histProb v (alg1 r sel) T h' *
        MNLBandit.UCB.choiceProb v (MNLBandit.UCB.runAlg r sel (List.ofFn h')).cur o := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    rw [Fin.snoc_castSucc]
    congr 2
    exact m3_prefix_castSucc h' o i
  · rw [Fin.snoc_last]
    congr 1
    show (MNLBandit.UCB.runAlg r sel (List.ofFn (histPrefix (Fin.snoc h' o : Fin (T+1) → _) (Fin.last T)))).cur = _
    rw [m3_prefix_last]

theorem m3_choice_sum {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (S : Finset (Fin N)) :
    ∑ o, MNLBandit.UCB.choiceProb v S o = 1 := by
  classical
  rw [Fintype.sum_option]
  simp only [MNLBandit.UCB.choiceProb]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div, ← add_div]
  have : 0 < 1 + ∑ j ∈ S, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => (hv j).1); linarith
  exact div_self this.ne'

theorem m3_choice_nonneg {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (S : Finset (Fin N)) (o : Option (Fin N)) :
    0 ≤ MNLBandit.UCB.choiceProb v S o := by
  have : 0 < 1 + ∑ j ∈ S, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => (hv j).1); linarith
  cases o with
  | none => simp only [MNLBandit.UCB.choiceProb]; positivity
  | some i =>
    simp only [MNLBandit.UCB.choiceProb]
    split_ifs
    · exact div_nonneg (hv i).1 this.le
    · exact le_rfl

theorem m3_hp_nonneg {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ) (h : Fin T → Option (Fin N)) :
    0 ≤ histProb v (alg1 r sel) T h :=
  Finset.prod_nonneg (fun t _ => m3_choice_nonneg v hv _ _)

theorem m3_hp_sum {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ) :
    ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h = 1 := by
  induction T with
  | zero => simp [histProb]
  | succ T ih =>
    rw [m3_sum_snoc]
    simp_rw [m3_hp_snoc, ← Finset.mul_sum, m3_choice_sum v hv, mul_one]
    exact ih

theorem m3_good_zero {N T : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    IsGood v r sel h 0 := by
  intro i
  refine ⟨?_, ?_⟩
  · simp [vUCB, MNLBandit.UCB.vUCBL, MNLBandit.UCB.TcountL]; exact (hv i).2
  · intro h1; simp [Tcount] at h1

theorem m3_Tcount_succ_le {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : Fin T → Option (Fin N)) (i : Fin N) (ℓ : ℕ) :
    Tcount r sel h i (ℓ + 1) ≤ Tcount r sel h i ℓ + 1 := by
  classical
  unfold Tcount
  calc ((Finset.Icc 1 (ℓ + 1)).filter (fun τ => i ∈ epochSet r sel h τ)).card
      ≤ (insert (ℓ + 1) ((Finset.Icc 1 ℓ).filter (fun τ => i ∈ epochSet r sel h τ))).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert] at hx ⊢
        by_cases hx' : x = ℓ + 1
        · exact Or.inl hx'
        · exact Or.inr ⟨⟨hx.1.1, by omega⟩, hx.2⟩
    _ ≤ _ := Finset.card_insert_le _ _

/-- Optimism plus the Lipschitz bound (Lemmas A.3–A.4): if `u ≥ v` and `S` maximizes the
`u`-revenue over the down-closed family, then `(1 + V(S))(R* − R(S)) ≤ ∑_{i∈S} (u_i − v_i)`. -/
theorem m3_epoch_dev {N : ℕ} (v r u : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (h𝒮 : 𝒮.Nonempty) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin N))
    (hmax : ∀ S' ∈ 𝒮, mnlObjective u r 1 S' ≤ mnlObjective u r 1 S)
    (huv : ∀ i, v i ≤ u i) :
    (1 + ∑ j ∈ S, v j) * (MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r S)
      ≤ ∑ i ∈ S, (u i - v i) := by
  classical
  set R := MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 with hRdef
  obtain ⟨Ss, hSs, hSseq⟩ := Finset.exists_mem_eq_sup' h𝒮 (fun S => mnlObjective v r 1 S)
  have hR : R = mnlObjective v r 1 Ss := hSseq
  have hu0 : ∀ i, 0 ≤ u i := fun i => le_trans (hv i).1 (huv i)
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
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => (hv j).1)
  have hdev : (1 + ∑ j ∈ S, v j) * (mnlObjective u r 1 S - revenue v r S)
      ≤ ∑ i ∈ S, (u i - v i) := by
    unfold revenue mnlObjective
    have hU : ∑ j ∈ S, v j ≤ ∑ j ∈ S, u j := Finset.sum_le_sum (fun j _ => huv j)
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
  calc (1 + ∑ j ∈ S, v j) * (R - revenue v r S)
      ≤ (1 + ∑ j ∈ S, v j) * (mnlObjective u r 1 S - revenue v r S) :=
        mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ _ := hdev

/-- `∑_{k ∈ s} 1/√k ≤ 2 √|s|` for a finite set of positive integers. -/
theorem m3_sqrt_sum (s : Finset ℕ) (hs : ∀ k ∈ s, 1 ≤ k) :
    ∑ k ∈ s, 1 / Real.sqrt (k : ℝ) ≤ 2 * Real.sqrt (s.card : ℝ) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [Finset.sum_insert ha, Finset.card_insert_of_notMem ha]
    have ih' := ih (fun k hk => hs k (Finset.mem_insert_of_mem hk))
    have hcard : s.card + 1 ≤ a := by
      have hsub : s ⊆ Finset.Icc 1 (a - 1) := by
        intro x hx
        have h1 := hs x (Finset.mem_insert_of_mem hx)
        have h2 := hlt x hx
        simp only [Finset.mem_Icc]; omega
      have := Finset.card_le_card hsub
      simp at this
      have := hs a (Finset.mem_insert_self a s)
      omega
    set n : ℝ := (s.card : ℝ)
    have hn0 : 0 ≤ n := by positivity
    have han : n + 1 ≤ (a : ℝ) := by
      have : ((s.card + 1 : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast hcard
      push_cast at this; linarith
    have hx : 0 < Real.sqrt (n + 1) := Real.sqrt_pos.2 (by linarith)
    have hxa : Real.sqrt (n + 1) ≤ Real.sqrt a := Real.sqrt_le_sqrt han
    have hstep : 1 / Real.sqrt (a : ℝ) ≤ 1 / Real.sqrt (n + 1) :=
      one_div_le_one_div_of_le hx hxa
    have hxx : Real.sqrt (n + 1) ^ 2 = n + 1 := Real.sq_sqrt (by linarith)
    have hyy : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0
    have hy0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
    have hkey : 1 / Real.sqrt (n + 1) ≤ 2 * (Real.sqrt (n + 1) - Real.sqrt n) := by
      rw [div_le_iff₀ hx]
      nlinarith [sq_nonneg (Real.sqrt (n + 1) - Real.sqrt n)]
    have : ((s.card + 1 : ℕ) : ℝ) = n + 1 := by push_cast; rfl
    rw [this]
    linarith

/-- The per-product deviation of a good epoch, once `T_i ≥ max(1, λ/2)` and `a ≤ λ`. -/
theorem m3_term (vi a lam t : ℝ) (hvi : 0 ≤ vi) (hvi1 : vi ≤ 1) (ha0 : 0 ≤ a) (hal : a ≤ lam)
    (ht : 1 ≤ t) (hlt : lam ≤ 2 * t) :
    C₁ * Real.sqrt (vi * a / t) + C₂ * a / t ≤ (C₁ + 2 * C₂) * Real.sqrt lam * (1 / Real.sqrt t) := by
  obtain ⟨hC1, -, -, hC2⟩ := m3_consts
  have ht0 : 0 < t := by linarith
  have hlam0 : 0 ≤ lam := le_trans ha0 hal
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht0
  have hss : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht0.le
  have hqq : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hlam0
  have hq0 : 0 ≤ Real.sqrt lam := Real.sqrt_nonneg _
  have h1 : Real.sqrt (vi * a / t) ≤ Real.sqrt lam * (1 / Real.sqrt t) := by
    rw [mul_one_div, ← Real.sqrt_div' _ ht0.le]
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_right _ ht0.le
    nlinarith
  have h2 : a / t ≤ 2 * (Real.sqrt lam * (1 / Real.sqrt t)) := by
    have hq2 : Real.sqrt lam ≤ 2 * Real.sqrt t := by
      have : Real.sqrt lam ≤ Real.sqrt (4 * t) := Real.sqrt_le_sqrt (by linarith)
      rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at this
      exact this
    calc a / t ≤ lam / t := div_le_div_of_nonneg_right hal ht0.le
      _ = Real.sqrt lam * Real.sqrt lam / (Real.sqrt t * Real.sqrt t) := by
          rw [← sq, ← sq, hqq, hss]
      _ ≤ 2 * (Real.sqrt lam * (1 / Real.sqrt t)) := by
          rw [div_le_iff₀ (by positivity)]
          field_simp
          nlinarith
  have e : C₂ * a / t = C₂ * (a / t) := by ring
  rw [e]
  have := mul_le_mul_of_nonneg_left h1 hC1.le
  have := mul_le_mul_of_nonneg_left h2 hC2.le
  nlinarith

theorem m3_harmonic (T : ℕ) : ∑ ℓ ∈ Finset.Icc 1 T, (1 : ℝ) / ℓ ≤ 1 + Real.log T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · subst h0; simp
    · have hT : (0 : ℝ) < T := by exact_mod_cast hpos
      have hkey : (1 : ℝ) / ((T + 1 : ℕ) : ℝ) ≤ Real.log ((T + 1 : ℕ) : ℝ) - Real.log T := by
        push_cast
        rw [← Real.log_div (by positivity) hT.ne']
        have h := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < ((T:ℝ) + 1) / T by positivity)
        have e : 1 - (((T:ℝ) + 1) / T)⁻¹ = 1 / ((T:ℝ) + 1) := by
          field_simp
          ring
        linarith
      linarith

theorem m3_started_le_done {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : Fin T → Option (Fin N)) :
    epochsStarted r sel h ≤ epochsDone r sel h + 1 := by
  unfold epochsStarted
  split <;> omega

open Classical in
/-- The pathwise epoch decomposition of the proof of Theorem 3 (pp. 48–50). -/
theorem m3_path (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (hN : 1 ≤ N) (hlam : 2 ≤ Real.log (N * T)) (h : Fin T → Option (Fin N)) :
    ∑ m ∈ Finset.Icc 1 (epochsStarted r sel h),
          (1 + ∑ j ∈ epochSet r sel h m, v j) *
            (MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 - revenue v r (epochSet r sel h m))
      ≤ (N + 1) * (((Finset.Icc 1 T).filter
            (fun ℓ => ℓ ≤ epochsDone r sel h ∧ ¬ IsGood v r sel h ℓ)).card : ℝ)
        + (N + 1) * (N * Real.log (N * T))
        + (C₁ + 2 * C₂) * Real.sqrt (Real.log (N * T)) *
            (N * (2 * Real.sqrt (N * tau N T (gap v r 𝒮 h𝒮)))) := by
  set L := epochsStarted r sel h with hL
  set lam := Real.log (N * T) with hlamdef
  set R := MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 with hRdef
  set c := (C₁ + 2 * C₂) * Real.sqrt lam with hc
  obtain ⟨hC1, -, -, hC2⟩ := m3_consts
  have hc0 : 0 ≤ c := by positivity
  have hLT : L ≤ T := m3_started_le r sel h
  have hLd : L ≤ epochsDone r sel h + 1 := m3_started_le_done r sel h
  have hSmem : ∀ m, epochSet r sel h m ∈ 𝒮 := fun m => (hsel _).1
  have hmax : ∀ m, ∀ S' ∈ 𝒮, mnlObjective (fun j => vUCB r sel h j (m - 1)) r 1 S' ≤
      mnlObjective (fun j => vUCB r sel h j (m - 1)) r 1 (epochSet r sel h m) :=
    fun m => (hsel _).2
  have hRle : ∀ m, revenue v r (epochSet r sel h m) ≤ R := fun m =>
    Finset.le_sup' (fun S => mnlObjective v r 1 S) (hSmem m)
  have hR1 : R < 1 := by
    obtain ⟨S0, -, hS0⟩ := Finset.exists_mem_eq_sup' h𝒮 (fun S => mnlObjective v r 1 S)
    rw [hRdef]; unfold MNLBandit.UCB.optRevenue; rw [hS0]
    exact (m3_rev_bounds v r hv hr S0).2
  have hNR : (0:ℝ) ≤ N := by positivity
  have hDR : ∀ m, (1 + ∑ j ∈ epochSet r sel h m, v j) *
      (R - revenue v r (epochSet r sel h m)) ≤ N + 1 := by
    intro m
    have hV0 : 0 ≤ ∑ j ∈ epochSet r sel h m, v j := Finset.sum_nonneg (fun j _ => (hv j).1)
    have hVN : ∑ j ∈ epochSet r sel h m, v j ≤ N := by
      calc ∑ j ∈ epochSet r sel h m, v j ≤ ∑ _j ∈ epochSet r sel h m, (1:ℝ) :=
            Finset.sum_le_sum (fun j _ => (hv j).2)
        _ = (epochSet r sel h m).card := by simp
        _ ≤ N := by
          have := Finset.card_le_univ (epochSet r sel h m)
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
    have h0 := (m3_rev_bounds v r hv hr (epochSet r sel h m)).1
    have h1 := hRle m
    have : R - revenue v r (epochSet r sel h m) ≤ 1 := by linarith
    nlinarith
  -- the three classes of epochs
  set xi : ℕ → Prop := fun m => ∃ i ∈ epochSet r sel h m, (Tcount r sel h i m : ℝ) < lam with hxi
  set P : ℕ → Prop := fun m => IsGood v r sel h (m - 1) ∧
      revenue v r (epochSet r sel h m) < R ∧ ¬ xi m with hP
  set G := (Finset.Icc 1 L).filter P with hG
  set g : ℕ → ℝ := fun m => ∑ i ∈ epochSet r sel h m,
      c * (1 / Real.sqrt (Tcount r sel h i (m - 1) : ℝ)) with hg
  have hg0 : ∀ m, 0 ≤ g m := fun m => Finset.sum_nonneg (fun i _ => by positivity)
  -- counts in good, sub-optimal, well-sampled epochs
  have hTc : ∀ m, 1 ≤ m → m ≤ L → P m → ∀ i ∈ epochSet r sel h m,
      1 ≤ (Tcount r sel h i (m - 1) : ℝ) ∧ lam ≤ 2 * (Tcount r sel h i (m - 1) : ℝ) := by
    intro m hm1 _ hPm i hi
    have hnx := hPm.2.2
    simp only [hxi, not_exists, not_and, not_lt] at hnx
    have h1 := hnx i hi
    have h2 := m3_Tcount_succ_le r sel h i (m - 1)
    rw [Nat.sub_add_cancel hm1] at h2
    have h3 : (Tcount r sel h i m : ℝ) ≤ (Tcount r sel h i (m - 1) : ℝ) + 1 := by
      exact_mod_cast h2
    constructor <;> linarith
  -- pointwise bound
  have hpt : ∀ m ∈ Finset.Icc 1 L,
      (1 + ∑ j ∈ epochSet r sel h m, v j) * (R - revenue v r (epochSet r sel h m)) ≤
        (N + 1) * (if (2 ≤ m ∧ ¬ IsGood v r sel h (m - 1)) then (1:ℝ) else 0)
        + (N + 1) * (if xi m then (1:ℝ) else 0) + (if P m then g m else 0) := by
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    have hnn1 : 0 ≤ (N + 1 : ℝ) * (if (2 ≤ m ∧ ¬ IsGood v r sel h (m - 1)) then (1:ℝ) else 0) := by
      split_ifs <;> positivity
    have hnn2 : 0 ≤ (N + 1 : ℝ) * (if xi m then (1:ℝ) else 0) := by
      split_ifs <;> positivity
    have hnn3 : 0 ≤ (if P m then g m else 0) := by
      split_ifs
      · exact hg0 m
      · exact le_rfl
    have hb := hDR m
    by_cases hbad : 2 ≤ m ∧ ¬ IsGood v r sel h (m - 1)
    · rw [if_pos hbad]; linarith
    have hgood : IsGood v r sel h (m - 1) := by
      by_cases hm1 : m = 1
      · subst hm1; exact m3_good_zero v r hv sel h
      · by_contra hng; exact hbad ⟨by omega, hng⟩
    by_cases hopt : revenue v r (epochSet r sel h m) = R
    · have h00 : (1 + ∑ j ∈ epochSet r sel h m, v j) * (R - revenue v r (epochSet r sel h m)) = 0 := by
        rw [hopt, sub_self, mul_zero]
      linarith
    by_cases hx : xi m
    · rw [if_pos hx]; linarith
    have hPm : P m := ⟨hgood, lt_of_le_of_ne (hRle m) hopt, hx⟩
    rw [if_pos hPm]
    have hdev := m3_epoch_dev v r (fun j => vUCB r sel h j (m - 1)) 𝒮 h𝒮 hdown hv hr
      (epochSet r sel h m) (hmax m) (fun i => (hgood i).1)
    have hsum : ∑ i ∈ epochSet r sel h m, (vUCB r sel h i (m - 1) - v i) ≤ g m := by
      apply Finset.sum_le_sum
      intro i hi
      obtain ⟨ht1, ht2⟩ := hTc m hm'.1 hm'.2 hPm i hi
      have hgi := (hgood i).2 (by exact_mod_cast ht1)
      refine le_trans hgi ?_
      have hmT : m - 1 < T := by omega
      apply m3_term (v i) _ lam _ (hv i).1 (hv i).2 _ (m3_log_le N T (m - 1) hN hmT) ht1 ht2
      apply Real.log_nonneg
      have : (0:ℝ) ≤ Real.sqrt N * ((m - 1 : ℕ) : ℝ) := by positivity
      linarith
    linarith
  -- sum the pointwise bound
  have hsum1 := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_boole, ← Finset.sum_filter] at hsum1
  -- (a) bad epochs
  have hA : (((Finset.Icc 1 L).filter (fun m => 2 ≤ m ∧ ¬ IsGood v r sel h (m - 1))).card : ℝ) ≤
      (((Finset.Icc 1 T).filter
            (fun ℓ => ℓ ≤ epochsDone r sel h ∧ ¬ IsGood v r sel h ℓ)).card : ℝ) := by
    norm_cast
    apply Finset.card_le_card_of_injOn (fun m => m - 1)
    · intro m hm
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hm ⊢
      exact ⟨⟨by omega, by omega⟩, by omega, hm.2.2⟩
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha hb hab
      omega
  -- (b) under-sampled epochs: Corollary C.1
  have hB : (((Finset.Icc 1 L).filter xi).card : ℝ) ≤ N * lam := by
    have := corollary_C_1 N v r 𝒮 sel hTU hdown hv hr hsel T h
    convert this using 3
  -- (c) good sub-optimal well-sampled epochs: Lemma 6.2 and the √-sum bound
  have hEG := lemma_6_2 N v r 𝒮 h𝒮 sel hTU hdown hv hr hsel T h
  have hGcard : (G.card : ℝ) ≤ N * tau N T (gap v r 𝒮 h𝒮) := by
    refine le_trans ?_ hEG
    norm_cast
    apply Finset.card_le_card_of_injOn (fun m => m - 1)
    · intro m hm
      simp only [hG, hP, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hm
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      refine ⟨by omega, hm.2.1, ?_⟩
      rw [Nat.sub_add_cancel hm.1.1]; exact hm.2.2.1
    · intro a ha b hb hab
      simp only [hG, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at ha hb hab
      omega
  have hC : ∑ m ∈ G, g m ≤ c * (N * (2 * Real.sqrt (N * tau N T (gap v r 𝒮 h𝒮)))) := by
    have e1 : ∑ m ∈ G, g m = ∑ i : Fin N, ∑ m ∈ G.filter (fun m => i ∈ epochSet r sel h m),
        c * (1 / Real.sqrt (Tcount r sel h i (m - 1) : ℝ)) := by
      simp only [hg]
      rw [Finset.sum_comm' (t' := Finset.univ)
        (s' := fun i => G.filter (fun m => i ∈ epochSet r sel h m))]
      intro m i
      simp
    rw [e1]
    have hper : ∀ i : Fin N, ∑ m ∈ G.filter (fun m => i ∈ epochSet r sel h m),
        c * (1 / Real.sqrt (Tcount r sel h i (m - 1) : ℝ)) ≤ c * (2 * Real.sqrt (G.card : ℝ)) := by
      intro i
      set Gi := G.filter (fun m => i ∈ epochSet r sel h m) with hGi
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hc0
      have hinj : ∀ x ∈ Gi, ∀ y ∈ Gi,
          Tcount r sel h i (x - 1) = Tcount r sel h i (y - 1) → x = y := by
        intro x hx y hy hxy
        simp only [hGi, hG, Finset.mem_filter, Finset.mem_Icc] at hx hy
        by_contra hne
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · have := m3_Tcount_step r sel h i (x - 1) x (y - 1) (by omega) (by omega) hx.2
          omega
        · have := m3_Tcount_step r sel h i (y - 1) y (x - 1) (by omega) (by omega) hy.2
          omega
      rw [← Finset.sum_image (f := fun k : ℕ => 1 / Real.sqrt (k : ℝ)) hinj]
      refine le_trans (m3_sqrt_sum _ ?_) ?_
      · intro k hk
        simp only [Finset.mem_image] at hk
        obtain ⟨x, hx, rfl⟩ := hk
        simp only [hGi, hG, Finset.mem_filter, Finset.mem_Icc] at hx
        have := (hTc x hx.1.1.1 hx.1.1.2 hx.1.2 i hx.2).1
        exact_mod_cast this
      · apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.sqrt_le_sqrt
        have : (Gi.image (fun x => Tcount r sel h i (x - 1))).card ≤ G.card :=
          le_trans Finset.card_image_le (Finset.card_filter_le _ _)
        exact_mod_cast this
    calc ∑ i : Fin N, ∑ m ∈ G.filter (fun m => i ∈ epochSet r sel h m),
          c * (1 / Real.sqrt (Tcount r sel h i (m - 1) : ℝ))
        ≤ ∑ _i : Fin N, c * (2 * Real.sqrt (G.card : ℝ)) := Finset.sum_le_sum (fun i _ => hper i)
      _ = N * (c * (2 * Real.sqrt (G.card : ℝ))) := by simp
      _ ≤ N * (c * (2 * Real.sqrt (N * tau N T (gap v r 𝒮 h𝒮)))) := by
          apply mul_le_mul_of_nonneg_left _ hNR
          apply mul_le_mul_of_nonneg_left _ hc0
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact Real.sqrt_le_sqrt hGcard
      _ = c * (N * (2 * Real.sqrt (N * tau N T (gap v r 𝒮 h𝒮)))) := by ring
  have hN1 : (0:ℝ) ≤ N + 1 := by positivity
  have := mul_le_mul_of_nonneg_left hA hN1
  have := mul_le_mul_of_nonneg_left hB hN1
  linarith

theorem m3_probT_union {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ)
    (E : (Fin T → Option (Fin N)) → Prop) (A B : Fin N → (Fin T → Option (Fin N)) → Prop)
    (hE : ∀ h, E h → ∃ i, A i h ∨ B i h) :
    probT v (alg1 r sel) T E ≤
      ∑ i, (probT v (alg1 r sel) T (A i) + probT v (alg1 r sel) T (B i)) := by
  classical
  unfold probT
  have hp := m3_hp_nonneg v r hv sel T
  calc _ ≤ ∑ h : Fin T → Option (Fin N), ∑ i : Fin N,
        ((if A i h then histProb v (alg1 r sel) T h else 0) +
          (if B i h then histProb v (alg1 r sel) T h else 0)) := by
        apply Finset.sum_le_sum
        intro h _
        have hnn : ∀ i ∈ (Finset.univ : Finset (Fin N)), 0 ≤
            ((if A i h then histProb v (alg1 r sel) T h else 0) +
              (if B i h then histProb v (alg1 r sel) T h else 0)) := by
          intro i _
          have := hp h
          split_ifs <;> linarith
        split_ifs with hEh
        · obtain ⟨i, hi⟩ := hE h hEh
          refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ i))
          have := hp h
          rcases hi with hi | hi
          · rw [if_pos hi]; split_ifs <;> linarith
          · rw [if_pos hi]; split_ifs <;> linarith
        · exact Finset.sum_nonneg hnn
    _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_add_distrib]

theorem m3_bad_prob (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T ℓ : ℕ) (hℓ : 1 ≤ ℓ) (hN : 1 ≤ N) :
    probT v (alg1 r sel) T (fun h => ℓ ≤ epochsDone r sel h ∧ ¬ IsGood v r sel h ℓ)
      ≤ 13 / (ℓ : ℝ) := by
  refine le_trans (m3_probT_union v r hv sel T _
    (fun i h => ℓ ≤ epochsDone r sel h ∧ vUCB r sel h i ℓ < v i)
    (fun i h => ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h i ℓ ∧
          C₁ * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
            + C₂ * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ
            < vUCB r sel h i ℓ - v i) ?_) ?_
  · intro h ⟨hd, hng⟩
    unfold IsGood at hng
    push Not at hng
    obtain ⟨i, hi⟩ := hng
    refine ⟨i, ?_⟩
    by_cases h1 : v i ≤ vUCB r sel h i ℓ
    · obtain ⟨a, b⟩ := hi h1
      exact Or.inr ⟨hd, a, b⟩
    · exact Or.inl ⟨hd, lt_of_not_ge h1⟩
  · have hN' : (0:ℝ) < N := by exact_mod_cast hN
    have hℓ' : (0:ℝ) < ℓ := by exact_mod_cast hℓ
    calc _ ≤ ∑ _i : Fin N, (6 / ((N : ℝ) * ℓ) + 7 / ((N : ℝ) * ℓ)) := by
          apply Finset.sum_le_sum
          intro i _
          obtain ⟨a, b⟩ := lemma_4_1 N v r 𝒮 sel hTU hdown hv hr hsel T ℓ hℓ i
          exact add_le_add a b
      _ = 13 / (ℓ : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
          ring

theorem m3_card_exp {N : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (T : ℕ) (E : (Fin T → Option (Fin N)) → ℕ → Prop) [∀ h, DecidablePred (E h)] :
    ∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
        (((Finset.Icc 1 T).filter (fun ℓ => E h ℓ)).card : ℝ)
      = ∑ ℓ ∈ Finset.Icc 1 T, probT v (alg1 r sel) T (fun h => E h ℓ) := by
  unfold probT
  simp_rw [Finset.card_filter]
  push_cast
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  apply Finset.sum_congr rfl
  intro h _
  split_ifs <;> simp_all

open Classical in
theorem m3_expect (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : MNLBandit.UCB.IsTU 𝒮) (hdown : MNLBandit.UCB.DownClosed 𝒮) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (hsel : MNLBandit.UCB.IsArgmaxSel 𝒮 sel)
    (T : ℕ) (hN : 1 ≤ N) (hlam : 2 ≤ Real.log (N * T)) :
    MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤
      (N + 1) * (13 * (1 + Real.log T)) + (N + 1) * (N * Real.log (N * T))
        + (C₁ + 2 * C₂) * Real.sqrt (Real.log (N * T)) *
            (N * (2 * Real.sqrt (N * tau N T (gap v r 𝒮 h𝒮)))) := by
  set D := (N + 1) * (N * Real.log (N * T))
        + (C₁ + 2 * C₂) * Real.sqrt (Real.log (N * T)) *
            (N * (2 * Real.sqrt (N * tau N T (gap v r 𝒮 h𝒮)))) with hD
  refine le_trans (display_C_5 N v r 𝒮 h𝒮 sel hTU hdown hv hr hsel T) ?_
  have hp := m3_hp_nonneg v r hv sel T
  have hstep := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin T → Option (Fin N))))
    (fun h _ => mul_le_mul_of_nonneg_left
      (m3_path N v r 𝒮 h𝒮 sel hTU hdown hv hr hsel T hN hlam h) (hp h))
  refine le_trans hstep ?_
  rw [show (∑ h : Fin T → Option (Fin N), histProb v (alg1 r sel) T h *
      ((N + 1) * (((Finset.Icc 1 T).filter
            (fun ℓ => ℓ ≤ epochsDone r sel h ∧ ¬ IsGood v r sel h ℓ)).card : ℝ)
        + (N + 1) * (N * Real.log (N * T))
        + (C₁ + 2 * C₂) * Real.sqrt (Real.log (N * T)) *
            (N * (2 * Real.sqrt (N * tau N T (gap v r 𝒮 h𝒮))))))
      = ∑ h : Fin T → Option (Fin N), ((N + 1) * (histProb v (alg1 r sel) T h *
          (((Finset.Icc 1 T).filter
            (fun ℓ => ℓ ≤ epochsDone r sel h ∧ ¬ IsGood v r sel h ℓ)).card : ℝ))
        + D * histProb v (alg1 r sel) T h) from
      Finset.sum_congr rfl (fun h _ => by rw [hD]; ring)]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, m3_hp_sum v r hv sel T,
    m3_card_exp v r sel T (fun h ℓ => ℓ ≤ epochsDone r sel h ∧ ¬ IsGood v r sel h ℓ), mul_one]
  have hb : ∑ ℓ ∈ Finset.Icc 1 T, probT v (alg1 r sel) T
      (fun h => ℓ ≤ epochsDone r sel h ∧ ¬ IsGood v r sel h ℓ) ≤ 13 * (1 + Real.log T) := by
    calc _ ≤ ∑ ℓ ∈ Finset.Icc 1 T, 13 * ((1 : ℝ) / ℓ) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          have := m3_bad_prob N v r 𝒮 sel hTU hdown hv hr hsel T ℓ (Finset.mem_Icc.1 hℓ).1 hN
          rw [mul_one_div]; exact this
      _ = 13 * ∑ ℓ ∈ Finset.Icc 1 T, ((1 : ℝ) / ℓ) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (m3_harmonic T) (by norm_num)
  have hN1 : (0:ℝ) ≤ N + 1 := by positivity
  have := mul_le_mul_of_nonneg_left hb hN1
  rw [hD] at *
  linarith

theorem m3_regret_le {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤ T * MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 := by
  unfold MNLBandit.UCB.regret
  have : 0 ≤ MNLBandit.UCB.expectedRevenue v r (alg1 r sel) T := by
    unfold MNLBandit.UCB.expectedRevenue
    apply Finset.sum_nonneg
    intro h _
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun t _ => m3_choice_nonneg v hv _ _)
    · exact Finset.sum_nonneg (fun t _ => (m3_rev_bounds v r hv hr _).1)
  linarith

theorem m3_opt_le {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
    (hv : ∀ i, 0 ≤ v i ∧ v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) :
    MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 ≤ 1 ∧ (N = 0 → MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 = 0) := by
  obtain ⟨S0, -, hS0⟩ := Finset.exists_mem_eq_sup' h𝒮 (fun S => mnlObjective v r 1 S)
  unfold MNLBandit.UCB.optRevenue
  rw [hS0]
  refine ⟨(m3_rev_bounds v r hv hr S0).2.le, ?_⟩
  intro hN
  subst hN
  have : S0 = ∅ := Finset.eq_empty_of_forall_notMem (fun x => Fin.elim0 x)
  subst this
  simp [mnlObjective]

theorem m3_log8 : 2 ≤ Real.log 8 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have h0 := Real.exp_pos 1
  have : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  nlinarith

end MNLBandit.WellSeparated

open MNLBandit.WellSeparated
open ChoiceCDLP.MNL

theorem solution :
    ∃ B₁ B₂ : ℝ, ∀ (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (h𝒮 : 𝒮.Nonempty)
      (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ),
      MNLBandit.UCB.IsTU 𝒮 → MNLBandit.UCB.DownClosed 𝒮 → (∀ i, 0 ≤ v i ∧ v i ≤ 1) → (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      MNLBandit.UCB.IsArgmaxSel 𝒮 sel →
      MNLBandit.UCB.regret v r 𝒮 h𝒮 (alg1 r sel) T ≤
        B₁ * ((N : ℝ) ^ 2 * Real.log T / gap v r 𝒮 h𝒮) + B₂ := by
  obtain ⟨hC1, -, -, hC2⟩ := m3_consts
  set K0 := 4 * (C₁ + 2 * C₂) * Real.sqrt Cmax with hK0
  have hCm : 0 ≤ Cmax := le_trans hC2.le (le_max_right _ _)
  have hK0nn : 0 ≤ K0 := by positivity
  refine ⟨2 * K0 + 100, 8, ?_⟩
  intro N v r 𝒮 h𝒮 sel T hTU hdown hv hr hsel
  obtain ⟨hgp, hg1⟩ := m3_gap_pos_le v r 𝒮 h𝒮 hv hr
  set Δ := gap v r 𝒮 h𝒮 with hΔ
  have hlogT : 0 ≤ Real.log T := Real.log_natCast_nonneg T
  have hX0 : 0 ≤ (N : ℝ) ^ 2 * Real.log T / Δ := by positivity
  have hB1 : 0 ≤ (2 * K0 + 100) * ((N : ℝ) ^ 2 * Real.log T / Δ) := by positivity
  have hreg := m3_regret_le v r 𝒮 h𝒮 sel hv hr T
  obtain ⟨hopt1, hopt0⟩ := m3_opt_le v r 𝒮 h𝒮 hv hr
  have hT0 : (0:ℝ) ≤ T := by positivity
  -- N = 0
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · have := hopt0 hN0
    rw [this, mul_zero] at hreg
    linarith
  -- small horizon
  by_cases hT8 : T < 8
  · have hT8' : (T : ℝ) ≤ 8 := by exact_mod_cast hT8.le
    have : (T : ℝ) * MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 ≤ T := by nlinarith
    linarith
  push Not at hT8
  have hT8' : (8 : ℝ) ≤ T := by exact_mod_cast hT8
  have hlog8T : 2 ≤ Real.log T := le_trans m3_log8 (Real.log_le_log (by norm_num) hT8')
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hNpos
  have hXY : (N : ℝ) ^ 2 * Real.log T ≤ (N : ℝ) ^ 2 * Real.log T / Δ := by
    rw [le_div_iff₀ hgp]
    have : 0 ≤ (N : ℝ) ^ 2 * Real.log T := by positivity
    nlinarith
  by_cases hNT : T < N
  · -- many products: the trivial bound
    have hTN : (T : ℝ) ≤ N := by exact_mod_cast hNT.le
    have : (T : ℝ) * MNLBandit.UCB.optRevenue v r 𝒮 h𝒮 ≤ T := by nlinarith
    have hNN : (N : ℝ) ≤ (N : ℝ) ^ 2 * Real.log T := by nlinarith
    nlinarith
  push Not at hNT
  have hNT' : (N : ℝ) ≤ T := by exact_mod_cast hNT
  have hT0' : (0:ℝ) < T := by linarith
  set lam := Real.log ((N : ℝ) * T) with hlam
  have hlam2 : 2 ≤ lam := le_trans m3_log8 (Real.log_le_log (by norm_num) (by nlinarith))
  have hlamT : lam ≤ 2 * Real.log T := by
    rw [hlam, ← Real.log_rpow hT0', show ((2:ℝ)) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]
    exact Real.log_le_log (by positivity) (by nlinarith)
  have hmain := m3_expect N v r 𝒮 h𝒮 sel hTU hdown hv hr hsel T hNpos hlam2
  -- the √(Nτ) term
  have hsq : Real.sqrt (N * tau N T Δ) = 2 * N * Real.sqrt Cmax * Real.sqrt lam / Δ := by
    have e : (N : ℝ) * tau N T Δ = (2 * N * Real.sqrt Cmax * Real.sqrt lam / Δ) ^ 2 := by
      unfold tau
      rw [div_pow, mul_pow, mul_pow, mul_pow, Real.sq_sqrt hCm, Real.sq_sqrt (by linarith)]
      ring
    rw [e, Real.sqrt_sq (by positivity)]
  rw [hsq] at hmain
  have hthird : (C₁ + 2 * C₂) * Real.sqrt lam * (N * (2 * (2 * N * Real.sqrt Cmax * Real.sqrt lam / Δ)))
      = K0 * ((N : ℝ) ^ 2 * lam / Δ) := by
    have : Real.sqrt lam * Real.sqrt lam = lam := Real.mul_self_sqrt (by linarith)
    calc _ = 4 * (C₁ + 2 * C₂) * Real.sqrt Cmax * ((N : ℝ) ^ 2 * (Real.sqrt lam * Real.sqrt lam) / Δ) := by
          ring
      _ = _ := by rw [this, hK0]
  rw [hthird] at hmain
  -- absorb the constants
  have h1 : ((N : ℝ) + 1) * (13 * (1 + Real.log T)) ≤ 52 * ((N : ℝ) ^ 2 * Real.log T) := by
    have a : (N : ℝ) + 1 ≤ 2 * N ^ 2 := by nlinarith
    have b : 13 * (1 + Real.log T) ≤ 26 * Real.log T := by linarith
    have := mul_le_mul a b (by positivity) (by positivity)
    linarith
  have h2 : ((N : ℝ) + 1) * (N * lam) ≤ 4 * ((N : ℝ) ^ 2 * Real.log T) := by
    have a : ((N : ℝ) + 1) * N ≤ 2 * N ^ 2 := by nlinarith
    have := mul_le_mul a hlamT (by linarith) (by positivity)
    linarith
  have h3 : K0 * ((N : ℝ) ^ 2 * lam / Δ) ≤ 2 * K0 * ((N : ℝ) ^ 2 * Real.log T / Δ) := by
    rw [show 2 * K0 * ((N : ℝ) ^ 2 * Real.log T / Δ) = K0 * (2 * ((N : ℝ) ^ 2 * Real.log T / Δ)) by ring]
    apply mul_le_mul_of_nonneg_left _ hK0nn
    rw [show 2 * ((N : ℝ) ^ 2 * Real.log T / Δ) = (N : ℝ) ^ 2 * (2 * Real.log T) / Δ by ring]
    apply div_le_div_of_nonneg_right _ hgp.le
    exact mul_le_mul_of_nonneg_left hlamT (by positivity)
  linarith
