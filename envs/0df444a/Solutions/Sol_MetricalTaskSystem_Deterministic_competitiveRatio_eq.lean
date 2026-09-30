-- Prove2me | solution 1 for MetricalTaskSystem.Deterministic.competitiveRatio_eq
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T23:21:10.515164+00:00
-- url     : https://prove2.me/submissions/d5428526-c935-4dd8-92c0-47fe5a03af5b

import Mathlib
import Definitions.Def_MetricalTaskSystem_Deterministic_Model
import Definitions.Def_MetricalTaskSystem_Deterministic_CruelTaskmaster



namespace MetricalTaskSystem.Deterministic
set_option linter.unusedSectionVars false

section CT
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

noncomputable def ctWf (d : S → S → ℝ) (T : ℕ → S → ℝ) (s₀ : S) : ℕ → S → ℝ
  | 0, s => d s₀ s
  | m + 1, s => Finset.univ.inf' Finset.univ_nonempty (fun t => ctWf d T s₀ m t + T m t + d t s)

theorem ctWf_lip (d : S → S → ℝ) (hd : IsTaskSystem d) (T : ℕ → S → ℝ) (s₀ : S) :
    ∀ m s t, ctWf d T s₀ m s ≤ ctWf d T s₀ m t + d t s
  | 0, s, t => by simp only [ctWf]; exact hd.triangle _ _ _
  | m + 1, s, t => by
    simp only [ctWf]
    obtain ⟨r, -, hr⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S))
      (fun t' => ctWf d T s₀ m t' + T m t' + d t' t)
    rw [hr]
    refine (Finset.inf'_le _ (Finset.mem_univ r)).trans ?_
    linarith [hd.triangle r t s]

theorem ctWf_le (d : S → S → ℝ) (hd : IsTaskSystem d) (T : ℕ → S → ℝ) (s₀ : S) (m : ℕ) (s : S) :
    ctWf d T s₀ (m + 1) s ≤ ctWf d T s₀ m s + T m s := by
  simp only [ctWf]
  refine (Finset.inf'_le _ (Finset.mem_univ s)).trans ?_
  rw [hd.diag]; linarith

theorem ctWf_ge (d : S → S → ℝ) (hd : IsTaskSystem d) (T : ℕ → S → ℝ) (hT : ∀ i s, 0 ≤ T i s)
    (s₀ : S) (m : ℕ) (s : S) :
    ctWf d T s₀ m s ≤ ctWf d T s₀ (m + 1) s := by
  simp only [ctWf]
  apply Finset.le_inf'
  intro t _
  linarith [ctWf_lip d hd T s₀ m s t, hT m t]

theorem ct_schedCost_snoc (d : S → S → ℝ) (T : ℕ → S → ℝ) (m : ℕ) (σ : Fin (m + 1) → S) (t : S) :
    schedCost d (prefixSeq T (m + 1)) (Fin.snoc σ t : Fin (m + 2) → S) =
      schedCost d (prefixSeq T m) σ + (d (σ (Fin.last m)) t + T m t) := by
  unfold schedCost
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    have h1 : (i.castSucc.succ : Fin (m + 2)) = i.succ.castSucc := rfl
    simp only [prefixSeq, Fin.val_castSucc, h1, Fin.snoc_castSucc]
  · have h1 : ((Fin.last m).succ : Fin (m + 2)) = Fin.last (m + 1) := rfl
    have h2 : ((Fin.last m).castSucc : Fin (m + 2)) = (Fin.last m).castSucc := rfl
    simp only [prefixSeq, h1, Fin.snoc_last, Fin.snoc_castSucc, Fin.val_last]

theorem ct_exists_sched (d : S → S → ℝ) (hd : IsTaskSystem d) (T : ℕ → S → ℝ) (s₀ : S) :
    ∀ m s, ∃ σ : Fin (m + 1) → S, σ 0 = s₀ ∧
      schedCost d (prefixSeq T m) σ + d (σ (Fin.last m)) s ≤ ctWf d T s₀ m s
  | 0, s => ⟨fun _ => s₀, rfl, by simp [schedCost, ctWf]⟩
  | m + 1, s => by
    obtain ⟨t, -, ht⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S))
      (fun t' => ctWf d T s₀ m t' + T m t' + d t' s)
    obtain ⟨σ, h0, hσ⟩ := ct_exists_sched d hd T s₀ m t
    refine ⟨Fin.snoc σ t, ?_, ?_⟩
    · have : (0 : Fin (m + 2)) = (0 : Fin (m + 1)).castSucc := rfl
      rw [this, Fin.snoc_castSucc, h0]
    · rw [ct_schedCost_snoc]
      simp only [ctWf, ht, Fin.snoc_last]
      linarith

theorem ct_opt_le (d : S → S → ℝ) (hd : IsTaskSystem d) (T : ℕ → S → ℝ) (s₀ : S) (m : ℕ) (s : S) :
    offlineOpt d s₀ (prefixSeq T m) ≤ ctWf d T s₀ m s := by
  obtain ⟨σ, h0, hσ⟩ := ct_exists_sched d hd T s₀ m s
  have hnn : 0 ≤ d (σ (Fin.last m)) s := by
    by_cases h : σ (Fin.last m) = s
    · rw [h, hd.diag]
    · exact (hd.pos _ _ h).le
  unfold offlineOpt
  refine (Finset.inf'_le (fun σ => schedCost d (prefixSeq T m) σ)
    (b := σ) (by simp [h0])).trans ?_
  linarith

end CT

section Cruel
variable {S : Type} [DecidableEq S]

theorem ct_cruelStates_eq (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) :
    ∀ k, cruelStates A s₀ ε k = (List.range (k + 1)).map (cruelState A s₀ ε)
  | 0 => by simp [cruelStates, cruelState]
  | k + 1 => by
    have h : cruelState A s₀ ε (k + 1) =
        A s₀ ((cruelStates A s₀ ε k).map (elemTask ε)) := by
      simp [cruelState, cruelStates]
    rw [List.range_succ, List.map_append, ← ct_cruelStates_eq A s₀ ε k]
    simp only [List.map_cons, List.map_nil]
    rw [h]
    simp [cruelStates]

theorem ct_cruelState_succ (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) (k : ℕ) :
    cruelState A s₀ ε (k + 1) = A s₀ ((List.range (k + 1)).map (cruelSeq A s₀ ε)) := by
  have h : cruelState A s₀ ε (k + 1) =
      A s₀ ((cruelStates A s₀ ε k).map (elemTask ε)) := by
    simp [cruelState, cruelStates]
  rw [h, ct_cruelStates_eq, List.map_map]
  rfl

theorem ct_take_ofFn (T : ℕ → S → ℝ) (m k : ℕ) (hk : k ≤ m) :
    (List.ofFn (prefixSeq T m)).take k = (List.range k).map T := by
  apply List.ext_getElem
  · simp; omega
  · intro i h1 h2
    simp [prefixSeq]

theorem ct_sched_eq (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) (m : ℕ) (j : Fin (m + 1)) :
    onlineSchedule A s₀ (prefixSeq (cruelSeq A s₀ ε) m) j = cruelState A s₀ ε j := by
  unfold onlineSchedule
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => simp [cruelState, cruelStates]
  | succ k =>
    simp only [Nat.add_one_ne_zero, if_false]
    rw [ct_take_ofFn _ _ _ (by omega), ct_cruelState_succ]

variable [Fintype S]

theorem ct_onlineCost_eq (d : S → S → ℝ) (A : OnlineAlgorithm S) (s₀ : S) (ε : ℝ) (m : ℕ) :
    onlineCost d A s₀ (prefixSeq (cruelSeq A s₀ ε) m) =
      ∑ i ∈ Finset.range m, (d (cruelState A s₀ ε i) (cruelState A s₀ ε (i + 1)) +
        elemTask ε (cruelState A s₀ ε i) (cruelState A s₀ ε (i + 1))) := by
  unfold onlineCost schedCost
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [ct_sched_eq, ct_sched_eq]
  simp [prefixSeq, cruelSeq]


theorem ct_ereal (L : ℝ) (r : ℕ → ℝ) (h : ∀ x < L, ∃ᶠ m in Filter.atTop, x ≤ r m) :
    ((L : ℝ) : EReal) ≤ Filter.limsup (fun m => ((r m : ℝ) : EReal)) Filter.atTop := by
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  induction c using EReal.rec with
  | bot => exact bot_le
  | top => exact absurd hc (not_lt.mpr le_top)
  | coe x =>
    have hx : x < L := EReal.coe_lt_coe_iff.mp hc
    exact Filter.le_limsup_of_frequently_le
      ((h x hx).mono (fun m hm => EReal.coe_le_coe_iff.mpr hm)) (by isBoundedDefault)

theorem ct_final (L κ Φ0 c : ℝ) (cA c₀ : ℕ → ℝ) (hκ : 0 < κ) (hc : 0 < c)
    (h1 : ∀ m, 1 ≤ m → c ≤ c₀ m) (h2 : ∀ m : ℕ, (m : ℝ) * c ≤ cA m)
    (h3 : ∀ m, κ * L * c₀ m - Φ0 ≤ κ * cA m) :
    ∀ x < L, ∃ᶠ m in Filter.atTop, x ≤ cA m / c₀ m := by
  intro x hx
  rw [Filter.frequently_atTop]
  intro N
  set B := max (Φ0 / (κ * (L - x))) 1 with hB
  have hLx : 0 < κ * (L - x) := mul_pos hκ (by linarith)
  by_cases hcase : ∃ m ≥ max N 1, B ≤ c₀ m
  · obtain ⟨m, hm, hBm⟩ := hcase
    refine ⟨m, le_of_max_le_left hm, ?_⟩
    have hm1 : 1 ≤ m := le_of_max_le_right hm
    have hc0 : 0 < c₀ m := lt_of_lt_of_le hc (h1 m hm1)
    rw [le_div_iff₀ hc0]
    have hB1 : Φ0 / (κ * (L - x)) ≤ c₀ m := (le_max_left _ _).trans hBm
    rw [div_le_iff₀ hLx] at hB1
    have := h3 m
    have h4 : κ * (x * c₀ m) ≤ κ * cA m := by nlinarith
    exact le_of_mul_le_mul_left h4 hκ
  · push Not at hcase
    have hB0 : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
    refine ⟨max (max N 1) (⌈|x| * B / c⌉₊), le_max_of_le_left (le_max_left _ _), ?_⟩
    set m := max (max N 1) (⌈|x| * B / c⌉₊) with hmdef
    have hm : m ≥ max N 1 := le_max_left _ _
    have hm1 : 1 ≤ m := le_of_max_le_right hm
    have hc0 : 0 < c₀ m := lt_of_lt_of_le hc (h1 m hm1)
    have hcB := hcase m hm
    rw [le_div_iff₀ hc0]
    have hceil : |x| * B / c ≤ (m : ℝ) := by
      refine (Nat.le_ceil _).trans ?_
      exact_mod_cast le_max_right _ _
    have h5 : |x| * B ≤ (m : ℝ) * c := by
      rw [div_le_iff₀ hc] at hceil; linarith
    have h6 : x * c₀ m ≤ |x| * c₀ m := mul_le_mul_of_nonneg_right (le_abs_self x) hc0.le
    have h7 : |x| * c₀ m ≤ |x| * B := mul_le_mul_of_nonneg_left hcB.le (abs_nonneg x)
    linarith [h2 m]

end Cruel

section Main
variable {S : Type} [Fintype S] [DecidableEq S] [Nontrivial S]

theorem ct_minOff_le (d : S → S → ℝ) (a b : S) (h : a ≠ b) : minOffDiag d ≤ d a b := by
  unfold minOffDiag
  exact Finset.inf'_le (fun p : S × S => d p.1 p.2) (b := (a, b)) (by simpa using h)

theorem ct_minOff_pos (d : S → S → ℝ) (hd : IsTaskSystem d) : 0 < minOffDiag d := by
  unfold minOffDiag
  obtain ⟨p, hp, hpe⟩ := Finset.exists_mem_eq_inf'
    (Finset.filter_nonempty_iff.mpr (by
      obtain ⟨a, b, hab⟩ := exists_pair_ne S
      exact ⟨(a, b), Finset.mem_univ _, hab⟩) : (Finset.univ.filter (fun p : S × S => p.1 ≠ p.2)).Nonempty)
    (fun p : S × S => d p.1 p.2)
  rw [hpe]
  exact hd.pos _ _ (Finset.mem_filter.mp hp).2

theorem ct_pot_step (d : S → S → ℝ) (hd : IsMetrical d) (A : OnlineAlgorithm S) (s₀ : S)
    (ε : ℝ) (hε : 0 < ε) (i : ℕ) :
    let v := ctWf d (cruelSeq A s₀ ε) s₀
    let u := cruelState A s₀ ε
    (2 * ∑ s, v (i + 1) s - v (i + 1) (u (i + 1))) - (2 * ∑ s, v i s - v i (u i)) ≤
      (1 + ε / minOffDiag d) * (d (u i) (u (i + 1)) + elemTask ε (u i) (u (i + 1))) := by
  intro v u
  have hts := hd.1
  have hT : ∀ i s, 0 ≤ cruelSeq A s₀ ε i s := by
    intro i s; simp only [cruelSeq, elemTask]; split_ifs <;> linarith
  have hδ := ct_minOff_pos d hts
  obtain ⟨a, ha⟩ : ∃ a, a = u i := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = u (i + 1) := ⟨_, rfl⟩
  rw [← ha, ← hb]
  have hTa : cruelSeq A s₀ ε i a = ε := by simp [cruelSeq, elemTask, ha, u]
  have hTs : ∀ s, s ≠ a → cruelSeq A s₀ ε i s = 0 := by
    intro s hs; simp [cruelSeq, elemTask, ← ha, u, hs]
  have hsame : ∀ s, s ≠ a → v (i + 1) s = v i s := by
    intro s hs
    apply le_antisymm
    · have := ctWf_le d hts (cruelSeq A s₀ ε) s₀ i s
      rw [hTs s hs] at this; simpa using this
    · exact ctWf_ge d hts _ hT s₀ i s
  have hΔ1 : v (i + 1) a ≤ v i a + ε := by
    have := ctWf_le d hts (cruelSeq A s₀ ε) s₀ i a
    rwa [hTa] at this
  have hΔ0 : v i a ≤ v (i + 1) a := ctWf_ge d hts _ hT s₀ i a
  have hsum : ∑ s, v (i + 1) s - ∑ s, v i s = v (i + 1) a - v i a := by
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single a]
    · intro s _ hs; rw [hsame s hs]; ring
    · intro h; exact absurd (Finset.mem_univ a) h
  have hκ : 1 ≤ 1 + ε / minOffDiag d := by
    have : 0 ≤ ε / minOffDiag d := div_nonneg hε.le hδ.le
    linarith
  by_cases hab : b = a
  · rw [hab, hts.diag]
    simp only [elemTask, if_true, zero_add]
    have : ε ≤ (1 + ε / minOffDiag d) * ε := by nlinarith
    linarith
  · have he : elemTask ε a b = 0 := by simp [elemTask, hab]
    rw [he, add_zero]
    have hvb := hsame b hab
    have hlip := ctWf_lip d hts (cruelSeq A s₀ ε) s₀ (i + 1) a b
    have hsym := hd.2 b a
    have hdab := ct_minOff_le d a b (Ne.symm hab)
    have : ε ≤ ε / minOffDiag d * d a b := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]
      exact mul_le_mul_of_nonneg_left hdab hε.le
    change v (i + 1) a ≤ v (i + 1) b + d b a at hlip
    nlinarith

theorem cruel_core (d : S → S → ℝ) (hd : IsMetrical d) (A : OnlineAlgorithm S) (s₀ : S)
    (ε : ℝ) (hε : 0 < ε) :
    ((((2 * (Fintype.card S : ℝ) - 1) / (1 + ε / minOffDiag d)) : ℝ) : EReal) ≤
      ratioLimsup d A s₀ (cruelSeq A s₀ ε) := by
  have hts := hd.1
  have hδ := ct_minOff_pos d hts
  have hT : ∀ i s, 0 ≤ cruelSeq A s₀ ε i s := by
    intro i s; simp only [cruelSeq, elemTask]; split_ifs <;> linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = 1 + ε / minOffDiag d := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; have := div_pos hε hδ; linarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = min ε (minOffDiag d) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min hε hδ
  let v := ctWf d (cruelSeq A s₀ ε) s₀
  let u := cruelState A s₀ ε
  let Φ : ℕ → ℝ := fun i => 2 * ∑ s, v i s - v i (u i)
  let step : ℕ → ℝ := fun i => d (u i) (u (i + 1)) + elemTask ε (u i) (u (i + 1))
  have hstep : ∀ i, c ≤ step i := by
    intro i
    simp only [step]
    by_cases h : u (i + 1) = u i
    · rw [h, hts.diag]; simp [elemTask, hcdef]
    · have := ct_minOff_le d (u i) (u (i + 1)) (Ne.symm h)
      have h2 : 0 ≤ elemTask ε (u i) (u (i + 1)) := by
        simp only [elemTask]; split_ifs <;> linarith
      rw [hcdef]; exact (min_le_right _ _).trans (by linarith)
  have hcA : ∀ m, onlineCost d A s₀ (prefixSeq (cruelSeq A s₀ ε) m) =
      ∑ i ∈ Finset.range m, step i := fun m => ct_onlineCost_eq d A s₀ ε m
  have htele : ∀ m, Φ m - Φ 0 ≤ κ * ∑ i ∈ Finset.range m, step i := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := ct_pot_step d hd A s₀ ε hε k
      rw [← hκdef] at this
      simp only [Φ, step] at this ih ⊢
      linarith
  have hn : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  have hΦ : ∀ m, (2 * (Fintype.card S : ℝ) - 1) * offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m)
      ≤ Φ m := by
    intro m
    have hle := ct_opt_le d hts (cruelSeq A s₀ ε) s₀ m
    have hsplit := Finset.add_sum_erase Finset.univ (v m) (Finset.mem_univ (u m))
    have hcard : ((Finset.univ.erase (u m)).card : ℝ) = (Fintype.card S : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Nat.cast_sub Fintype.card_pos]
      simp
    have hs2 : ((Finset.univ.erase (u m)).card : ℝ) *
        offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m) ≤ ∑ s ∈ Finset.univ.erase (u m), v m s := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ (fun s _ => hle s)
    rw [hcard] at hs2
    have := hle (u m)
    simp only [Φ]
    rw [← hsplit]
    linarith
  have hc0 : ∀ m, 1 ≤ m → c ≤ offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    unfold offlineOpt
    apply Finset.le_inf'
    intro σ hσ
    have hσ0 : σ 0 = s₀ := (Finset.mem_filter.mp hσ).2
    unfold schedCost
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))), 0 ≤
        d (σ i.castSucc) (σ i.succ) + prefixSeq (cruelSeq A s₀ ε) (k + 1) i (σ i.succ) := by
      intro i _
      have : 0 ≤ d (σ i.castSucc) (σ i.succ) := by
        by_cases h : σ i.castSucc = σ i.succ
        · rw [h, hts.diag]
        · exact (hts.pos _ _ h).le
      exact add_nonneg this (hT i _)
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ 0))
    have h00 : ((0 : Fin (k + 1)).castSucc : Fin (k + 2)) = 0 := rfl
    rw [h00, hσ0]
    simp only [prefixSeq, cruelSeq, Fin.val_zero]
    have hu0 : cruelState A s₀ ε 0 = s₀ := by simp [cruelState, cruelStates]
    rw [hu0]
    by_cases h : σ (0 : Fin (k + 1)).succ = s₀
    · rw [h, hts.diag]; simp [elemTask, hcdef]
    · have := ct_minOff_le d s₀ _ (Ne.symm h)
      have h2 : 0 ≤ elemTask ε s₀ (σ (0 : Fin (k + 1)).succ) := by
        simp only [elemTask]; split_ifs <;> linarith
      rw [hcdef]; exact (min_le_right _ _).trans (by linarith)
  have hL : κ * ((2 * (Fintype.card S : ℝ) - 1) / (1 + ε / minOffDiag d)) =
      2 * (Fintype.card S : ℝ) - 1 := by
    rw [← hκdef]; field_simp
  unfold ratioLimsup
  apply ct_ereal
  apply ct_final _ κ (Φ 0) c _ _ hκ hc hc0
  · intro m
    rw [hcA]
    have : ∑ i ∈ Finset.range m, c ≤ ∑ i ∈ Finset.range m, step i :=
      Finset.sum_le_sum (fun i _ => hstep i)
    simpa using this
  · intro m
    rw [hL, hcA]
    have := hΦ m
    have := htele m
    linarith

theorem cruel_facts (d : S → S → ℝ) (hd : IsMetrical d) (A : OnlineAlgorithm S) (s₀ : S)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ Φ0 c : ℝ, 0 < c ∧ ∀ m : ℕ, (m : ℝ) * c ≤ onlineCost d A s₀ (prefixSeq (cruelSeq A s₀ ε) m) ∧
      (2 * (Fintype.card S : ℝ) - 1) * offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m) - Φ0 ≤
        (1 + ε / minOffDiag d) * onlineCost d A s₀ (prefixSeq (cruelSeq A s₀ ε) m) := by
  have hts := hd.1
  have hδ := ct_minOff_pos d hts
  have hT : ∀ i s, 0 ≤ cruelSeq A s₀ ε i s := by
    intro i s; simp only [cruelSeq, elemTask]; split_ifs <;> linarith
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = 1 + ε / minOffDiag d := ⟨_, rfl⟩
  have hκ : 0 < κ := by rw [hκdef]; have := div_pos hε hδ; linarith
  obtain ⟨c, hcdef⟩ : ∃ c, c = min ε (minOffDiag d) := ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact lt_min hε hδ
  let v := ctWf d (cruelSeq A s₀ ε) s₀
  let u := cruelState A s₀ ε
  let Φ : ℕ → ℝ := fun i => 2 * ∑ s, v i s - v i (u i)
  let step : ℕ → ℝ := fun i => d (u i) (u (i + 1)) + elemTask ε (u i) (u (i + 1))
  have hstep : ∀ i, c ≤ step i := by
    intro i
    simp only [step]
    by_cases h : u (i + 1) = u i
    · rw [h, hts.diag]; simp [elemTask, hcdef]
    · have := ct_minOff_le d (u i) (u (i + 1)) (Ne.symm h)
      have h2 : 0 ≤ elemTask ε (u i) (u (i + 1)) := by
        simp only [elemTask]; split_ifs <;> linarith
      rw [hcdef]; exact (min_le_right _ _).trans (by linarith)
  have hcA : ∀ m, onlineCost d A s₀ (prefixSeq (cruelSeq A s₀ ε) m) =
      ∑ i ∈ Finset.range m, step i := fun m => ct_onlineCost_eq d A s₀ ε m
  have htele : ∀ m, Φ m - Φ 0 ≤ κ * ∑ i ∈ Finset.range m, step i := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := ct_pot_step d hd A s₀ ε hε k
      rw [← hκdef] at this
      simp only [Φ, step] at this ih ⊢
      linarith
  have hn : (1 : ℝ) ≤ Fintype.card S := by
    exact_mod_cast Fintype.card_pos
  have hΦ : ∀ m, (2 * (Fintype.card S : ℝ) - 1) * offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m)
      ≤ Φ m := by
    intro m
    have hle := ct_opt_le d hts (cruelSeq A s₀ ε) s₀ m
    have hsplit := Finset.add_sum_erase Finset.univ (v m) (Finset.mem_univ (u m))
    have hcard : ((Finset.univ.erase (u m)).card : ℝ) = (Fintype.card S : ℝ) - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Nat.cast_sub Fintype.card_pos]
      simp
    have hs2 : ((Finset.univ.erase (u m)).card : ℝ) *
        offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m) ≤ ∑ s ∈ Finset.univ.erase (u m), v m s := by
      rw [← nsmul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ (fun s _ => hle s)
    rw [hcard] at hs2
    have := hle (u m)
    simp only [Φ]
    rw [← hsplit]
    linarith
  have hc0 : ∀ m, 1 ≤ m → c ≤ offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m) := by
    intro m hm
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    unfold offlineOpt
    apply Finset.le_inf'
    intro σ hσ
    have hσ0 : σ 0 = s₀ := (Finset.mem_filter.mp hσ).2
    unfold schedCost
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin (k + 1))), 0 ≤
        d (σ i.castSucc) (σ i.succ) + prefixSeq (cruelSeq A s₀ ε) (k + 1) i (σ i.succ) := by
      intro i _
      have : 0 ≤ d (σ i.castSucc) (σ i.succ) := by
        by_cases h : σ i.castSucc = σ i.succ
        · rw [h, hts.diag]
        · exact (hts.pos _ _ h).le
      exact add_nonneg this (hT i _)
    refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ 0))
    have h00 : ((0 : Fin (k + 1)).castSucc : Fin (k + 2)) = 0 := rfl
    rw [h00, hσ0]
    simp only [prefixSeq, cruelSeq, Fin.val_zero]
    have hu0 : cruelState A s₀ ε 0 = s₀ := by simp [cruelState, cruelStates]
    rw [hu0]
    by_cases h : σ (0 : Fin (k + 1)).succ = s₀
    · rw [h, hts.diag]; simp [elemTask, hcdef]
    · have := ct_minOff_le d s₀ _ (Ne.symm h)
      have h2 : 0 ≤ elemTask ε s₀ (σ (0 : Fin (k + 1)).succ) := by
        simp only [elemTask]; split_ifs <;> linarith
      rw [hcdef]; exact (min_le_right _ _).trans (by linarith)
  refine ⟨Φ 0, c, hc, fun m => ⟨?_, ?_⟩⟩
  · rw [hcA]
    have : ∑ i ∈ Finset.range m, c ≤ ∑ i ∈ Finset.range m, step i :=
      Finset.sum_le_sum (fun i _ => hstep i)
    simpa using this
  · rw [← hκdef, hcA]
    have := hΦ m
    have := htele m
    linarith

end Main

section WFA
variable {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]

noncomputable def wfArgmin (f : S → ℝ) : S :=
  Classical.choose (Finset.univ.exists_min_image f Finset.univ_nonempty)

theorem wfArgmin_le (f : S → ℝ) (y : S) : f (wfArgmin f) ≤ f y :=
  (Classical.choose_spec (Finset.univ.exists_min_image f Finset.univ_nonempty)).2 y
    (Finset.mem_univ y)

noncomputable def wfaState (d : S → S → ℝ) (T : ℕ → S → ℝ) (s₀ : S) : ℕ → S
  | 0 => s₀
  | t + 1 => wfArgmin (fun x => ctWf d T s₀ t x + T t x + d (wfaState d T s₀ t) x)

noncomputable def wfaAlg (d : S → S → ℝ) : OnlineAlgorithm S :=
  fun s₀ l => wfaState d (fun i => l.getD i 0) s₀ l.length

theorem wfa_congr (d : S → S → ℝ) (T T' : ℕ → S → ℝ) (s₀ : S) (j : ℕ)
    (h : ∀ i < j, T i = T' i) :
    ∀ t, t ≤ j → ctWf d T s₀ t = ctWf d T' s₀ t ∧ wfaState d T s₀ t = wfaState d T' s₀ t := by
  intro t
  induction t with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ t ih =>
    intro ht
    obtain ⟨h1, h2⟩ := ih (by omega)
    have h3 := h t (by omega)
    constructor
    · funext s
      simp only [ctWf, h1, h3]
    · simp only [wfaState, h1, h2, h3]

theorem wfa_sched_eq (d : S → S → ℝ) (s₀ : S) (m : ℕ) (T : Fin m → S → ℝ) (j : Fin (m + 1)) :
    onlineSchedule (wfaAlg d) s₀ T j =
      wfaState d (fun i => if h : i < m then T ⟨i, h⟩ else 0) s₀ j := by
  unfold onlineSchedule
  obtain ⟨j, hj⟩ := j
  cases j with
  | zero => simp [wfaState]
  | succ k =>
    simp only [Nat.add_one_ne_zero, if_false, wfaAlg]
    have hlen : ((List.ofFn T).take (k + 1)).length = k + 1 := by simp; omega
    rw [hlen]
    refine (wfa_congr d _ _ s₀ (k + 1) ?_ (k + 1) le_rfl).2
    intro i hi
    funext s
    have him : i < m := by omega
    simp only [him, dif_pos]
    rw [List.getD_eq_getElem _ _ (by rw [hlen]; exact hi)]
    simp

theorem wfa_sched_ge (d : S → S → ℝ) (hd : IsTaskSystem d) (T : ℕ → S → ℝ) (s₀ : S) :
    ∀ m (σ : Fin (m + 1) → S), σ 0 = s₀ →
      ctWf d T s₀ m (σ (Fin.last m)) ≤ schedCost d (prefixSeq T m) σ
  | 0, σ, h0 => by
    have : (Fin.last 0) = 0 := rfl
    simp [ctWf, schedCost, this, h0, hd.diag]
  | m + 1, σ, h0 => by
    have hσ := Fin.snoc_init_self σ
    rw [← hσ, ct_schedCost_snoc, Fin.snoc_last]
    have h0' : Fin.init σ 0 = s₀ := h0
    have ih := wfa_sched_ge d hd T s₀ m (Fin.init σ) h0'
    have h1 := ctWf_le d hd T s₀ m (σ (Fin.last (m + 1)))
    have h2 := ctWf_lip d hd T s₀ m (σ (Fin.last (m + 1))) (Fin.init σ (Fin.last m))
    linarith

theorem wfa_competitive (d : S → S → ℝ) (hd : IsMetrical d) :
    IsCompetitive d (wfaAlg d) (2 * (Fintype.card S : ℝ) - 1) := by
  have hts := hd.1
  have hn : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  have hdnn : ∀ a b, 0 ≤ d a b := by
    intro a b
    by_cases h : a = b
    · rw [h, hts.diag]
    · exact (hts.pos _ _ h).le
  set D : ℝ := ∑ p : S × S, d p.1 p.2 with hD
  have hDle : ∀ a b, d a b ≤ D := by
    intro a b
    exact Finset.single_le_sum (f := fun p : S × S => d p.1 p.2) (fun p _ => hdnn _ _)
      (Finset.mem_univ (a, b))
  refine ⟨by linarith, 2 * Fintype.card S * D, ?_⟩
  intro s₀ m T hT
  set T' : ℕ → S → ℝ := fun i => if h : i < m then T ⟨i, h⟩ else 0 with hT'
  have hT'nn : ∀ i s, 0 ≤ T' i s := by
    intro i s; simp only [hT']; split_ifs
    · exact hT _ _
    · exact le_rfl
  have hpre : prefixSeq T' m = T := by
    funext i s; simp [prefixSeq, hT']
  let v := ctWf d T' s₀
  let u := wfaState d T' s₀
  let Φ : ℕ → ℝ := fun t => 2 * ∑ s, v t s - v t (u t)
  -- step identity
  have hstep : ∀ t, d (u t) (u (t + 1)) + T' t (u (t + 1)) ≤ Φ (t + 1) - Φ t := by
    intro t
    set g : S → ℝ := fun x => v t x + T' t x + d (u t) x with hg
    have hx : u (t + 1) = wfArgmin g := rfl
    have hmin := wfArgmin_le g
    have hv : v (t + 1) (u t) = g (wfArgmin g) := by
      apply le_antisymm
      · show ctWf d T' s₀ (t + 1) (u t) ≤ _
        simp only [ctWf]
        refine (Finset.inf'_le _ (Finset.mem_univ (wfArgmin g))).trans ?_
        simp only [hg]; rw [hd.2]
      · show _ ≤ ctWf d T' s₀ (t + 1) (u t)
        simp only [ctWf]
        apply Finset.le_inf'
        intro r _
        have := hmin r
        simp only [hg] at this ⊢
        rw [hd.2 (u t) r] at this
        exact this
    have hΔ : ∀ s, 0 ≤ v (t + 1) s - v t s := fun s => by
      have := ctWf_ge d hts T' hT'nn s₀ t s; simp only [v]; linarith
    have hA := Finset.single_le_sum (f := fun s => v (t + 1) s - v t s) (fun s _ => hΔ s)
      (Finset.mem_univ (u t))
    have hB := Finset.single_le_sum (f := fun s => v (t + 1) s - v t s) (fun s _ => hΔ s)
      (Finset.mem_univ (u (t + 1)))
    rw [Finset.sum_sub_distrib] at hA hB
    rw [← hx] at hv
    simp only [Φ]
    simp only [hg] at hv
    linarith
  have htele : ∀ k, ∑ i ∈ Finset.range k, (d (u i) (u (i + 1)) + T' i (u (i + 1))) ≤ Φ k - Φ 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ]; linarith [hstep k]
  have hcost : onlineCost d (wfaAlg d) s₀ T =
      ∑ i ∈ Finset.range m, (d (u i) (u (i + 1)) + T' i (u (i + 1))) := by
    unfold onlineCost schedCost
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [wfa_sched_eq, wfa_sched_eq]
    simp [u, hT', T']
  have hΦ0 : 0 ≤ Φ 0 := by
    simp only [Φ, v, u, ctWf, wfaState, hts.diag, sub_zero]
    have := Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) => hdnn s₀ s)
    linarith
  -- offline lower bound
  obtain ⟨σ, hσ, hσe⟩ := Finset.exists_mem_eq_inf'
    (⟨fun _ => s₀, by simp⟩ : (Finset.univ.filter (fun σ : Fin (m + 1) → S => σ 0 = s₀)).Nonempty)
    (fun σ => schedCost d T σ)
  have hopt : offlineOpt d s₀ T = schedCost d T σ := hσe
  have hge := wfa_sched_ge d hts T' s₀ m σ (Finset.mem_filter.mp hσ).2
  rw [hpre, ← hopt] at hge
  have hup : ∀ s, v m s ≤ offlineOpt d s₀ T + D := by
    intro s
    have := ctWf_lip d hts T' s₀ m s (σ (Fin.last m))
    have := hDle (σ (Fin.last m)) s
    simp only [v]; linarith
  have hlo : offlineOpt d s₀ T ≤ v m (u m) := by
    have := ct_opt_le d hts T' s₀ m (u m); rw [hpre] at this; exact this
  have hsum : ∑ s, v m s ≤ Fintype.card S * (offlineOpt d s₀ T + D) := by
    have := Finset.sum_le_sum (fun s (_ : s ∈ Finset.univ) => hup s)
    simpa [mul_add] using this
  rw [hcost]
  have := htele m
  simp only [Φ] at this hΦ0
  nlinarith

end WFA

section Goal
variable {S : Type} [Fintype S] [DecidableEq S]

theorem lower_nontrivial [Nontrivial S] (d : S → S → ℝ) (hd : IsMetrical d)
    (A : OnlineAlgorithm S) (w : ℝ) (hw : IsCompetitive d A w) :
    2 * (Fintype.card S : ℝ) - 1 ≤ w := by
  by_contra hlt
  push Not at hlt
  obtain ⟨hw0, K, hK⟩ := hw
  have hδ := ct_minOff_pos d hd.1
  have hn : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos
  set N : ℝ := 2 * (Fintype.card S : ℝ) - 1 with hN
  -- choose ε with (1 + ε/δ) w < N
  set ε : ℝ := (N - w) / w * minOffDiag d / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]; have : 0 < N - w := by linarith
    positivity
  have hκw : (1 + ε / minOffDiag d) * w < N := by
    have : ε / minOffDiag d = (N - w) / w / 2 := by
      rw [hεdef]; field_simp
    rw [this]
    have : (1 + (N - w) / w / 2) * w = w + (N - w) / 2 := by field_simp
    rw [this]; linarith
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  obtain ⟨Φ0, c, hc, hf⟩ := cruel_facts d hd A s₀ ε hε
  set κ := 1 + ε / minOffDiag d with hκ
  have hκpos : 0 < κ := by have := div_pos hε hδ; linarith
  have hT : ∀ i s, 0 ≤ cruelSeq A s₀ ε i s := by
    intro i s; simp only [cruelSeq, elemTask]; split_ifs <;> linarith
  -- offline cost bounded
  have hB : ∀ m, (N - κ * w) * offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m) ≤ κ * K + Φ0 := by
    intro m
    have h1 := (hf m).2
    have h2 := hK s₀ m (prefixSeq (cruelSeq A s₀ ε) m) (fun i s => hT i s)
    have h3 := mul_le_mul_of_nonneg_left h2 hκpos.le
    nlinarith
  have hpos : 0 < N - κ * w := by linarith
  obtain ⟨m, hm⟩ := exists_nat_gt ((w * ((κ * K + Φ0) / (N - κ * w)) + K) / c)
  have h1 := (hf m).1
  have h2 := hK s₀ m (prefixSeq (cruelSeq A s₀ ε) m) (fun i s => hT i s)
  have h3 : offlineOpt d s₀ (prefixSeq (cruelSeq A s₀ ε) m) ≤ (κ * K + Φ0) / (N - κ * w) := by
    rw [le_div_iff₀ hpos]; linarith [hB m]
  have h4 := mul_le_mul_of_nonneg_left h3 hw0.le
  rw [div_lt_iff₀ hc] at hm
  linarith

theorem lower_single [Nonempty S] [Subsingleton S] (d : S → S → ℝ) (hd : IsMetrical d)
    (A : OnlineAlgorithm S) (w : ℝ) (hw : IsCompetitive d A w) :
    2 * (Fintype.card S : ℝ) - 1 ≤ w := by
  have hcard : Fintype.card S = 1 := Fintype.card_eq_one_iff.mpr
    ⟨Classical.arbitrary S, fun x => Subsingleton.elim _ _⟩
  rw [hcard]
  norm_num
  by_contra hlt
  push Not at hlt
  obtain ⟨hw0, K, hK⟩ := hw
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  have hsc : ∀ m (σ : Fin (m + 1) → S), schedCost d (fun (_ : Fin m) (_ : S) => (1 : ℝ)) σ = m := by
    intro m σ
    unfold schedCost
    have h0 : ∀ x : Fin m, d (σ x.castSucc) (σ x.succ) = 0 := fun x => by
      rw [Subsingleton.elim (σ x.castSucc) (σ x.succ), hd.1.diag]
    simp [h0]
  obtain ⟨m, hm⟩ := exists_nat_gt (K / (1 - w))
  have h := hK s₀ m (fun _ _ => 1) (fun _ _ => zero_le_one)
  unfold onlineCost at h
  rw [hsc] at h
  have hopt : offlineOpt d s₀ (fun (_ : Fin m) (_ : S) => (1 : ℝ)) ≤ m := by
    unfold offlineOpt
    refine (Finset.inf'_le _ (b := fun _ => s₀) (by simp)).trans ?_
    rw [hsc]
  have := mul_le_mul_of_nonneg_left hopt hw0.le
  rw [div_lt_iff₀ (by linarith)] at hm
  nlinarith

theorem competitiveRatio_core [Nonempty S] (d : S → S → ℝ) (hd : IsMetrical d) :
    competitiveRatio d = 2 * (Fintype.card S : ℝ) - 1 := by
  unfold competitiveRatio
  apply IsLeast.csInf_eq
  refine ⟨⟨wfaAlg d, wfa_competitive d hd⟩, ?_⟩
  rintro w ⟨A, hA⟩
  rcases subsingleton_or_nontrivial S with h | h
  · exact lower_single d hd A w hA
  · exact lower_nontrivial d hd A w hA

end Goal

end MetricalTaskSystem.Deterministic

open MetricalTaskSystem.Deterministic


theorem solution {S : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    (d : S → S → ℝ) (hd : IsMetrical d) :
    competitiveRatio d = 2 * (Fintype.card S : ℝ) - 1 := by
  exact competitiveRatio_core d hd
