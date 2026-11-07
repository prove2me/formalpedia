-- Prove2me | solution 1 for MNLBandit.UCB.theorem_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T01:35:49.437486+00:00
-- url     : https://prove2.me/submissions/6babf13f-4a77-4f5c-becb-ea9bc851eed1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1
import Theorems.Thm_MNLBandit_UCB_eq_A_14
import Theorems.Thm_MNLBandit_UCB_lemma_4_1
import Theorems.Thm_MNLBandit_UCB_lemma_A_3
import Theorems.Thm_MNLBandit_UCB_lemma_A_4

namespace MNLT1

open ChoiceCDLP.MNL MNLBandit.UCB

/-! ## Infrastructure on the history law and the run of Algorithm 1 -/

lemma t1_choiceProb_nonneg {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N))
    (a : Option (Fin N)) : 0 ≤ choiceProb v S a := by
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  cases a with
  | none => simp only [choiceProb]; positivity
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv i) (by linarith)
    · exact le_refl _

lemma t1_choiceProb_sum {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    ∑ a, choiceProb v S a = 1 := by
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  rw [Fintype.sum_option]
  simp only [choiceProb]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
  field_simp

lemma t1_histPrefix_snoc_castSucc {N T : ℕ} (h : History N T) (a : Option (Fin N)) (t : Fin T) :
    histPrefix (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) t.castSucc
      = histPrefix h t := by
  funext u
  show (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) (Fin.castLE _ u) = h (Fin.castLE _ u)
  have : (Fin.castLE (t.castSucc).isLt.le u : Fin (T+1)) = Fin.castSucc (Fin.castLE t.isLt.le u) :=
    Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma t1_histPrefix_snoc_last {N T : ℕ} (h : History N T) (a : Option (Fin N)) :
    histPrefix (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) (Fin.last T)
      = h := by
  funext u
  show (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) (Fin.castLE _ u) = h u
  have : (Fin.castLE (Fin.last T).isLt.le u : Fin (T+1)) = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma t1_histProb_snoc {N T : ℕ} (v : Fin N → ℝ) (π : Policy N) (h : History N T)
    (a : Option (Fin N)) :
    histProb v π (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1))
      = histProb v π h * choiceProb v (π T h) a := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t _
    unfold offered
    rw [t1_histPrefix_snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · unfold offered
    rw [t1_histPrefix_snoc_last, Fin.snoc_last]
    rfl

lemma t1_sum_hist_succ {N T : ℕ} (f : History N (T+1) → ℝ) :
    ∑ h, f h = ∑ h : History N T, ∑ a, f (Fin.snoc (α := fun _ => Option (Fin N)) h a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (T+1) => Option (Fin N))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl


lemma t1_histProb_sum {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) :
    ∀ T : ℕ, ∑ h : History N T, histProb v π h = 1 := by
  intro T
  induction T with
  | zero => simp [histProb]
  | succ T ih =>
    rw [t1_sum_hist_succ]
    simp_rw [t1_histProb_snoc, ← Finset.mul_sum, t1_choiceProb_sum v hv, mul_one]
    exact ih

lemma t1_expect_eq {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N)
    (X Y : (t : ℕ) → (Fin t → Option (Fin N)) → Option (Fin N) → ℝ)
    (hXY : ∀ t pre, ∑ a, choiceProb v (π t pre) a * X t pre a
        = ∑ a, choiceProb v (π t pre) a * Y t pre a) :
    ∀ T : ℕ, ∑ h : History N T, histProb v π h * ∑ t : Fin T, X t (histPrefix h t) (h t)
      = ∑ h : History N T, histProb v π h * ∑ t : Fin T, Y t (histPrefix h t) (h t) := by
  have key : ∀ (Z : (t : ℕ) → (Fin t → Option (Fin N)) → Option (Fin N) → ℝ) (T : ℕ),
      ∑ h : History N (T+1), histProb v π h * ∑ t : Fin (T+1), Z t (histPrefix h t) (h t)
      = ∑ h : History N T, histProb v π h * ∑ t : Fin T, Z t (histPrefix h t) (h t)
        + ∑ h : History N T, histProb v π h * ∑ a, choiceProb v (π T h) a * Z T h a := by
    intro Z T
    rw [t1_sum_hist_succ, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro h _
    have e1 : ∀ a, ∑ t : Fin (T+1), Z t (histPrefix (Fin.snoc (α := fun _ => Option (Fin N)) h a :
        History N (T+1)) t) ((Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) t)
        = ∑ t : Fin T, Z t (histPrefix h t) (h t) + Z T h a := by
      intro a
      rw [Fin.sum_univ_castSucc]
      congr 1
      · apply Finset.sum_congr rfl
        intro t _
        rw [t1_histPrefix_snoc_castSucc, Fin.snoc_castSucc]
        rfl
      · rw [t1_histPrefix_snoc_last, Fin.snoc_last]
        rfl
    simp_rw [e1, t1_histProb_snoc]
    have hs := t1_choiceProb_sum v hv (π T h)
    have e2 : ∀ a, histProb v π h * choiceProb v (π T h) a *
          (∑ t : Fin T, Z t (histPrefix h t) (h t) + Z T h a)
        = (histProb v π h * ∑ t : Fin T, Z t (histPrefix h t) (h t)) * choiceProb v (π T h) a
          + histProb v π h * (choiceProb v (π T h) a * Z T h a) := fun a => by ring
    rw [Finset.sum_congr rfl (fun a _ => e2 a), Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, hs, mul_one]
  intro T
  induction T with
  | zero => simp
  | succ T ih => rw [key X, key Y, ih]; congr 1; apply Finset.sum_congr rfl; intro h _; rw [hXY]


lemma t1_fold_prefix {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
    ∀ (ds : List (Option (Fin N))) (s : AlgState N), s.past <+: (ds.foldl (step r sel) s).past := by
  intro ds
  induction ds with
  | nil => intro s; exact List.prefix_refl _
  | cons d ds ih =>
    intro s
    rw [List.foldl_cons]
    refine List.IsPrefix.trans ?_ (ih _)
    cases d with
    | none => exact List.prefix_append _ _
    | some i => exact List.prefix_refl _

lemma t1_fold_cur {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
    ∀ (ds : List (Option (Fin N))) (s : AlgState N), s.cur = optimisticSet r sel s.past →
      (ds.foldl (step r sel) s).cur = optimisticSet r sel (ds.foldl (step r sel) s).past := by
  intro ds
  induction ds with
  | nil => intro s hs; exact hs
  | cons d ds ih =>
    intro s hs
    rw [List.foldl_cons]
    apply ih
    cases d with
    | none => rfl
    | some i => exact hs

lemma t1_fold_len {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
    ∀ (ds : List (Option (Fin N))) (s : AlgState N),
      (ds.foldl (step r sel) s).past.length = s.past.length + ds.count none := by
  intro ds
  induction ds with
  | nil => intro s; simp
  | cons d ds ih =>
    intro s
    rw [List.foldl_cons, ih]
    cases d with
    | none => simp [step]; ring
    | some i => simp [step]

lemma t1_runAlg_cur {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs : List (Option (Fin N))) :
    (runAlg r sel cs).cur = optimisticSet r sel (runAlg r sel cs).past :=
  t1_fold_cur r sel cs _ rfl

lemma t1_runAlg_len {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs : List (Option (Fin N))) :
    (runAlg r sel cs).past.length = cs.count none := by
  unfold runAlg; rw [t1_fold_len]; simp [initState]

lemma t1_runAlg_prefix {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs ds : List (Option (Fin N))) :
    (runAlg r sel cs).past <+: (runAlg r sel (cs ++ ds)).past := by
  unfold runAlg; rw [List.foldl_append]; exact t1_fold_prefix r sel ds _

lemma t1_ofFn_histPrefix {N T : ℕ} (h : History N T) (t : Fin T) :
    List.ofFn (histPrefix h t) = (List.ofFn h).take t := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [histPrefix]

lemma t1_offered_eq {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (t : Fin T) :
    offered (alg1 r sel) h t = nextSet r sel h (((List.ofFn h).take t).count none) := by
  unfold offered alg1 nextSet pastUpTo finalState
  rw [t1_runAlg_cur, t1_ofFn_histPrefix]
  congr 1
  have hp := t1_runAlg_prefix r sel ((List.ofFn h).take t) ((List.ofFn h).drop t)
  rw [List.take_append_drop] at hp
  rw [List.prefix_iff_eq_take.mp hp, t1_runAlg_len]


lemma t1_count_take {N T : ℕ} (h : History N T) :
    ∀ m : ℕ, ((List.ofFn h).take m).count none
      = (Finset.univ.filter (fun u : Fin T => u.val < m ∧ h u = none)).card := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    rw [List.take_add_one, List.count_append, ih]
    by_cases hm : m < T
    · have hg : (List.ofFn h)[m]? = some (h ⟨m, hm⟩) := by simp [hm]
      rw [hg]
      rw [Finset.card_filter, Finset.card_filter]
      have hpt : ∀ u : Fin T, (if u.val < m + 1 ∧ h u = none then 1 else 0)
          = (if u.val < m ∧ h u = none then 1 else 0)
            + (if u = ⟨m, hm⟩ then (if h u = none then 1 else 0) else 0) := by
        intro u
        by_cases h1 : u = ⟨m, hm⟩
        · subst h1; simp
        · have h2 : u.val ≠ m := fun e => h1 (Fin.ext e)
          by_cases h3 : u.val < m
          · simp [h1, h3, show u.val < m + 1 by omega]
          · simp [h1, h3, show ¬ u.val < m + 1 by omega]
      rw [Finset.sum_congr rfl (fun u _ => hpt u), Finset.sum_add_distrib, Finset.sum_ite_eq']
      simp [List.count_singleton]
    · have hg : (List.ofFn h)[m]? = none := by simp; omega
      rw [hg]
      simp only [Option.toList_none, List.count_nil, add_zero]
      congr 1
      apply Finset.filter_congr
      intro u _
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩

lemma t1_count_mono {N T : ℕ} (h : History N T) {m m' : ℕ} (hmm : m ≤ m') :
    ((List.ofFn h).take m).count none ≤ ((List.ofFn h).take m').count none := by
  apply List.IsPrefix.count_le
  have : (List.ofFn h).take m = ((List.ofFn h).take m').take m := by
    rw [List.take_take, min_eq_left hmm]
  rw [this]; exact List.take_prefix _ _

lemma t1_count_succ {N T : ℕ} (h : History N T) (t : Fin T) (ht : h t = none) :
    ((List.ofFn h).take (t.val + 1)).count none = ((List.ofFn h).take t.val).count none + 1 := by
  rw [List.take_add_one, List.count_append]
  have hg : (List.ofFn h)[t.val]? = some (h t) := by simp
  rw [hg, ht]; simp


/-! ## Structural invariant: the recorded assortments are the optimistic sets -/

def Inv {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (s : AlgState N) : Prop :=
  s.cur = optimisticSet r sel s.past ∧
    ∀ k (hk : k < s.past.length), (s.past[k]).1 = optimisticSet r sel (s.past.take k)

lemma inv_step {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (s : AlgState N) (hs : Inv r sel s) (a : Option (Fin N)) : Inv r sel (step r sel s a) := by
  cases a with
  | none =>
    refine ⟨rfl, ?_⟩
    intro k hk
    simp only [step] at hk ⊢
    rw [List.length_append, List.length_singleton] at hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | hk'
    · rw [List.getElem_append_left hk', List.take_append_of_le_length hk'.le]
      exact hs.2 k hk'
    · subst hk'
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      rw [List.take_left' rfl]
      exact hs.1
  | some i => exact hs

lemma inv_fold {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
    ∀ (ds : List (Option (Fin N))) (s : AlgState N), Inv r sel s →
      Inv r sel (ds.foldl (step r sel) s) := by
  intro ds
  induction ds with
  | nil => intro s hs; exact hs
  | cons d ds ih => intro s hs; rw [List.foldl_cons]; exact ih _ (inv_step r sel s hs d)

lemma inv_final {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) : Inv r sel (finalState r sel h) := by
  unfold finalState runAlg
  apply inv_fold
  refine ⟨rfl, ?_⟩
  intro k hk; simp [initState] at hk

lemma TcountL_snoc {N : ℕ} (l : List (EpochRecord N)) (e : EpochRecord N) (i : Fin N) :
    TcountL (l ++ [e]) i = TcountL l i + if i ∈ e.1 then 1 else 0 := by
  unfold TcountL
  rw [List.filter_append, List.length_append]
  by_cases hi : i ∈ e.1 <;> simp [hi]

lemma epochsDone_eq {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) : epochsDone r sel h = (List.ofFn h).count none := by
  unfold epochsDone finalState; exact t1_runAlg_len r sel _

lemma Tcount_succ {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) (hℓ : ℓ < epochsDone r sel h) :
    Tcount r sel h i (ℓ + 1) = Tcount r sel h i ℓ + if i ∈ nextSet r sel h ℓ then 1 else 0 := by
  have hl : ℓ < (finalState r sel h).past.length := hℓ
  have hinv := (inv_final r sel h).2 ℓ hl
  unfold Tcount pastUpTo
  rw [List.take_add_one, List.getElem?_eq_getElem hl, Option.toList_some, TcountL_snoc, hinv]
  rfl

lemma Tcount_eq_card {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) :
    ∀ ℓ, ℓ ≤ epochsDone r sel h →
      Tcount r sel h i ℓ = ((Finset.range ℓ).filter (fun ℓ' => i ∈ nextSet r sel h ℓ')).card := by
  intro ℓ
  induction ℓ with
  | zero => intro _; simp [Tcount, pastUpTo, TcountL]
  | succ ℓ ih =>
    intro hl
    rw [Tcount_succ r sel h i ℓ (by omega), ih (by omega), Finset.range_add_one,
      Finset.filter_insert]
    by_cases hi : i ∈ nextSet r sel h ℓ
    · rw [if_pos hi, if_pos hi, Finset.card_insert_of_notMem (by simp)]
    · rw [if_neg hi, if_neg hi]; simp

lemma epochsStarted_le {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) :
    epochsStarted h ≤ epochsDone r sel h + 1 ∧ epochsStarted h ≤ T := by
  unfold epochsStarted
  split_ifs with hT
  · omega
  · have h1 : (Finset.univ.filter (fun t : Fin T => t.val + 1 < T ∧ h t = none)).card ≤
        epochsDone r sel h := by
      rw [epochsDone_eq]
      have := t1_count_take h T
      rw [List.take_of_length_le (by simp)] at this
      rw [this]
      apply Finset.card_le_card
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
      exact ⟨u.isLt, hu.2⟩
    have h2 : (Finset.univ.filter (fun t : Fin T => t.val + 1 < T ∧ h t = none)).card ≤ T - 1 := by
      have : (Finset.univ.filter (fun t : Fin T => t.val + 1 < T ∧ h t = none)) ⊆
          (Finset.univ.filter (fun t : Fin T => t.val + 1 < T)) := by
        intro u; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact fun h => h.1
      refine (Finset.card_le_card this).trans ?_
      have hT' : T - 1 < T := by omega
      have : (Finset.univ.filter (fun t : Fin T => t.val + 1 < T)) ⊆
          (Finset.univ.erase (⟨T - 1, hT'⟩ : Fin T)) := by
        intro u hu
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
          and_true] at hu ⊢
        intro e; rw [e] at hu; simp at hu; omega
      refine (Finset.card_le_card this).trans (le_of_eq ?_)
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega

/-! ## Counting the epochs: every completed epoch ends at a no-purchase -/

lemma count_step {N T : ℕ} (h : History N T) (m : ℕ) :
    ((List.ofFn h).take (m + 1)).count none = ((List.ofFn h).take m).count none +
      (if hm : m < T then (if h ⟨m, hm⟩ = none then 1 else 0) else 0) := by
  rw [List.take_add_one, List.count_append]
  by_cases hm : m < T
  · have hg : (List.ofFn h)[m]? = some (h ⟨m, hm⟩) := by simp [hm]
    rw [hg, dif_pos hm]
    by_cases hn : h ⟨m, hm⟩ = none
    · rw [hn]; simp
    · rw [if_neg hn]; simp [List.count_singleton, hn]
  · have hg : (List.ofFn h)[m]? = none := by simp; omega
    rw [hg, dif_neg hm]; simp

lemma count_full {N T : ℕ} (h : History N T) (m : ℕ) (hm : T ≤ m) :
    ((List.ofFn h).take m).count none = (List.ofFn h).count none := by
  rw [List.take_of_length_le (by simp; omega)]

lemma surj_epoch {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (ℓ : ℕ) (hℓ : ℓ < epochsDone r sel h) :
    ∃ t : Fin T, h t = none ∧ ((List.ofFn h).take t).count none = ℓ := by
  rw [epochsDone_eq] at hℓ
  set k : ℕ → ℕ := fun m => ((List.ofFn h).take m).count none with hk
  have hex : ∃ m, ℓ < k (m + 1) := ⟨T, by simp only [hk]; rw [count_full h _ (by omega)]; exact hℓ⟩
  classical
  set m0 := Nat.find hex with hm0
  have hspec : ℓ < k (m0 + 1) := Nat.find_spec hex
  have hle : k m0 ≤ ℓ := by
    rcases Nat.eq_zero_or_pos m0 with h0 | hpos
    · rw [h0]; simp [hk]
    · have := Nat.find_min hex (show m0 - 1 < m0 by omega)
      rw [show m0 - 1 + 1 = m0 by omega] at this
      omega
  have hstep := count_step h m0
  by_cases hm : m0 < T
  · rw [dif_pos hm] at hstep
    by_cases hn : h ⟨m0, hm⟩ = none
    · refine ⟨⟨m0, hm⟩, hn, ?_⟩
      rw [if_pos hn] at hstep
      show k m0 = ℓ
      have : k (m0 + 1) = k m0 + 1 := hstep
      omega
    · rw [if_neg hn] at hstep
      have : k (m0 + 1) = k m0 := by simp only [hk]; rw [hstep]; simp
      omega
  · rw [dif_neg hm] at hstep
    have : k (m0 + 1) = k m0 := by simp only [hk]; rw [hstep]; simp
    omega

lemma sum_epochs_le {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (G : ℕ → ℝ) (hG : ∀ ℓ, 0 ≤ G ℓ) :
    ∑ ℓ ∈ Finset.range (epochsDone r sel h), G ℓ ≤
      ∑ t : Fin T, (if h t = none then G (((List.ofFn h).take t).count none) else 0) := by
  rw [← Finset.sum_filter]
  set k : Fin T → ℕ := fun t => ((List.ofFn h).take t).count none with hk
  have hlt : ∀ t t' : Fin T, h t = none → t < t' → k t < k t' := by
    intro t t' ht htt'
    have := t1_count_succ h t ht
    have h2 := t1_count_mono h (show t.val + 1 ≤ t'.val from htt')
    simp only [hk]; omega
  have hinj : Set.InjOn k (Finset.univ.filter (fun t : Fin T => h t = none) : Set (Fin T)) := by
    intro t ht t' ht' e
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ht ht'
    rcases lt_trichotomy t t' with c | c | c
    · exact absurd e (ne_of_lt (hlt t t' ht c))
    · exact c
    · exact absurd e.symm (ne_of_lt (hlt t' t ht' c))
  rw [← Finset.sum_image (f := G) (g := k) hinj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro ℓ hℓ
    rw [Finset.mem_range] at hℓ
    obtain ⟨t, ht, hkt⟩ := surj_epoch r sel h ℓ hℓ
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨t, ht, hkt⟩
  · intro ℓ _ _; exact hG ℓ

lemma V_le {N : ℕ} (v : Fin N → ℝ) (hv1 : ∀ i, v i ≤ 1) (S : Finset (Fin N)) :
    ∑ j ∈ S, v j ≤ N := by
  calc ∑ j ∈ S, v j ≤ ∑ _j ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hv1 j)
    _ = S.card := by simp
    _ ≤ N := by
        have := Finset.card_le_univ S
        rw [Fintype.card_fin] at this
        exact_mod_cast this

/-- (A.20): the expected total "length" `∑_ℓ (1 + V(S_ℓ))` of the started epochs is at most
`T + N + 1`. -/
lemma expect_W {N : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (T : ℕ) :
    ∑ h : History N T, histProb v (alg1 r sel) h *
        ∑ ℓ ∈ Finset.range (epochsStarted h), (1 + ∑ j ∈ nextSet r sel h ℓ, v j)
      ≤ T + (N + 1) := by
  set π := alg1 r sel with hπ
  let X : (t : ℕ) → (Fin t → Option (Fin N)) → Option (Fin N) → ℝ := fun _ _ _ => 1
  let Y : (t : ℕ) → (Fin t → Option (Fin N)) → Option (Fin N) → ℝ :=
    fun t pre a => if a = none then (1 + ∑ j ∈ π t pre, v j) else 0
  have hXY : ∀ t pre, ∑ a, choiceProb v (π t pre) a * X t pre a
      = ∑ a, choiceProb v (π t pre) a * Y t pre a := by
    intro t pre
    have hV : 0 ≤ ∑ j ∈ π t pre, v j := Finset.sum_nonneg (fun j _ => hv0 j)
    simp only [X, mul_one]
    rw [t1_choiceProb_sum v hv0, Fintype.sum_option]
    simp only [Y, if_true, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, add_zero,
      choiceProb]
    field_simp
  have hE := t1_expect_eq v hv0 π X Y hXY T
  have hX : ∑ h : History N T, histProb v π h * ∑ t : Fin T, X t (histPrefix h t) (h t) = T := by
    simp only [X, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    rw [← Finset.sum_mul, t1_histProb_sum v hv0, one_mul]
  have hpath : ∀ h : History N T,
      ∑ ℓ ∈ Finset.range (epochsStarted h), (1 + ∑ j ∈ nextSet r sel h ℓ, v j) ≤
        ∑ t : Fin T, Y t (histPrefix h t) (h t) + (N + 1) := by
    intro h
    have hG : ∀ ℓ, 0 ≤ 1 + ∑ j ∈ nextSet r sel h ℓ, v j := fun ℓ => by
      have := Finset.sum_nonneg (fun j (_ : j ∈ nextSet r sel h ℓ) => hv0 j); linarith
    have h1 := (epochsStarted_le r sel h).1
    calc ∑ ℓ ∈ Finset.range (epochsStarted h), (1 + ∑ j ∈ nextSet r sel h ℓ, v j)
        ≤ ∑ ℓ ∈ Finset.range (epochsDone r sel h + 1), (1 + ∑ j ∈ nextSet r sel h ℓ, v j) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h1)
            (fun ℓ _ _ => hG ℓ)
      _ = ∑ ℓ ∈ Finset.range (epochsDone r sel h), (1 + ∑ j ∈ nextSet r sel h ℓ, v j)
            + (1 + ∑ j ∈ nextSet r sel h (epochsDone r sel h), v j) := Finset.sum_range_succ _ _
      _ ≤ ∑ t : Fin T, Y t (histPrefix h t) (h t) + (N + 1) := by
          apply add_le_add
          · refine (sum_epochs_le r sel h _ hG).trans (le_of_eq ?_)
            apply Finset.sum_congr rfl
            intro t _
            have e : π t (histPrefix h t) = nextSet r sel h (((List.ofFn h).take t).count none) :=
              t1_offered_eq r sel h t
            simp only [Y]
            rw [e]
          · have := V_le v hv1 (nextSet r sel h (epochsDone r sel h)); linarith
  calc _ ≤ ∑ h : History N T, histProb v π h * (∑ t : Fin T, Y t (histPrefix h t) (h t) + (N + 1)) := by
        apply Finset.sum_le_sum; intro h _
        exact mul_le_mul_of_nonneg_left (hpath h)
          (Finset.prod_nonneg (fun t _ => t1_choiceProb_nonneg v hv0 _ _))
    _ = T + (N + 1) := by
        rw [Finset.sum_congr rfl (fun h _ => mul_add _ _ _), Finset.sum_add_distrib,
          ← Finset.sum_mul, t1_histProb_sum v hv0, one_mul, ← hE, hX]

/-! ## Per-epoch regret: the good event and the deterministic bound -/

noncomputable def Bd {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) : ℝ :=
  (Real.sqrt 72 + Real.sqrt 24)
      * Real.sqrt (v i * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ)
    + 144 * Real.log (Real.sqrt N * ℓ + 1) / Tcount r sel h i ℓ

def Good {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (ℓ : ℕ) : Prop :=
  ∀ i, v i ≤ vUCB r sel h i ℓ ∧
    (1 ≤ Tcount r sel h i ℓ → vUCB r sel h i ℓ - v i ≤ Bd v r sel h i ℓ)

noncomputable def Dd {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) : ℝ :=
  if Tcount r sel h i ℓ = 0 then 1 else Bd v r sel h i ℓ

lemma vUCB_of_zero {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (j : Fin N) (ℓ : ℕ)
    (h0 : Tcount r sel h j ℓ = 0) : vUCB r sel h j ℓ = 1 := by
  simp only [vUCB, vUCBL]
  have : TcountL (pastUpTo r sel h ℓ) j = 0 := h0
  simp [this]

lemma log_nonneg' (N ℓ : ℕ) : 0 ≤ Real.log (Real.sqrt N * ℓ + 1) :=
  Real.log_nonneg (by have := Real.sqrt_nonneg (N : ℝ); nlinarith [(Nat.cast_nonneg ℓ : (0:ℝ) ≤ ℓ)])

lemma Bd_nonneg {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) : 0 ≤ Bd v r sel h i ℓ := by
  unfold Bd
  have := log_nonneg' N ℓ
  positivity

lemma Dd_nonneg {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (i : Fin N) (ℓ : ℕ) : 0 ≤ Dd v r sel h i ℓ := by
  unfold Dd; split_ifs
  · norm_num
  · exact Bd_nonneg v r sel h i ℓ

lemma good_zero {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv1 : ∀ i, v i ≤ 1) (h : History N T) : Good v r sel h 0 := by
  have h0 : ∀ i, Tcount r sel h i 0 = 0 := by intro i; simp [Tcount, pastUpTo, TcountL]
  intro i
  refine ⟨by rw [vUCB_of_zero r sel h i 0 (h0 i)]; exact hv1 i, ?_⟩
  intro h1; rw [h0 i] at h1; omega

lemma exists_opt {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N))) (hdc : DownClosed 𝒮)
    (hne : 𝒮.Nonempty) (hv0 : ∀ i, 0 ≤ v i) :
    ∃ Sstar ∈ 𝒮, mnlObjective v r 1 Sstar = optRevenue v r 𝒮 hne ∧ ∀ j ∈ Sstar, 0 < v j := by
  obtain ⟨S0, hS0, heq⟩ := Finset.exists_mem_eq_sup' hne (fun S => mnlObjective v r 1 S)
  classical
  refine ⟨S0.filter (fun j => 0 < v j), hdc S0 hS0 _ (Finset.filter_subset _ _), ?_, ?_⟩
  · unfold optRevenue
    rw [heq]
    unfold mnlObjective
    have e : ∀ g : Fin N → ℝ, (∀ j, ¬ 0 < v j → g j = 0) →
        ∑ j ∈ S0.filter (fun j => 0 < v j), g j = ∑ j ∈ S0, g j := by
      intro g hg
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs with hj
      · rfl
      · exact (hg j hj).symm
    have hz : ∀ j, ¬ 0 < v j → v j = 0 := fun j hj => le_antisymm (not_lt.mp hj) (hv0 j)
    rw [e (fun j => r j * v j) (fun j hj => by rw [hz j hj, mul_zero]), e v hz]
  · intro j hj; exact (Finset.mem_filter.mp hj).2

lemma mnl_le_one {N : ℕ} (v r : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (S : Finset (Fin N)) :
    0 ≤ mnlObjective v r 1 S ∧ mnlObjective v r 1 S ≤ 1 := by
  unfold mnlObjective
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv0 j)
  have hnum0 : 0 ≤ ∑ j ∈ S, r j * v j :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (hr j).1 (hv0 j))
  have hnum : ∑ j ∈ S, r j * v j ≤ ∑ j ∈ S, v j :=
    Finset.sum_le_sum (fun j _ => by nlinarith [(hr j).1, (hr j).2, hv0 j])
  refine ⟨div_nonneg hnum0 (by linarith), ?_⟩
  rw [div_le_one (by linarith)]; linarith

lemma dR_le {N T : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (h : History N T) (ℓ : ℕ) :
    0 ≤ (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
        (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) ∧
    (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
        (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) ≤ N + 1 := by
  have hmem : nextSet r sel h ℓ ∈ 𝒮 := (hsel _).1
  have hle : mnlObjective v r 1 (nextSet r sel h ℓ) ≤ optRevenue v r 𝒮 hne :=
    Finset.le_sup' (fun S => mnlObjective v r 1 S) hmem
  have hopt1 : optRevenue v r 𝒮 hne ≤ 1 :=
    Finset.sup'_le hne _ (fun S _ => (mnl_le_one v r hv0 hr S).2)
  have h0 := (mnl_le_one v r hv0 hr (nextSet r sel h ℓ)).1
  have hV : 0 ≤ ∑ j ∈ nextSet r sel h ℓ, v j := Finset.sum_nonneg (fun j _ => hv0 j)
  have hVN := V_le v hv1 (nextSet r sel h ℓ)
  constructor
  · apply mul_nonneg <;> linarith
  · calc _ ≤ (1 + (N : ℝ)) * 1 := by
          apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
      _ = N + 1 := by ring

lemma dR_good {N T : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty)
    (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (h : History N T) (ℓ : ℕ) (hg : Good v r sel h ℓ) :
    (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
        (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) ≤
      ∑ i ∈ nextSet r sel h ℓ, Dd v r sel h i ℓ := by
  obtain ⟨Sstar, hSstar, hopt, hpos⟩ := exists_opt v r 𝒮 hdc hne hv0
  set S := nextSet r sel h ℓ with hS
  set u : Fin N → ℝ := fun j => vUCB r sel h j ℓ with hu
  have hopt' : ∀ Q ∈ 𝒮, mnlObjective v r 1 Q ≤ mnlObjective v r 1 Sstar := by
    intro Q hQ; rw [hopt]; exact Finset.le_sup' (fun S => mnlObjective v r 1 S) hQ
  have h1 : mnlObjective v r 1 Sstar ≤ mnlObjective u r 1 Sstar :=
    lemma_A_3 𝒮 hdc r hr v u hv0 (fun j => (hg j).1) Sstar hSstar hopt' hpos
  have h2 : mnlObjective u r 1 Sstar ≤ mnlObjective u r 1 S :=
    (hsel (fun S => mnlObjective (fun i => vUCBL (pastUpTo r sel h ℓ) i) r 1 S)).2 Sstar hSstar
  have hA4 := lemma_A_4 r hr v u S (fun i _ => hv0 i) (fun i _ => (hg i).1)
  have hV : 0 < 1 + ∑ j ∈ S, v j := by
    have := Finset.sum_nonneg (fun j (_ : j ∈ S) => hv0 j); linarith
  have step1 : (1 + ∑ j ∈ S, v j) * (mnlObjective u r 1 S - mnlObjective v r 1 S) ≤
      ∑ j ∈ S, (u j - v j) := by
    have := mul_le_mul_of_nonneg_left hA4 hV.le
    rwa [mul_div_cancel₀ _ hV.ne'] at this
  have step0 : (1 + ∑ j ∈ S, v j) * (optRevenue v r 𝒮 hne - mnlObjective v r 1 S) ≤
      (1 + ∑ j ∈ S, v j) * (mnlObjective u r 1 S - mnlObjective v r 1 S) := by
    apply mul_le_mul_of_nonneg_left _ hV.le; rw [← hopt]; linarith
  refine step0.trans (step1.trans (Finset.sum_le_sum ?_))
  intro i _
  unfold Dd
  split_ifs with h0
  · simp only [hu]; rw [vUCB_of_zero r sel h i ℓ h0]; linarith [hv0 i]
  · exact (hg i).2 (by omega)

end MNLT1

namespace MNLT1Prob
open ChoiceCDLP.MNL MNLBandit.UCB

lemma histProb_nonneg {N T : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N)
    (h : History N T) : 0 ≤ histProb v π h := by
  unfold histProb
  apply Finset.prod_nonneg
  intro t _
  have hden : 0 < 1 + ∑ j ∈ offered π h t, v j :=
    by have := Finset.sum_nonneg (fun j (_ : j ∈ offered π h t) => hv0 j); linarith
  cases h t with
  | none => simp only [choiceProb]; positivity
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv0 i) hden.le
    · exact le_refl 0

lemma probT_mono {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E F : History N T → Prop) (hEF : ∀ h, E h → F h) :
    probT v π T E ≤ probT v π T F := by
  unfold probT
  apply Finset.sum_le_sum
  intro h _
  have := histProb_nonneg v hv0 π h
  by_cases hE : E h
  · rw [if_pos hE, if_pos (hEF h hE)]
  · rw [if_neg hE]; split_ifs <;> linarith

lemma probT_or {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E F : History N T → Prop) :
    probT v π T (fun h => E h ∨ F h) ≤ probT v π T E + probT v π T F := by
  unfold probT
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro h _
  have := histProb_nonneg v hv0 π h
  by_cases hE : E h
  · rw [if_pos (Or.inl hE), if_pos hE]; split_ifs <;> linarith
  · by_cases hF : F h
    · rw [if_pos (Or.inr hF), if_neg hE, if_pos hF]; linarith
    · rw [if_neg (by tauto), if_neg hE, if_neg hF]; simp

lemma sqrt_add_le' (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  have h1 : a + b ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc Real.sqrt (a + b) ≤ Real.sqrt ((Real.sqrt a + Real.sqrt b) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)


open scoped Classical in
lemma probT_exists {N : ℕ} (v : Fin N → ℝ) (hv0 : ∀ i, 0 ≤ v i) (π : Policy N) (T : ℕ)
    (E : Fin N → History N T → Prop) :
    probT v π T (fun h => ∃ j, E j h) ≤ ∑ j, probT v π T (E j) := by
  unfold probT
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro h _
  have hx := histProb_nonneg v hv0 π h
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin N)),
      0 ≤ (if E j h then histProb v π h else 0) := by
    intro j _; split_ifs <;> linarith
  by_cases hE : ∃ j, E j h
  · obtain ⟨j0, hj0⟩ := hE
    rw [if_pos ⟨j0, hj0⟩]
    have := Finset.single_le_sum hnn (Finset.mem_univ j0)
    rw [if_pos hj0] at this
    exact this
  · rw [if_neg hE]; exact Finset.sum_nonneg hnn

lemma sum_const_bound (N ℓ : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    ∑ _j : Fin N, c / (N * ℓ) ≤ c / ℓ := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rcases Nat.eq_zero_or_pos N with h0 | hpos
  · subst h0; simp; positivity
  · have hN : (0 : ℝ) < N := by exact_mod_cast hpos
    rcases Nat.eq_zero_or_pos ℓ with hl | hl
    · subst hl; simp
    · have hl' : (0 : ℝ) < ℓ := by exact_mod_cast hl
      rw [le_div_iff₀ hl']
      field_simp
      exact le_refl _

lemma vUCB_ge_one_of_zero {N T : ℕ} (r : Fin N → ℝ)
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (h : History N T) (j : Fin N) (ℓ : ℕ)
    (h0 : Tcount r sel h j ℓ = 0) : vUCB r sel h j ℓ = 1 := by
  simp only [vUCB, vUCBL]
  have : TcountL (pastUpTo r sel h ℓ) j = 0 := h0
  simp [this]

end MNLT1Prob

namespace MNLT1
open ChoiceCDLP.MNL MNLBandit.UCB MNLT1Prob

/-! ## Probability of the bad event (A.17) and the expected number of bad epochs -/

lemma sum_inv_le (T : ℕ) : ∑ ℓ ∈ Finset.range T, (1 / (ℓ : ℝ)) ≤ 1 + Real.log T := by
  rcases Nat.eq_zero_or_pos T with h0 | hpos
  · subst h0; simp
  · obtain ⟨n, rfl⟩ : ∃ n, T = n + 1 := ⟨T - 1, by omega⟩
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, div_zero, add_zero]
    have hh := harmonic_le_one_add_log n
    have e : ((harmonic n : ℚ) : ℝ) = ∑ ℓ ∈ Finset.range n, (1 / ((ℓ + 1 : ℕ) : ℝ)) := by
      unfold harmonic
      push_cast
      apply Finset.sum_congr rfl; intro i _; rw [one_div]
    have e2 : ∑ ℓ ∈ Finset.range n, (1 / ((ℓ + 1 : ℕ) : ℝ)) =
        ∑ ℓ ∈ Finset.range n, (1 / ((ℓ : ℝ) + 1)) := by
      apply Finset.sum_congr rfl; intro i _; push_cast; rfl
    rw [← e]
    refine hh.trans ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have : Real.log n ≤ Real.log ((n + 1 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hn) (by push_cast; linarith)
      linarith

open scoped Classical in
lemma bad_prob {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T ℓ : ℕ) :
    probT v (alg1 r sel) T (fun h => ℓ ≤ epochsDone r sel h ∧ ¬ Good v r sel h ℓ) ≤ 13 / ℓ := by
  rcases Nat.eq_zero_or_pos ℓ with h0 | hℓ
  · subst h0
    have : probT v (alg1 r sel) T (fun h => 0 ≤ epochsDone r sel h ∧ ¬ Good v r sel h 0) = 0 := by
      unfold probT
      apply Finset.sum_eq_zero
      intro h _
      rw [if_neg (fun hh => hh.2 (good_zero v r sel hv1 h))]
    rw [this]; simp
  set E1 : Fin N → History N T → Prop := fun j h =>
    ℓ ≤ epochsDone r sel h ∧ vUCB r sel h j ℓ < v j with hE1
  set E2 : Fin N → History N T → Prop := fun j h =>
    ℓ ≤ epochsDone r sel h ∧ 1 ≤ Tcount r sel h j ℓ ∧ vUCB r sel h j ℓ - v j > Bd v r sel h j ℓ
    with hE2
  have hsub : ∀ h : History N T, (ℓ ≤ epochsDone r sel h ∧ ¬ Good v r sel h ℓ) →
      (∃ j, E1 j h) ∨ (∃ j, E2 j h) := by
    intro h ⟨hl, hng⟩
    by_contra hall
    simp only [not_or, not_exists, hE1, hE2, not_and, not_lt, gt_iff_lt] at hall
    obtain ⟨h1, h2⟩ := hall
    exact hng (fun i => ⟨h1 i hl, fun hT => h2 i hl hT⟩)
  calc _ ≤ probT v (alg1 r sel) T (fun h => (∃ j, E1 j h) ∨ (∃ j, E2 j h)) :=
        probT_mono v hv0 _ T _ _ hsub
    _ ≤ probT v (alg1 r sel) T (fun h => ∃ j, E1 j h) +
          probT v (alg1 r sel) T (fun h => ∃ j, E2 j h) := probT_or v hv0 _ T _ _
    _ ≤ (∑ j, probT v (alg1 r sel) T (E1 j)) + ∑ j, probT v (alg1 r sel) T (E2 j) :=
        add_le_add (probT_exists v hv0 _ T E1) (probT_exists v hv0 _ T E2)
    _ ≤ (∑ _j : Fin N, (6 : ℝ) / (N * ℓ)) + ∑ _j : Fin N, (7 : ℝ) / (N * ℓ) := by
        apply add_le_add
        · apply Finset.sum_le_sum; intro j _
          exact (lemma_4_1 v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T ℓ hℓ j).1
        · apply Finset.sum_le_sum; intro j _
          exact (lemma_4_1 v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T ℓ hℓ j).2
    _ ≤ 6 / ℓ + 7 / ℓ := add_le_add (sum_const_bound N ℓ 6 (by norm_num))
          (sum_const_bound N ℓ 7 (by norm_num))
    _ = 13 / ℓ := by ring

open scoped Classical in
lemma bad_expect {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (T : ℕ) :
    ∑ h : History N T, histProb v (alg1 r sel) h *
        ∑ ℓ ∈ Finset.range (epochsStarted h), (if Good v r sel h ℓ then (0 : ℝ) else 1)
      ≤ 13 * (1 + Real.log T) := by
  have hpath : ∀ h : History N T,
      ∑ ℓ ∈ Finset.range (epochsStarted h), (if Good v r sel h ℓ then (0 : ℝ) else 1) ≤
        ∑ ℓ ∈ Finset.range T,
          (if ℓ ≤ epochsDone r sel h ∧ ¬ Good v r sel h ℓ then (1 : ℝ) else 0) := by
    intro h
    have hle := epochsStarted_le r sel h
    calc _ = ∑ ℓ ∈ Finset.range (epochsStarted h),
          (if ℓ ≤ epochsDone r sel h ∧ ¬ Good v r sel h ℓ then (1 : ℝ) else 0) := by
          apply Finset.sum_congr rfl
          intro ℓ hℓ
          rw [Finset.mem_range] at hℓ
          have : ℓ ≤ epochsDone r sel h := by omega
          by_cases hg : Good v r sel h ℓ <;> simp [hg, this]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hle.2)
          (fun ℓ _ _ => by split_ifs <;> norm_num)
  calc _ ≤ ∑ h : History N T, histProb v (alg1 r sel) h * ∑ ℓ ∈ Finset.range T,
          (if ℓ ≤ epochsDone r sel h ∧ ¬ Good v r sel h ℓ then (1 : ℝ) else 0) := by
        apply Finset.sum_le_sum; intro h _
        exact mul_le_mul_of_nonneg_left (hpath h) (histProb_nonneg v hv0 _ h)
    _ = ∑ ℓ ∈ Finset.range T,
          probT v (alg1 r sel) T (fun h => ℓ ≤ epochsDone r sel h ∧ ¬ Good v r sel h ℓ) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro ℓ _
        unfold probT
        apply Finset.sum_congr rfl; intro h _
        by_cases hE : ℓ ≤ epochsDone r sel h ∧ ¬ Good v r sel h ℓ
        · rw [if_pos hE, if_pos hE, mul_one]
        · rw [if_neg hE, if_neg hE, mul_zero]
    _ ≤ ∑ ℓ ∈ Finset.range T, 13 * (1 / (ℓ : ℝ)) := by
        apply Finset.sum_le_sum; intro ℓ _
        refine (bad_prob v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T ℓ).trans (le_of_eq ?_)
        ring
    _ ≤ 13 * (1 + Real.log T) := by
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inv_le T) (by norm_num)


/-! ## Summing the confidence widths over epochs (A.19) -/

lemma count_sum (P : ℕ → Prop) [DecidablePred P] (g : ℕ → ℝ) :
    ∀ L, ∑ ℓ ∈ Finset.range L, (if P ℓ then g ((Finset.range ℓ).filter P).card else 0) =
      ∑ k ∈ Finset.range ((Finset.range L).filter P).card, g k := by
  intro L
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih, Finset.range_add_one, Finset.filter_insert]
    by_cases hP : P L
    · rw [if_pos hP, if_pos hP, Finset.card_insert_of_notMem (by simp), Finset.sum_range_succ]
    · rw [if_neg hP, if_neg hP, add_zero]

lemma sum_inv_sqrt_le : ∀ n : ℕ, ∑ k ∈ Finset.range n, (1 / Real.sqrt k) ≤ 2 * Real.sqrt n := by
  have key : ∀ m : ℕ, ∑ k ∈ Finset.range (m + 1), (1 / Real.sqrt k) ≤ 2 * Real.sqrt m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ]
      have hx : 0 < Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_pos.mpr (by positivity)
      have hx2 : Real.sqrt ((m + 1 : ℕ) : ℝ) ^ 2 = (m : ℝ) + 1 := by
        rw [Real.sq_sqrt (by positivity)]; push_cast; ring
      have hy2 : Real.sqrt (m : ℝ) ^ 2 = m := Real.sq_sqrt (by positivity)
      have hy0 := Real.sqrt_nonneg (m : ℝ)
      have hstep : 1 / Real.sqrt ((m + 1 : ℕ) : ℝ) ≤
          2 * Real.sqrt ((m + 1 : ℕ) : ℝ) - 2 * Real.sqrt m := by
        rw [div_le_iff₀ hx]
        nlinarith [sq_nonneg (Real.sqrt ((m + 1 : ℕ) : ℝ) - Real.sqrt m)]
      linarith
  intro n
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine (key m).trans ?_
    have : Real.sqrt m ≤ Real.sqrt ((m + 1 : ℕ) : ℝ) := Real.sqrt_le_sqrt (by push_cast; linarith)
    linarith

/-- The width function: `g(0) = 1` and `g(k) = a √(v Λ / k) + 144 Λ / k`. -/
noncomputable def gW (a vi Λ : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 else a * Real.sqrt (vi * Λ / k) + 144 * Λ / k

lemma sum_gW_le (a vi Λ : ℝ) (ha : 0 ≤ a) (hvi : 0 ≤ vi) (hΛ : 0 ≤ Λ) (n T : ℕ) (hn : n ≤ T) :
    ∑ k ∈ Finset.range n, gW a vi Λ k ≤
      1 + 2 * a * Real.sqrt Λ * Real.sqrt (vi * n) + 144 * Λ * (1 + Real.log T) := by
  have hg : ∀ k : ℕ, gW a vi Λ k = (if k = 0 then 1 else 0) +
      a * Real.sqrt (vi * Λ) * (1 / Real.sqrt k) + 144 * Λ * (1 / (k : ℝ)) := by
    intro k
    unfold gW
    split_ifs with hk
    · subst hk; simp
    · rw [Real.sqrt_div' _ (Nat.cast_nonneg k)]; ring
  simp only [hg, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ k ∈ Finset.range n, (if k = 0 then (1 : ℝ) else 0) ≤ 1 := by
    rw [Finset.sum_ite_eq']; split_ifs <;> norm_num
  have h2 := sum_inv_sqrt_le n
  have h3 := sum_inv_le n
  have hlog : Real.log n ≤ Real.log T := by
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · subst h0; simp only [Nat.cast_zero, Real.log_zero]
      exact Real.log_natCast_nonneg T
    · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hn)
  have e : Real.sqrt (vi * Λ) * Real.sqrt n = Real.sqrt Λ * Real.sqrt (vi * n) := by
    rw [← Real.sqrt_mul (by positivity), ← Real.sqrt_mul hΛ]; ring_nf
  have hA : 0 ≤ a * Real.sqrt (vi * Λ) := by positivity
  calc _ ≤ 1 + a * Real.sqrt (vi * Λ) * (2 * Real.sqrt n) + 144 * Λ * (1 + Real.log n) := by
        gcongr
    _ = 1 + 2 * a * (Real.sqrt (vi * Λ) * Real.sqrt n) + 144 * Λ * (1 + Real.log n) := by ring
    _ ≤ _ := by
        rw [e, show 2 * a * (Real.sqrt Λ * Real.sqrt (vi * n)) =
          2 * a * Real.sqrt Λ * Real.sqrt (vi * n) by ring]
        have := mul_le_mul_of_nonneg_left hlog (by positivity : (0:ℝ) ≤ 144 * Λ)
        nlinarith


lemma sum_mem_ite {N : ℕ} (S : Finset (Fin N)) (f : Fin N → ℝ) :
    ∑ i ∈ S, f i = ∑ i, (if i ∈ S then f i else 0) := by
  rw [← Finset.sum_filter]; congr 1; ext i; simp

lemma pathD {N T : ℕ} (v r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hv0 : ∀ i, 0 ≤ v i) (h : History N T) :
    ∑ ℓ ∈ Finset.range (epochsStarted h), ∑ i ∈ nextSet r sel h ℓ, Dd v r sel h i ℓ ≤
      N * (1 + 144 * Real.log (Real.sqrt N * T + 1) * (1 + Real.log T)) +
        2 * (Real.sqrt 72 + Real.sqrt 24) * Real.sqrt (Real.log (Real.sqrt N * T + 1)) *
          (Real.sqrt N * Real.sqrt (∑ ℓ ∈ Finset.range (epochsStarted h),
            (1 + ∑ j ∈ nextSet r sel h ℓ, v j))) := by
  classical
  set L := epochsStarted h with hL
  set Λ := Real.log (Real.sqrt N * T + 1) with hΛ
  set a := Real.sqrt 72 + Real.sqrt 24 with ha
  have ha0 : 0 ≤ a := by positivity
  have hΛ0 : 0 ≤ Λ := by
    rw [hΛ]; exact Real.log_nonneg (by have := Real.sqrt_nonneg (N : ℝ); nlinarith [(Nat.cast_nonneg T : (0:ℝ) ≤ T)])
  have hle := epochsStarted_le r sel h
  set n : Fin N → ℕ := fun i => ((Finset.range L).filter (fun ℓ => i ∈ nextSet r sel h ℓ)).card
    with hn
  -- per product
  have hper : ∀ i, ∑ ℓ ∈ Finset.range L,
      (if i ∈ nextSet r sel h ℓ then Dd v r sel h i ℓ else 0) ≤
      1 + 2 * a * Real.sqrt Λ * Real.sqrt (v i * n i) + 144 * Λ * (1 + Real.log T) := by
    intro i
    calc _ ≤ ∑ ℓ ∈ Finset.range L, (if i ∈ nextSet r sel h ℓ then
          gW a (v i) Λ ((Finset.range ℓ).filter (fun ℓ' => i ∈ nextSet r sel h ℓ')).card
          else 0) := by
          apply Finset.sum_le_sum
          intro ℓ hℓ
          rw [Finset.mem_range] at hℓ
          split_ifs with hi
          · rw [← Tcount_eq_card r sel h i ℓ (by omega)]
            unfold Dd gW
            split_ifs with h0
            · rfl
            · unfold Bd
              have hlog : Real.log (Real.sqrt N * ℓ + 1) ≤ Λ := by
                rw [hΛ]
                apply Real.log_le_log (by positivity)
                have : (ℓ : ℝ) ≤ T := by exact_mod_cast (show ℓ ≤ T by omega)
                have := Real.sqrt_nonneg (N : ℝ)
                nlinarith
              have hTc : (0 : ℝ) < Tcount r sel h i ℓ := by
                have : 0 < Tcount r sel h i ℓ := Nat.pos_of_ne_zero h0
                exact_mod_cast this
              gcongr
              · exact hv0 i
          · rfl
      _ = ∑ k ∈ Finset.range (n i), gW a (v i) Λ k := count_sum _ _ L
      _ ≤ _ := sum_gW_le a (v i) Λ ha0 (hv0 i) hΛ0 (n i) T (by
          refine (Finset.card_le_card (Finset.filter_subset _ _)).trans ?_
          rw [Finset.card_range]; exact hle.2)
  have hswap : ∑ ℓ ∈ Finset.range L, ∑ i ∈ nextSet r sel h ℓ, Dd v r sel h i ℓ =
      ∑ i, ∑ ℓ ∈ Finset.range L, (if i ∈ nextSet r sel h ℓ then Dd v r sel h i ℓ else 0) := by
    rw [Finset.sum_comm]
    · apply Finset.sum_congr rfl; intro ℓ _; exact sum_mem_ite _ _
  rw [hswap] at *
  rw [hswap]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hper i)
  refine hsum.trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  -- Cauchy-Schwarz
  have hCS : ∑ i, Real.sqrt (v i * n i) ≤ Real.sqrt N * Real.sqrt (∑ i, v i * n i) := by
    have := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (Fin N)) (f := fun _ => (1 : ℝ))
      (g := fun i => v i * n i) (fun _ => by norm_num) (fun i => mul_nonneg (hv0 i) (Nat.cast_nonneg _))
    simpa using this
  have hVn : ∑ i, v i * (n i : ℝ) ≤
      ∑ ℓ ∈ Finset.range L, (1 + ∑ j ∈ nextSet r sel h ℓ, v j) := by
    have e1 : ∀ i, v i * (n i : ℝ) =
        ∑ ℓ ∈ Finset.range L, (if i ∈ nextSet r sel h ℓ then v i else 0) := by
      intro i
      simp only [hn, Finset.card_filter]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro ℓ _; split_ifs <;> simp
    simp only [e1]
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro ℓ _
    rw [← sum_mem_ite]; linarith
  have hsq : Real.sqrt (∑ i, v i * n i) ≤ Real.sqrt (∑ ℓ ∈ Finset.range L,
      (1 + ∑ j ∈ nextSet r sel h ℓ, v j)) := Real.sqrt_le_sqrt hVn
  have hB : 0 ≤ 2 * a * Real.sqrt Λ := by positivity
  have := mul_le_mul_of_nonneg_left (hCS.trans (mul_le_mul_of_nonneg_left hsq
    (Real.sqrt_nonneg _))) hB
  nlinarith


/-! ## The explicit regret bound -/

open scoped Classical in
lemma main_bound {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ)
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) :
    regret v r 𝒮 hne (alg1 r sel) T ≤
      (N + 1) * (13 * (1 + Real.log T)) +
      (N * (1 + 144 * Real.log (Real.sqrt N * T + 1) * (1 + Real.log T)) +
        2 * (Real.sqrt 72 + Real.sqrt 24) * Real.sqrt (Real.log (Real.sqrt N * T + 1)) *
          (Real.sqrt N * Real.sqrt (T + (N + 1)))) := by
  set π := alg1 r sel with hπ
  set p : History N T → ℝ := fun h => histProb v π h with hp
  have hp0 : ∀ h, 0 ≤ p h := fun h => histProb_nonneg v hv0 π h
  have hp1 : ∑ h, p h = 1 := t1_histProb_sum v hv0 π T
  set W : History N T → ℝ := fun h => ∑ ℓ ∈ Finset.range (epochsStarted h),
      (1 + ∑ j ∈ nextSet r sel h ℓ, v j) with hW
  have hW0 : ∀ h, 0 ≤ W h := fun h => Finset.sum_nonneg (fun ℓ _ => by
    have := Finset.sum_nonneg (fun j (_ : j ∈ nextSet r sel h ℓ) => hv0 j); linarith)
  set bad : History N T → ℝ := fun h => ∑ ℓ ∈ Finset.range (epochsStarted h),
      (if Good v r sel h ℓ then (0 : ℝ) else 1) with hbad
  set K : ℝ := N * (1 + 144 * Real.log (Real.sqrt N * T + 1) * (1 + Real.log T)) with hK
  set c : ℝ := 2 * (Real.sqrt 72 + Real.sqrt 24) * Real.sqrt (Real.log (Real.sqrt N * T + 1)) *
    Real.sqrt N with hc
  have hc0 : 0 ≤ c := by positivity
  have hpath : ∀ h : History N T, ∑ ℓ ∈ Finset.range (epochsStarted h),
      (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
        (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) ≤
      (N + 1) * bad h + (K + c * Real.sqrt (W h)) := by
    intro h
    have h1 : ∑ ℓ ∈ Finset.range (epochsStarted h),
        (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
          (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) ≤
        ∑ ℓ ∈ Finset.range (epochsStarted h), ((N + 1) * (if Good v r sel h ℓ then (0 : ℝ) else 1)
          + ∑ i ∈ nextSet r sel h ℓ, Dd v r sel h i ℓ) := by
      apply Finset.sum_le_sum
      intro ℓ _
      have hD : 0 ≤ ∑ i ∈ nextSet r sel h ℓ, Dd v r sel h i ℓ :=
        Finset.sum_nonneg (fun i _ => Dd_nonneg v r sel h i ℓ)
      by_cases hg : Good v r sel h ℓ
      · rw [if_pos hg, mul_zero, zero_add]
        exact dR_good v r 𝒮 sel hdc hne hsel hv0 hv1 hr h ℓ hg
      · rw [if_neg hg, mul_one]
        have := (dR_le v r 𝒮 sel hne hsel hv0 hv1 hr h ℓ).2
        linarith
    have h2 := pathD v r sel hv0 h
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at h1
    simp only [hbad, hK, hc, hW]
    have e : 2 * (Real.sqrt 72 + Real.sqrt 24) * Real.sqrt (Real.log (Real.sqrt N * T + 1)) *
        Real.sqrt N * Real.sqrt (∑ ℓ ∈ Finset.range (epochsStarted h),
          (1 + ∑ j ∈ nextSet r sel h ℓ, v j)) =
        2 * (Real.sqrt 72 + Real.sqrt 24) * Real.sqrt (Real.log (Real.sqrt N * T + 1)) *
        (Real.sqrt N * Real.sqrt (∑ ℓ ∈ Finset.range (epochsStarted h),
          (1 + ∑ j ∈ nextSet r sel h ℓ, v j))) := by ring
    rw [e]
    linarith
  have hA14 := eq_A_14 v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T
  have hbadE := bad_expect v r 𝒮 sel hTU hdc hne hsel hv0 hv1 hr T
  have hWE := expect_W v r sel hv0 hv1 T
  -- Jensen for the square root
  have hJ : ∑ h, p h * Real.sqrt (W h) ≤ Real.sqrt (T + (N + 1)) := by
    have hcs := Real.sum_sqrt_mul_sqrt_le (Finset.univ : Finset (History N T))
      (f := p) (g := fun h => p h * W h) hp0 (fun h => mul_nonneg (hp0 h) (hW0 h))
    have e : ∀ h, Real.sqrt (p h) * Real.sqrt (p h * W h) = p h * Real.sqrt (W h) := by
      intro h
      rw [Real.sqrt_mul (hp0 h), ← mul_assoc, Real.mul_self_sqrt (hp0 h)]
    simp only [e, hp1, Real.sqrt_one, one_mul] at hcs
    exact hcs.trans (Real.sqrt_le_sqrt hWE)
  calc regret v r 𝒮 hne π T ≤ ∑ h, p h * ((N + 1) * bad h + (K + c * Real.sqrt (W h))) := by
        refine hA14.trans (Finset.sum_le_sum (fun h _ => ?_))
        exact mul_le_mul_of_nonneg_left (hpath h) (hp0 h)
    _ = (N + 1) * ∑ h, p h * bad h + (K * ∑ h, p h + c * ∑ h, p h * Real.sqrt (W h)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · apply Finset.sum_congr rfl; intro h _; ring
        · congr 1
          · apply Finset.sum_congr rfl; intro h _; ring
          · apply Finset.sum_congr rfl; intro h _; ring
    _ ≤ (N + 1) * (13 * (1 + Real.log T)) + (K * 1 + c * Real.sqrt (T + (N + 1))) := by
        rw [hp1]
        gcongr
    _ = _ := by simp only [hK, hc]; ring


/-! ## Degenerate horizons and the final arithmetic -/

lemma regret_T0 {N : ℕ} (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
    (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (hne : 𝒮.Nonempty) :
    regret v r 𝒮 hne (alg1 r sel) 0 ≤ 0 := by
  unfold regret expectedRevenue; simp

lemma regret_N0 (v r : Fin 0 → ℝ) (𝒮 : Finset (Finset (Fin 0)))
    (sel : (Finset (Fin 0) → ℝ) → Finset (Fin 0)) (hne : 𝒮.Nonempty) (T : ℕ) :
    regret v r 𝒮 hne (alg1 r sel) T ≤ 0 := by
  have h0 : ∀ S : Finset (Fin 0), mnlObjective v r 1 S = 0 := by
    intro S; rw [Subsingleton.elim S ∅]; unfold mnlObjective; simp
  unfold regret expectedRevenue optRevenue
  simp only [h0]
  simp

lemma regret_11 (v r : Fin 1 → ℝ) (𝒮 : Finset (Finset (Fin 1)))
    (sel : (Finset (Fin 1) → ℝ) → Finset (Fin 1)) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) :
    regret v r 𝒮 hne (alg1 r sel) 1 ≤ 0 := by
  set S0 := optimisticSet r sel [] with hS0
  have hoff : ∀ (h : History 1 1) (t : Fin 1), offered (alg1 r sel) h t = S0 := by
    intro h t
    have ht : t = 0 := Subsingleton.elim _ _
    subst ht
    rfl
  have hexp : expectedRevenue v r (alg1 r sel) 1 = mnlObjective v r 1 S0 := by
    unfold expectedRevenue
    simp only [hoff, Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_smul]
    rw [← Finset.sum_mul, t1_histProb_sum v hv0, one_mul]
  have hopt : optRevenue v r 𝒮 hne ≤ mnlObjective v r 1 S0 := by
    apply Finset.sup'_le
    intro Q hQ
    have hsQ := (hsel (fun S => mnlObjective (fun i => vUCBL ([] : List (EpochRecord 1)) i) r 1 S)).2 Q hQ
    have hu : (fun i => vUCBL ([] : List (EpochRecord 1)) i) = fun _ => (1 : ℝ) := by
      funext i; simp [vUCBL, TcountL]
    rw [hu] at hsQ
    change mnlObjective (fun _ => (1 : ℝ)) r 1 Q ≤ mnlObjective (fun _ => (1 : ℝ)) r 1 S0 at hsQ
    have hS0nn := (mnl_le_one v r hv0 hr S0).1
    -- the subsets of `Fin 1`
    have hsub : ∀ S : Finset (Fin 1), S = ∅ ∨ S = {0} := by
      intro S
      by_cases h : (0 : Fin 1) ∈ S
      · right; ext i; have : i = 0 := Subsingleton.elim _ _; subst this; simp [h]
      · left; ext i; have : i = 0 := Subsingleton.elim _ _; subst this; simp [h]
    rcases hsub Q with hQe | hQe
    · subst hQe
      have : mnlObjective v r 1 ∅ = 0 := by simp [mnlObjective]
      rw [this]; exact hS0nn
    · rcases hsub S0 with hS | hS
      · -- `S0 = ∅`, so `r 0 / 2 ≤ 0`, hence `r 0 = 0`
        rw [hS, hQe] at hsQ
        rw [hS, hQe]
        unfold mnlObjective at hsQ ⊢
        simp at hsQ ⊢
        have hr0 := (hr 0).1
        have : r 0 = 0 := by linarith
        rw [this]; simp
      · rw [hS, hQe]
  unfold regret
  rw [hexp]
  simp only [Nat.cast_one, one_mul]
  linarith

lemma final_arith (N T lT Λ ℒ : ℝ) (hN : 1 ≤ N) (hℒ : 0.69 < ℒ) (hT : 0 ≤ T)
    (hlT0 : 0 ≤ lT) (hlT : lT ≤ ℒ) (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ 2 * ℒ) :
    (N + 1) * (13 * (1 + lT)) +
      (N * (1 + 144 * Λ * (1 + lT)) +
        2 * (Real.sqrt 72 + Real.sqrt 24) * Real.sqrt Λ * (Real.sqrt N * Real.sqrt (T + (N + 1))))
      ≤ 100 * Real.sqrt (N * T * ℒ) + 2000 * N * ℒ ^ 2 := by
  have ha : Real.sqrt 72 + Real.sqrt 24 ≤ 14 := by
    have h1 : Real.sqrt 72 ≤ 9 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have h2 : Real.sqrt 24 ≤ 5 := by
      rw [Real.sqrt_le_left (by norm_num)]; norm_num
    linarith
  have hℒ0 : 0 ≤ ℒ := by linarith
  set sN := Real.sqrt N with hsN
  set sT := Real.sqrt T with hsT
  set sL := Real.sqrt ℒ with hsL
  have hsN2 : sN ^ 2 = N := Real.sq_sqrt (by linarith)
  have hsL2 : sL ^ 2 = ℒ := Real.sq_sqrt hℒ0
  have hsN0 : 0 ≤ sN := Real.sqrt_nonneg _
  have hsT0 : 0 ≤ sT := Real.sqrt_nonneg _
  have hsL0 : 0 ≤ sL := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 ≤ 3 / 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hs20 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hs22 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  -- √Λ ≤ √2 · √ℒ
  have hsΛ : Real.sqrt Λ ≤ Real.sqrt 2 * sL := by
    rw [← Real.sqrt_mul (by norm_num)]; exact Real.sqrt_le_sqrt (by linarith)
  -- √(T + N + 1) ≤ √T + √2 √N
  have hsTN : Real.sqrt (T + (N + 1)) ≤ sT + Real.sqrt 2 * sN := by
    have h1 : Real.sqrt (T + (N + 1)) ≤ Real.sqrt (T + 2 * N) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (T + 2 * N) ≤ sT + Real.sqrt (2 * N) := by
      have hx : T + 2 * N ≤ (sT + Real.sqrt (2 * N)) ^ 2 := by
        have := Real.sq_sqrt hT; have := Real.sq_sqrt (show (0:ℝ) ≤ 2 * N by linarith)
        nlinarith [Real.sqrt_nonneg (2 * N)]
      calc Real.sqrt (T + 2 * N) ≤ Real.sqrt ((sT + Real.sqrt (2 * N)) ^ 2) := Real.sqrt_le_sqrt hx
        _ = _ := Real.sqrt_sq (by positivity)
    rw [Real.sqrt_mul (by norm_num)] at h2
    linarith
  have hroot : Real.sqrt (N * T * ℒ) = sN * sT * sL := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by linarith)]
  rw [hroot]
  -- the square-root term
  have hA : 2 * (Real.sqrt 72 + Real.sqrt 24) * Real.sqrt Λ * (sN * Real.sqrt (T + (N + 1)))
      ≤ 28 * (Real.sqrt 2 * sL) * (sN * (sT + Real.sqrt 2 * sN)) := by
    have hΛs := Real.sqrt_nonneg Λ
    have hts := Real.sqrt_nonneg (T + (N + 1))
    gcongr
    · linarith
  have hB : 28 * (Real.sqrt 2 * sL) * (sN * (sT + Real.sqrt 2 * sN)) ≤
      42 * (sN * sT * sL) + 56 * N * sL := by
    have e : 28 * (Real.sqrt 2 * sL) * (sN * (sT + Real.sqrt 2 * sN)) =
        28 * Real.sqrt 2 * (sN * sT * sL) + 28 * (Real.sqrt 2 ^ 2) * (sN ^ 2) * sL := by ring
    rw [e, hs22, hsN2]
    have : 0 ≤ sN * sT * sL := by positivity
    nlinarith
  have hsLb : sL ≤ 3 * ℒ ^ 2 := by
    nlinarith [sq_nonneg (sL - 1)]
  have hNs : 56 * N * sL ≤ 168 * N * ℒ ^ 2 := by nlinarith
  have hrest : (N + 1) * (13 * (1 + lT)) + N * (1 + 144 * Λ * (1 + lT)) ≤ 1832 * N * ℒ ^ 2 := by
    have h1 : 1 + lT ≤ 3 * ℒ := by linarith
    have h2 : (N + 1) * (13 * (1 + lT)) ≤ 2 * N * (13 * (3 * ℒ)) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have h3 : 144 * Λ * (1 + lT) ≤ 144 * (2 * ℒ) * (3 * ℒ) := by
      apply mul_le_mul (by linarith) h1 (by positivity) (by positivity)
    have h4 : N * (1 + 144 * Λ * (1 + lT)) ≤ N * (1 + 144 * (2 * ℒ) * (3 * ℒ)) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  have hX : 0 ≤ sN * sT * sL := by positivity
  linarith [hA, hB, hNs, hrest]

end MNLT1

open ChoiceCDLP.MNL MNLBandit.UCB in
theorem solution :
    ∃ C₁ C₂ : ℝ, ∀ (N : ℕ) (v r : Fin N → ℝ) (𝒮 : Finset (Finset (Fin N)))
      (hne : 𝒮.Nonempty) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) (T : ℕ),
      IsTU 𝒮 → DownClosed 𝒮 → IsArgmaxSel 𝒮 sel →
      (∀ i, 0 ≤ v i) → (∀ i, v i ≤ 1) → (∀ i, r i ∈ Set.Icc (0 : ℝ) 1) →
      regret v r 𝒮 hne (alg1 r sel) T ≤
        C₁ * Real.sqrt (N * T * Real.log (N * T)) + C₂ * N * Real.log (N * T) ^ 2 := by
  refine ⟨100, 2000, ?_⟩
  intro N v r 𝒮 hne sel T hTU hdc hsel hv0 hv1 hr
  have hR0 : 0 ≤ 100 * Real.sqrt (N * T * Real.log (N * T)) +
      2000 * N * Real.log (N * T) ^ 2 := by positivity
  rcases Nat.eq_zero_or_pos T with hT0 | hTpos
  · subst hT0; exact (MNLT1.regret_T0 v r 𝒮 sel hne).trans hR0
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; exact (MNLT1.regret_N0 v r 𝒮 sel hne T).trans hR0
  by_cases h11 : N = 1 ∧ T = 1
  · obtain ⟨rfl, rfl⟩ := h11
    exact (MNLT1.regret_11 v r 𝒮 sel hne hsel hv0 hr).trans hR0
  have hNT : (2 : ℝ) ≤ (N : ℝ) * T := by
    have : 2 ≤ N * T := by
      rcases Nat.lt_or_ge 1 N with h | h
      · nlinarith
      · have : N = 1 := by omega
        subst this; omega
    exact_mod_cast this
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have hℒ : 0.69 < Real.log (N * T) := by
    have := Real.log_le_log (by norm_num) hNT
    have := Real.log_two_gt_d9
    linarith
  have hlT : Real.log T ≤ Real.log (N * T) :=
    Real.log_le_log (by linarith) (by nlinarith)
  have hlT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hΛ0 : 0 ≤ Real.log (Real.sqrt N * T + 1) := by
    apply Real.log_nonneg; have := Real.sqrt_nonneg (N : ℝ); nlinarith
  have hΛ : Real.log (Real.sqrt N * T + 1) ≤ 2 * Real.log (N * T) := by
    have hsN : Real.sqrt N ≤ N := by
      rw [Real.sqrt_le_left (by linarith)]; nlinarith
    have h1 : Real.sqrt N * T + 1 ≤ 2 * (N * T) := by nlinarith
    have h2 : Real.log (Real.sqrt N * T + 1) ≤ Real.log (2 * (N * T)) :=
      Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (by positivity)] at h2
    have : Real.log 2 ≤ Real.log (N * T) := Real.log_le_log (by norm_num) hNT
    linarith
  have hmain := MNLT1.main_bound v r 𝒮 sel T hTU hdc hne hsel hv0 hv1 hr
  have hfin := MNLT1.final_arith N T (Real.log T) (Real.log (Real.sqrt N * T + 1))
    (Real.log (N * T)) hN1 hℒ (by linarith) hlT0 hlT hΛ0 hΛ
  linarith
