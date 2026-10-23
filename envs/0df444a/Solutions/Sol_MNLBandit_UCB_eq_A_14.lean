-- Prove2me | solution 1 for MNLBandit.UCB.eq_A_14
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T07:31:17.192988+00:00
-- url     : https://prove2.me/submissions/4cc2a01f-f791-4448-91e2-a442ab1cd913

import Mathlib
import Definitions.Def_ChoiceCDLP_MNL_mnlObjective
import Definitions.Def_MNLBandit_UCB_Setting
import Definitions.Def_MNLBandit_UCB_Algorithm1



namespace MNLBandit.UCB

open ChoiceCDLP.MNL

lemma g59_choiceProb_nonneg {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N))
    (a : Option (Fin N)) : 0 ≤ choiceProb v S a := by
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  cases a with
  | none => simp only [choiceProb]; positivity
  | some i =>
    simp only [choiceProb]
    split_ifs
    · exact div_nonneg (hv i) (by linarith)
    · exact le_refl _

lemma g59_choiceProb_sum {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (S : Finset (Fin N)) :
    ∑ a, choiceProb v S a = 1 := by
  have hV : 0 ≤ ∑ j ∈ S, v j := Finset.sum_nonneg (fun j _ => hv j)
  rw [Fintype.sum_option]
  simp only [choiceProb]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.sum_div]
  field_simp

lemma g59_histPrefix_snoc_castSucc {N T : ℕ} (h : History N T) (a : Option (Fin N)) (t : Fin T) :
    histPrefix (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) t.castSucc
      = histPrefix h t := by
  funext u
  show (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) (Fin.castLE _ u) = h (Fin.castLE _ u)
  have : (Fin.castLE (t.castSucc).isLt.le u : Fin (T+1)) = Fin.castSucc (Fin.castLE t.isLt.le u) :=
    Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma g59_histPrefix_snoc_last {N T : ℕ} (h : History N T) (a : Option (Fin N)) :
    histPrefix (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) (Fin.last T)
      = h := by
  funext u
  show (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1)) (Fin.castLE _ u) = h u
  have : (Fin.castLE (Fin.last T).isLt.le u : Fin (T+1)) = Fin.castSucc u := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

lemma g59_histProb_snoc {N T : ℕ} (v : Fin N → ℝ) (π : Policy N) (h : History N T)
    (a : Option (Fin N)) :
    histProb v π (Fin.snoc (α := fun _ => Option (Fin N)) h a : History N (T+1))
      = histProb v π h * choiceProb v (π T h) a := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  congr 1
  · apply Finset.prod_congr rfl
    intro t _
    unfold offered
    rw [g59_histPrefix_snoc_castSucc, Fin.snoc_castSucc]
    rfl
  · unfold offered
    rw [g59_histPrefix_snoc_last, Fin.snoc_last]
    rfl

lemma g59_sum_hist_succ {N T : ℕ} (f : History N (T+1) → ℝ) :
    ∑ h, f h = ∑ h : History N T, ∑ a, f (Fin.snoc (α := fun _ => Option (Fin N)) h a) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (T+1) => Option (Fin N))).sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  rfl


lemma g59_histProb_sum {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N) :
    ∀ T : ℕ, ∑ h : History N T, histProb v π h = 1 := by
  intro T
  induction T with
  | zero => simp [histProb]
  | succ T ih =>
    rw [g59_sum_hist_succ]
    simp_rw [g59_histProb_snoc, ← Finset.mul_sum, g59_choiceProb_sum v hv, mul_one]
    exact ih

lemma g59_expect_eq {N : ℕ} (v : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i) (π : Policy N)
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
    rw [g59_sum_hist_succ, ← Finset.sum_add_distrib]
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
        rw [g59_histPrefix_snoc_castSucc, Fin.snoc_castSucc]
        rfl
      · rw [g59_histPrefix_snoc_last, Fin.snoc_last]
        rfl
    simp_rw [e1, g59_histProb_snoc]
    have hs := g59_choiceProb_sum v hv (π T h)
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


lemma g59_fold_prefix {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
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

lemma g59_fold_cur {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
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

lemma g59_fold_len {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N)) :
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

lemma g59_runAlg_cur {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs : List (Option (Fin N))) :
    (runAlg r sel cs).cur = optimisticSet r sel (runAlg r sel cs).past :=
  g59_fold_cur r sel cs _ rfl

lemma g59_runAlg_len {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs : List (Option (Fin N))) :
    (runAlg r sel cs).past.length = cs.count none := by
  unfold runAlg; rw [g59_fold_len]; simp [initState]

lemma g59_runAlg_prefix {N : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (cs ds : List (Option (Fin N))) :
    (runAlg r sel cs).past <+: (runAlg r sel (cs ++ ds)).past := by
  unfold runAlg; rw [List.foldl_append]; exact g59_fold_prefix r sel ds _

lemma g59_ofFn_histPrefix {N T : ℕ} (h : History N T) (t : Fin T) :
    List.ofFn (histPrefix h t) = (List.ofFn h).take t := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp [histPrefix]

lemma g59_offered_eq {N T : ℕ} (r : Fin N → ℝ) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (h : History N T) (t : Fin T) :
    offered (alg1 r sel) h t = nextSet r sel h (((List.ofFn h).take t).count none) := by
  unfold offered alg1 nextSet pastUpTo finalState
  rw [g59_runAlg_cur, g59_ofFn_histPrefix]
  congr 1
  have hp := g59_runAlg_prefix r sel ((List.ofFn h).take t) ((List.ofFn h).drop t)
  rw [List.take_append_drop] at hp
  rw [List.prefix_iff_eq_take.mp hp, g59_runAlg_len]


lemma g59_count_take {N T : ℕ} (h : History N T) :
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

lemma g59_count_mono {N T : ℕ} (h : History N T) {m m' : ℕ} (hmm : m ≤ m') :
    ((List.ofFn h).take m).count none ≤ ((List.ofFn h).take m').count none := by
  apply List.IsPrefix.count_le
  have : (List.ofFn h).take m = ((List.ofFn h).take m').take m := by
    rw [List.take_take, min_eq_left hmm]
  rw [this]; exact List.take_prefix _ _

lemma g59_count_succ {N T : ℕ} (h : History N T) (t : Fin T) (ht : h t = none) :
    ((List.ofFn h).take (t.val + 1)).count none = ((List.ofFn h).take t.val).count none + 1 := by
  rw [List.take_add_one, List.count_append]
  have hg : (List.ofFn h)[t.val]? = some (h t) := by simp
  rw [hg, ht]; simp

lemma g59_pathwise {N T : ℕ} (h : History N T) (G : ℕ → ℝ) (hG : ∀ ℓ, 0 ≤ G ℓ) :
    ∑ t : Fin T, (if h t = none then G (((List.ofFn h).take t).count none) else 0)
      ≤ ∑ ℓ ∈ Finset.range (epochsStarted h), G ℓ := by
  rw [← Finset.sum_filter]
  set k : Fin T → ℕ := fun t => ((List.ofFn h).take t).count none with hk
  have hlt : ∀ t t' : Fin T, h t = none → t < t' → k t < k t' := by
    intro t t' ht htt'
    have := g59_count_succ h t ht
    have h2 := g59_count_mono h (show t.val + 1 ≤ t'.val from htt')
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
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
    obtain ⟨t, ht, rfl⟩ := hℓ
    rw [Finset.mem_range]
    have hT : T ≠ 0 := by have := t.isLt; omega
    unfold epochsStarted
    rw [if_neg hT]
    have h1 := g59_count_mono h (show t.val ≤ T - 1 by have := t.isLt; omega)
    rw [g59_count_take h (T-1)] at h1
    have h3 : (Finset.univ.filter (fun u : Fin T => u.val < T - 1 ∧ h u = none))
        = (Finset.univ.filter (fun u : Fin T => u.val + 1 < T ∧ h u = none)) := by
      apply Finset.filter_congr; intro u _; constructor
      · rintro ⟨a, b⟩; exact ⟨by omega, b⟩
      · rintro ⟨a, b⟩; exact ⟨by omega, b⟩
    rw [h3] at h1
    simp only [hk]; omega
  · intro ℓ _ _; exact hG ℓ


theorem eq_A_14_core {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (T : ℕ) :
    regret v r 𝒮 hne (alg1 r sel) T ≤
      ∑ h : History N T, histProb v (alg1 r sel) h *
        ∑ ℓ ∈ Finset.range (epochsStarted h),
          (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
            (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) := by
  set opt := optRevenue v r 𝒮 hne with hopt
  set π := alg1 r sel with hπ
  let X : (t : ℕ) → (Fin t → Option (Fin N)) → Option (Fin N) → ℝ :=
    fun t pre _ => opt - mnlObjective v r 1 (π t pre)
  let Y : (t : ℕ) → (Fin t → Option (Fin N)) → Option (Fin N) → ℝ :=
    fun t pre a => if a = none then
      (1 + ∑ j ∈ π t pre, v j) * (opt - mnlObjective v r 1 (π t pre)) else 0
  have hXY : ∀ t pre, ∑ a, choiceProb v (π t pre) a * X t pre a
      = ∑ a, choiceProb v (π t pre) a * Y t pre a := by
    intro t pre
    have hV : 0 ≤ ∑ j ∈ π t pre, v j := Finset.sum_nonneg (fun j _ => hv0 j)
    rw [← Finset.sum_mul, g59_choiceProb_sum v hv0, one_mul, Fintype.sum_option]
    simp only [Y, X, if_true, reduceCtorEq, if_false, mul_zero, Finset.sum_const_zero, add_zero,
      choiceProb]
    field_simp
  have hreg : regret v r 𝒮 hne π T
      = ∑ h : History N T, histProb v π h * ∑ t : Fin T, X t (histPrefix h t) (h t) := by
    unfold regret expectedRevenue
    have h1 : (T : ℝ) * opt = ∑ h : History N T, histProb v π h * ∑ _t : Fin T, opt := by
      rw [← Finset.sum_mul, g59_histProb_sum v hv0, one_mul]; simp
    rw [h1, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro h _
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    rfl
  rw [hreg, g59_expect_eq v hv0 π X Y hXY T]
  apply Finset.sum_le_sum
  intro h _
  apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg (fun t _ => g59_choiceProb_nonneg v hv0 _ _))
  have hG : ∀ ℓ, 0 ≤ (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
      (opt - mnlObjective v r 1 (nextSet r sel h ℓ)) := by
    intro ℓ
    have hmem : nextSet r sel h ℓ ∈ 𝒮 := (hsel _).1
    have hle : mnlObjective v r 1 (nextSet r sel h ℓ) ≤ opt :=
      Finset.le_sup' (fun S => mnlObjective v r 1 S) hmem
    have hV : 0 ≤ ∑ j ∈ nextSet r sel h ℓ, v j := Finset.sum_nonneg (fun j _ => hv0 j)
    apply mul_nonneg <;> linarith
  refine le_trans (le_of_eq ?_) (g59_pathwise h _ hG)
  apply Finset.sum_congr rfl
  intro t _
  have e : π t (histPrefix h t) = nextSet r sel h (((List.ofFn h).take t).count none) :=
    g59_offered_eq r sel h t
  simp only [Y]
  rw [e]

end MNLBandit.UCB

open MNLBandit.UCB
open ChoiceCDLP.MNL

theorem solution {N : ℕ} (v r : Fin N → ℝ)
    (𝒮 : Finset (Finset (Fin N))) (sel : (Finset (Fin N) → ℝ) → Finset (Fin N))
    (hTU : IsTU 𝒮) (hdc : DownClosed 𝒮) (hne : 𝒮.Nonempty) (hsel : IsArgmaxSel 𝒮 sel)
    (hv0 : ∀ i, 0 ≤ v i) (hv1 : ∀ i, v i ≤ 1) (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1)
    (T : ℕ) :
    regret v r 𝒮 hne (alg1 r sel) T ≤
      ∑ h : History N T, histProb v (alg1 r sel) h *
        ∑ ℓ ∈ Finset.range (epochsStarted h),
          (1 + ∑ j ∈ nextSet r sel h ℓ, v j) *
            (optRevenue v r 𝒮 hne - mnlObjective v r 1 (nextSet r sel h ℓ)) := by
  exact eq_A_14_core v r 𝒮 sel hne hsel hv0 T
