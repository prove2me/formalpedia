-- Prove2me | solution 1 for LawlerMoore.PrecDeadline.sorted_isFeasible
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T09:05:33.810039+00:00
-- url     : https://prove2.me/submissions/7d40e3b3-d052-4d13-9a45-2d3b76a37da4

import Mathlib
import Definitions.Def_MooreLateJobs_Shared_completionTime
import Definitions.Def_LawlerPrec_MinMax_IsFeasible
import Definitions.Def_LawlerMoore_PrecDeadline_modifiedDeadline



namespace LawlerMoore.PrecDeadline
set_option autoImplicit false

lemma lm_mono {n : ℕ} (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (i j : Fin n) (hij : i ≠ j) (h : ρ i j) :
    modifiedDeadline ρ d ε i < modifiedDeadline ρ d ε j := by
  unfold modifiedDeadline
  have h1 : (insert i (Finset.univ.filter (ρ i))).inf' (Finset.insert_nonempty _ _) d
      ≤ (insert j (Finset.univ.filter (ρ j))).inf' (Finset.insert_nonempty _ _) d := by
    apply Finset.inf'_mono
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rcases hk with rfl | hk
    · exact Or.inr h
    · exact Or.inr (htrans _ _ _ h hk)
  have h2 : (i : ℕ) < j := lt_of_le_of_ne (hnum _ _ h) (fun e => hij (Fin.ext e))
  have h3 : ((i : ℕ) + 1 : ℝ) * ε < ((j : ℕ) + 1 : ℝ) * ε := by
    apply mul_lt_mul_of_pos_right _ hε
    have : (i : ℝ) < j := by exact_mod_cast h2
    linarith
  linarith

lemma lm_succ {n : ℕ} (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (i j : Fin n) (hlt : modifiedDeadline ρ d ε j < modifiedDeadline ρ d ε i) :
    ∃ k, (k = j ∨ ρ j k) ∧ d k ≤ d i := by
  unfold modifiedDeadline at hlt
  obtain ⟨k, hk, hkeq⟩ := Finset.exists_mem_eq_inf' (Finset.insert_nonempty j (Finset.univ.filter (ρ j))) d
  simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hk
  refine ⟨k, hk, ?_⟩
  by_contra hcon
  push Not at hcon
  have hg := hgap _ _ hcon
  have hi : (insert i (Finset.univ.filter (ρ i))).inf' (Finset.insert_nonempty _ _) d ≤ d i :=
    Finset.inf'_le _ (Finset.mem_insert_self _ _)
  have hi1 : ((i : ℕ) + 1 : ℝ) ≤ n := by
    have : (i : ℕ) + 1 ≤ n := i.isLt
    exact_mod_cast this
  have hi2 : ((i : ℕ) + 1 : ℝ) * ε ≤ n * ε := mul_le_mul_of_nonneg_right hi1 hε.le
  have hj : 0 < ((j : ℕ) + 1 : ℝ) * ε := by positivity
  rw [hkeq] at hlt
  linarith

lemma lm_inj {n : ℕ} (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (i j : Fin n) (h : modifiedDeadline ρ d ε i = modifiedDeadline ρ d ε j) : i = j := by
  unfold modifiedDeadline at h
  obtain ⟨k, -, hk⟩ := Finset.exists_mem_eq_inf' (Finset.insert_nonempty i (Finset.univ.filter (ρ i))) d
  obtain ⟨k', -, hk'⟩ := Finset.exists_mem_eq_inf' (Finset.insert_nonempty j (Finset.univ.filter (ρ j))) d
  rw [hk, hk'] at h
  by_contra hne
  have hi1 : ((i : ℕ) + 1 : ℝ) ≤ n := by
    have : (i : ℕ) + 1 ≤ n := i.isLt
    exact_mod_cast this
  have hj1 : ((j : ℕ) + 1 : ℝ) ≤ n := by
    have : (j : ℕ) + 1 ≤ n := j.isLt
    exact_mod_cast this
  have hij : (i : ℝ) ≠ j := by
    intro e; exact hne (Fin.ext (by exact_mod_cast e))
  have hd : |((i : ℝ)) - j| ≥ 1 := by
    have : (i : ℕ) ≠ j := fun e => hne (Fin.ext e)
    rcases lt_or_gt_of_ne this with h | h
    · have : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_of_neg (by linarith)]; linarith
    · have : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]; linarith
  have hnn : (0:ℝ) ≤ i ∧ (0:ℝ) ≤ j := ⟨by positivity, by positivity⟩
  rcases lt_trichotomy (d k) (d k') with h1 | h1 | h1
  · have := hgap _ _ h1
    nlinarith
  · have : ((i : ℕ) + 1 : ℝ) * ε = ((j : ℕ) + 1 : ℝ) * ε := by linarith
    have := mul_right_cancel₀ hε.ne' this
    exact hij (by linarith)
  · have := hgap _ _ h1
    nlinarith

open MooreLateJobs.Shared in
lemma ct_append {n : ℕ} (a : Fin n → ℝ) (l₁ l₂ : List (Fin n)) (x : Fin n) (h : x ∉ l₁) :
    completionTime a (l₁ ++ l₂) x = (l₁.map a).sum + ((l₂.take (l₂.idxOf x + 1)).map a).sum := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_notMem h]
  have : l₁.length + l₂.idxOf x + 1 = l₁.length + (l₂.idxOf x + 1) := by omega
  rw [this, List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left,
    List.map_append, List.sum_append]

open MooreLateJobs.Shared in
lemma ct_left {n : ℕ} (a : Fin n → ℝ) (l₁ l₂ l₃ : List (Fin n)) (x : Fin n) (h : x ∈ l₁) :
    completionTime a (l₁ ++ l₂) x = completionTime a (l₁ ++ l₃) x := by
  unfold completionTime completionAt
  rw [List.idxOf_append_of_mem h, List.idxOf_append_of_mem h]
  have hlt : l₁.idxOf x < l₁.length := List.idxOf_lt_length_iff.2 h
  rw [List.take_append_of_le_length (by omega), List.take_append_of_le_length (by omega)]


open MooreLateJobs.Shared in
lemma ct_first {n : ℕ} (a : Fin n → ℝ) (l₁ L : List (Fin n)) (p q : Fin n) (h : p ∉ l₁) :
    completionTime a (l₁ ++ p :: q :: L) p = (l₁.map a).sum + a p := by
  rw [ct_append a l₁ _ p h]; simp

open MooreLateJobs.Shared in
lemma ct_second {n : ℕ} (a : Fin n → ℝ) (l₁ L : List (Fin n)) (p q : Fin n) (h : q ∉ l₁) (hpq : p ≠ q) :
    completionTime a (l₁ ++ p :: q :: L) q = (l₁.map a).sum + (a p + a q) := by
  rw [ct_append a l₁ _ q h]
  simp [List.idxOf_cons, beq_false_of_ne hpq]

open MooreLateJobs.Shared in
lemma ct_rest {n : ℕ} (a : Fin n → ℝ) (l₁ L : List (Fin n)) (p q x : Fin n) (h : x ∉ l₁) (hp : x ≠ p) (hq : x ≠ q) :
    completionTime a (l₁ ++ p :: q :: L) x
      = (l₁.map a).sum + (a p + a q) + ((L.take (L.idxOf x + 1)).map a).sum := by
  rw [ct_append a l₁ _ x h]
  simp [List.idxOf_cons, beq_false_of_ne hp.symm, beq_false_of_ne hq.symm]
  ring

lemma sorted_core (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε)
    (l : List (Fin n)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hsorted : l.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y)) :
    LawlerPrec.MinMax.IsFeasible ρ Finset.univ l := by
  refine ⟨hl, ?_⟩
  refine List.Pairwise.imp_of_mem ?_ hsorted
  intro x y hx hy hxy hρ
  have hne : y ≠ x := by
    intro e; subst e; exact lt_irrefl _ hxy
  have := lm_mono d ρ htrans hnum ε hε y x hne hρ
  linarith

open MooreLateJobs.Shared in
lemma adj_core (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (l₁ l₂ : List (Fin n)) (i j : Fin n)
    (hfeas : LawlerPrec.MinMax.IsFeasible ρ Finset.univ (l₁ ++ i :: j :: l₂))
    (hon : ∀ x, completionTime a (l₁ ++ i :: j :: l₂) x ≤ d x)
    (hlt : modifiedDeadline ρ d ε j < modifiedDeadline ρ d ε i) :
    LawlerPrec.MinMax.IsFeasible ρ Finset.univ (l₁ ++ j :: i :: l₂) ∧
      ∀ x, completionTime a (l₁ ++ j :: i :: l₂) x ≤ d x := by
  obtain ⟨⟨hnd, hmem⟩, hpw⟩ := hfeas
  have hperm : (l₁ ++ j :: i :: l₂).Perm (l₁ ++ i :: j :: l₂) := by
    apply List.Perm.append_left; exact List.Perm.swap _ _ _
  have hnd' : (l₁ ++ j :: i :: l₂).Nodup := hperm.nodup_iff.2 hnd
  have hij : i ≠ j := by
    intro e; subst e; simp [List.nodup_append] at hnd
  have hjl₁ : j ∉ l₁ := by
    intro h; simp [List.nodup_append] at hnd; grind
  have hil₁ : i ∉ l₁ := by
    intro h; simp [List.nodup_append] at hnd; grind
  -- feasibility
  have hfeas' : LawlerPrec.MinMax.IsFeasible ρ Finset.univ (l₁ ++ j :: i :: l₂) := by
    refine ⟨⟨hnd', fun x => by simpa using (hperm.mem_iff.trans (hmem x))⟩, ?_⟩
    have hnρ : ¬ ρ i j := fun h => by
      have := lm_mono d ρ htrans hnum ε hε i j hij h
      linarith
    simp only [List.pairwise_append, List.pairwise_cons, List.mem_append, List.mem_cons] at hpw ⊢
    grind
  refine ⟨hfeas', ?_⟩
  have hnρ1 : ∀ k ∈ l₁, ¬ ρ j k := by
    simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons] at hpw
    grind
  have hnρ2 : ¬ ρ j i := by
    simp only [List.pairwise_append, List.pairwise_cons, List.mem_cons] at hpw
    grind
  have hnn2 : ∀ L : List (Fin n) , ∀ m, 0 ≤ ((L.take m).map a).sum := by
    intro L m; exact List.sum_nonneg (by simp only [List.mem_map]; rintro _ ⟨y, -, rfl⟩; exact ha y)
  have hai := ha i
  have haj := ha j
  -- key: old completion of j is at most d i
  have key : (l₁.map a).sum + (a i + a j) ≤ d i := by
    obtain ⟨k, hk, hdk⟩ := lm_succ d ρ ε hε hgap i j hlt
    have hkon := hon k
    have : (l₁.map a).sum + (a i + a j) ≤ completionTime a (l₁ ++ i :: j :: l₂) k := by
      by_cases hk1 : k ∈ l₁
      · exfalso
        rcases hk with rfl | hk
        · exact hjl₁ hk1
        · exact hnρ1 k hk1 hk
      by_cases hki : k = i
      · subst hki
        rcases hk with h | h
        · exact absurd h hij
        · exact absurd h hnρ2
      by_cases hkj : k = j
      · subst hkj
        rw [ct_second a l₁ l₂ i k hjl₁ hij]
      · rw [ct_rest a l₁ l₂ i j k hk1 hki hkj]
        linarith [hnn2 l₂ (l₂.idxOf k + 1)]
    linarith
  intro x
  by_cases hx1 : x ∈ l₁
  · rw [ct_left a l₁ _ (i :: j :: l₂) x hx1]; exact hon x
  by_cases hxj : x = j
  · subst hxj
    have := hon x
    rw [ct_second a l₁ l₂ i x hx1 hij] at this
    rw [ct_first a l₁ l₂ x i hx1]
    linarith
  by_cases hxi : x = i
  · subst hxi
    rw [ct_second a l₁ l₂ j x hil₁ hij.symm]
    linarith
  · have := hon x
    rw [ct_rest a l₁ l₂ i j x hx1 hxi hxj] at this
    rw [ct_rest a l₁ l₂ j i x hx1 hxj hxi]
    linarith


open MooreLateJobs.Shared in
lemma move_front (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (x : Fin n) (A : List (Fin n)) :
    ∀ (pre B : List (Fin n)), (∀ y ∈ A, modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y) →
      (LawlerPrec.MinMax.IsFeasible ρ Finset.univ (pre ++ (A ++ x :: B)) ∧
        ∀ j, completionTime a (pre ++ (A ++ x :: B)) j ≤ d j) →
      (LawlerPrec.MinMax.IsFeasible ρ Finset.univ (pre ++ x :: (A ++ B)) ∧
        ∀ j, completionTime a (pre ++ x :: (A ++ B)) j ≤ d j) := by
  induction A with
  | nil => intro pre B _ h; simpa using h
  | cons y A' ih =>
    intro pre B hA h
    have h1 : pre ++ ((y :: A') ++ x :: B) = (pre ++ [y]) ++ (A' ++ x :: B) := by simp
    rw [h1] at h
    have h2 := ih (pre ++ [y]) B (fun z hz => hA z (List.mem_cons_of_mem _ hz)) h
    have h3 : (pre ++ [y]) ++ x :: (A' ++ B) = pre ++ y :: x :: (A' ++ B) := by simp
    rw [h3] at h2
    have h4 := adj_core n a d ha ρ htrans hnum ε hε hgap pre (A' ++ B) y x h2.1 h2.2
      (hA y (List.mem_cons_self))
    have h5 : pre ++ x :: ((y :: A') ++ B) = pre ++ x :: y :: (A' ++ B) := by simp
    rw [h5]; exact h4

open MooreLateJobs.Shared in
lemma sort_core (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k) :
    ∀ (m : ℕ) (L pre : List (Fin n)), L.length = m →
      (LawlerPrec.MinMax.IsFeasible ρ Finset.univ (pre ++ L) ∧
        ∀ j, completionTime a (pre ++ L) j ≤ d j) →
      ∃ L' : List (Fin n), L'.Perm L ∧
        L'.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y) ∧
        (LawlerPrec.MinMax.IsFeasible ρ Finset.univ (pre ++ L') ∧
          ∀ j, completionTime a (pre ++ L') j ≤ d j) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro L pre hlen h
    cases L with
    | nil => exact ⟨[], List.Perm.refl _, List.Pairwise.nil, h⟩
    | cons z Z =>
      have hne : (z :: Z).toFinset.Nonempty := ⟨z, by simp⟩
      obtain ⟨x, hxs, hmin⟩ := Finset.exists_min_image (z :: Z).toFinset
        (modifiedDeadline ρ d ε) hne
      have hxL : x ∈ z :: Z := by simpa using hxs
      obtain ⟨A, B, hAB⟩ := List.append_of_mem hxL
      have hnd : (pre ++ (z :: Z)).Nodup := h.1.1.1
      have hnd2 : (z :: Z).Nodup := (List.nodup_append.1 hnd).2.1
      rw [hAB] at hnd2 hlen h
      have hxA : x ∉ A := by
        intro hx; simp [List.nodup_append] at hnd2; grind
      have hxB : x ∉ B := by
        intro hx; simp [List.nodup_append] at hnd2; grind
      have hlt : ∀ y ∈ A ++ B, modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y := by
        intro y hy
        have hyx : y ≠ x := by
          rintro rfl; simp at hy; grind
        have hy' : y ∈ (z :: Z).toFinset := by
          rw [hAB]; simp at hy ⊢; grind
        refine lt_of_le_of_ne (hmin y hy') ?_
        intro e; exact hyx (lm_inj d ρ ε hε hgap _ _ e).symm
      have hmv := move_front n a d ha ρ htrans hnum ε hε hgap x A pre B
        (fun y hy => hlt y (List.mem_append_left _ hy)) h
      have hlen2 : (A ++ B).length < m := by
        rw [← hlen]; simp
      rw [← List.cons_append] at hmv
      have hmv2 : (pre ++ [x]) ++ (A ++ B) = pre ++ x :: (A ++ B) := by simp
      obtain ⟨L', hp, hs, hP⟩ := ih _ hlen2 (A ++ B) (pre ++ [x]) rfl
        (by rw [hmv2]; exact hmv)
      refine ⟨x :: L', ?_, ?_, ?_⟩
      · rw [hAB]
        exact (List.Perm.cons x hp).trans List.perm_middle.symm
      · refine List.Pairwise.cons ?_ hs
        intro y hy
        exact hlt y (hp.subset hy)
      · have : pre ++ x :: L' = (pre ++ [x]) ++ L' := by simp
        rw [this]; exact hP

open MooreLateJobs.Shared in
theorem lmA20_core (n : ℕ) (a d : Fin n → ℝ) (ha : ∀ j, 0 ≤ a j)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (hrefl : ∀ j, ρ j j)
    (hantisymm : ∀ i j, ρ i j → ρ j i → i = j)
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε) (hgap : ∀ k k', d k < d k' → (n : ℝ) * ε < d k' - d k)
    (l : List (Fin n)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hsorted : l.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y)) :
    (∃ l' : List (Fin n), LawlerPrec.MinMax.IsFeasible ρ Finset.univ l' ∧
        ∀ j, completionTime a l' j ≤ d j) ↔
      ∀ j, completionTime a l j ≤ d j := by
  constructor
  · rintro ⟨l', hf, hon⟩
    obtain ⟨L', hp, hs, hP⟩ := sort_core n a d ha ρ htrans hnum ε hε hgap _ l' [] rfl
      (by simpa using And.intro hf hon)
    have hperm : l.Perm l' := by
      rw [List.perm_ext_iff_of_nodup hl.1 hf.1.1]
      intro x; rw [hl.2, hf.1.2]
    have h2 : L'.Perm l := hp.trans hperm.symm
    have hL' : L' = l := by
      exact List.Perm.eq_of_pairwise (le := fun x y => modifiedDeadline ρ d ε x ≤ modifiedDeadline ρ d ε y)
        (fun x _ y _ h1 h2 => lm_inj d ρ ε hε hgap _ _ (le_antisymm h1 h2))
        (hs.imp (fun h => h.le)) (hsorted.imp (fun h => h.le)) h2
    subst hL'
    simpa using hP.2
  · intro h
    exact ⟨l, sorted_core n d ρ htrans hnum ε hε l hl hsorted, h⟩

end LawlerMoore.PrecDeadline

open LawlerMoore.PrecDeadline


theorem solution (n : ℕ) (d : Fin n → ℝ)
    (ρ : Fin n → Fin n → Prop) [DecidableRel ρ]
    (htrans : ∀ i j k, ρ i j → ρ j k → ρ i k)
    (hnum : ∀ i j, ρ i j → i ≤ j)
    (ε : ℝ) (hε : 0 < ε)
    (l : List (Fin n)) (hl : MooreLateJobs.Shared.IsSchedule Finset.univ l)
    (hsorted : l.Pairwise (fun x y => modifiedDeadline ρ d ε x < modifiedDeadline ρ d ε y)) :
    LawlerPrec.MinMax.IsFeasible ρ Finset.univ l := by
  exact sorted_core n d ρ htrans hnum ε hε l hl hsorted
