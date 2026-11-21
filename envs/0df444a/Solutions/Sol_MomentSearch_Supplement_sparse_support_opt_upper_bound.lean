-- Prove2me | solution 1 for MomentSearch.Supplement.sparse_support_opt_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-21T01:02:28.366999+00:00
-- url     : https://prove2.me/submissions/1caa9737-aca5-426e-b208-505bcc584689

import Mathlib
import Definitions.Def_MomentSearch_OPT

open Finset MomentSearch

private theorem interval_tree {a b : ℕ} (h : a ≤ b) : Nonempty (SearchTree a b) := by
  induction b with
  | zero =>
    obtain rfl : a = 0 := by omega
    exact ⟨.leaf 0⟩
  | succ b ih =>
    by_cases e : a = b+1
    · subst a; exact ⟨.leaf _⟩
    · exact ⟨.node (b+1) h le_rfl (by omega)
        (fun _ => (ih (by omega)).some) (fun z => (lt_irrefl _ z).elim)⟩

/-- An increasing list of fewer than 2^d marked positions admits depth d on every mark. -/
private theorem marked_tree (d a b m : ℕ) (hab : a ≤ b) (size : m < 2^d)
    (f : Fin m → ℕ) (inc : StrictMono f) (lo : ∀ i, a ≤ f i) (hi : ∀ i, f i ≤ b) :
    ∃ T : SearchTree a b, ∀ i, queries T (f i) ≤ d := by
  classical
  induction d generalizing a b m with
  | zero =>
    have : m = 0 := by simpa using size
    subst m
    exact ⟨(interval_tree hab).some, fun i => Fin.elim0 i⟩
  | succ d ih =>
    by_cases hm : m = 0
    · subst m; exact ⟨(interval_tree hab).some, fun i => Fin.elim0 i⟩
    by_cases e : a = b
    · subst b; exact ⟨.leaf _, by simp [queries]⟩
    let k := m / 2
    have hk : k < m := by dsimp [k]; omega
    let mid : Fin m := ⟨k,hk⟩
    let v := f mid
    have cap := size
    rw [pow_succ] at cap
    let l (i : Fin k) : Fin m := ⟨i.val,by omega⟩
    let r (i : Fin (m-k-1)) : Fin m := ⟨k+1+i.val,by omega⟩
    have hl (i : Fin k) : f (l i) < v := inc (show l i < mid from i.isLt)
    have hr (i : Fin (m-k-1)) : v < f (r i) := inc (by change k < k+1+i.val; omega)
    have L (hv : a < v) := ih a (v-1) k (by omega) (by dsimp [k]; omega)
      (fun i => f (l i)) (inc.comp (fun _ _ h => h)) (fun i => lo (l i))
      (fun i => by have := hl i; omega)
    have R (hv : v < b) := ih (v+1) b (m-k-1) (by omega) (by dsimp [k]; omega)
      (fun i => f (r i)) (inc.comp (fun i j h => by
        change k+1+i.val < k+1+j.val; exact Nat.add_lt_add_left h _))
      (fun i => hr i) (fun i => hi (r i))
    choose left hleft using L
    choose right hright using R
    refine ⟨.node v (lo mid) (hi mid) (lt_of_le_of_ne hab e) left right,fun i => ?_⟩
    rcases lt_trichotomy i.val k with h | h | h
    · let j : Fin k := ⟨i.val,h⟩
      have lt := hl j
      have idl : l j = i := Fin.ext rfl
      rw [idl] at lt
      have hv := (lo i).trans_lt lt
      have dep := hleft hv j
      change queries (left hv) (f (l j)) ≤ d at dep
      rw [idl] at dep
      simp only [queries,if_neg lt.ne,if_pos lt,dif_pos hv]
      omega
    · have eq : i = mid := Fin.ext h
      subst i
      simp [queries,v]
    · let j : Fin (m-k-1) := ⟨i.val-k-1,by have := i.isLt; omega⟩
      have idr : r j = i := Fin.ext (by change k+1+(i.val-k-1) = i.val; omega)
      have gt := hr j
      rw [idr] at gt
      have hv := gt.trans_le (hi i)
      have dep := hright hv j
      change queries (right hv) (f (r j)) ≤ d at dep
      rw [idr] at dep
      simp only [queries,if_neg gt.ne.symm,if_neg (not_lt_of_gt gt),dif_pos hv]
      omega

private theorem positive_queries {a b : ℕ} (T : SearchTree a b) (h : a < b) (t : ℕ) :
    1 ≤ queries T t := by
  cases T with
  | leaf a => omega
  | node v hav hvb hab l r =>
    simp only [queries]
    split
    · norm_num
    · split <;> split <;> omega

theorem solution {n q : ℕ} (hn : 2 ≤ n) (hq : 0 < q) (p : Fin n → ℝ)
    (hp : p ∈ stdSimplex ℝ (Fin n)) (hs : (Function.support p).ncard ≤ q) :
    0 < MomentSearch.OPT p ∧ MomentSearch.OPT p ≤ 1 + Real.logb 2 q := by
  classical
  let s := (Function.support p).toFinset
  have card : s.card ≤ q := by simpa [s, Set.ncard_eq_toFinset_card'] using hs
  let f := s.orderEmbOfFin rfl
  let d := Nat.log 2 q + 1
  obtain ⟨T,hT⟩ := marked_tree d 0 (n-1) s.card (Nat.zero_le _)
    (lt_of_le_of_lt card (Nat.lt_pow_succ_log_self (by decide) q))
    (fun i => (f i).val) (fun i j hij => f.strictMono hij) (fun _ => Nat.zero_le _)
    (fun i => by have := (f i).isLt; omega)
  have lower (S : Strategy n) : 1 ≤ cost p S := by
    calc
      1 = ∑ i, p i * 1 := by simpa using hp.2.symm
      _ ≤ _ := sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (by exact_mod_cast positive_queries S (by omega) i) (hp.1 i)
  let : Nonempty (Strategy n) := ⟨T⟩
  refine ⟨zero_lt_one.trans_le (le_ciInf lower), ?_⟩
  have opt : OPT p ≤ cost p T := ciInf_le ⟨1,by rintro _ ⟨S,rfl⟩; exact lower S⟩ T
  have upper : cost p T ≤ (d:ℝ) := by
    calc
      _ ≤ ∑ i, p i * (d:ℝ) := by
        apply sum_le_sum
        intro i _
        by_cases h : p i = 0
        · simp [h]
        · have mem : i ∈ s := by simpa [s] using h
          let j := (s.orderIsoOfFin rfl).symm ⟨i,mem⟩
          have eq : f j = i := congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i,mem⟩)
          have depth := hT j
          simp only [eq] at depth
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast depth) (hp.1 i)
      _ = _ := by rw [← sum_mul,hp.2,one_mul]
  apply (opt.trans upper).trans
  have logq := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ) < 2)
    (by exact_mod_cast hq : (1:ℝ) ≤ q))
  have floor_eq : ⌊Real.logb 2 (q:ℝ)⌋₊ = Nat.log 2 q := by simpa using Real.natFloor_logb_natCast 2 q
  rw [floor_eq] at logq
  dsimp [d]
  push_cast
  linarith
