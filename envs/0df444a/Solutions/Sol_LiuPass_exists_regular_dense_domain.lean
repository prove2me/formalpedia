-- Prove2me | solution 1 for LiuPass.exists_regular_dense_domain
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T09:36:36.861435+00:00
-- url     : https://prove2.me/submissions/f532c699-abc1-473c-b79a-3e4e964e0015

import Mathlib
import Definitions.Def_LiuPass_crypto

set_option autoImplicit false

open scoped Classical

/-- size of the full fibre of `f` through `x` among `n`-bit strings -/
noncomputable def lpRD_fib (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) (x : LiuPass.BitStr) : ℕ :=
  (Finset.univ.filter fun v : Fin n → Bool => f (List.ofFn v) = f x).card

/-- the regularity class of a fibre size -/
def lpRD_cls (s : ℕ) : ℕ := max 1 (Nat.clog 2 s)

theorem lpRD_cls_bounds (s : ℕ) (hs : 1 ≤ s) :
    2 ^ (lpRD_cls s - 1) ≤ s ∧ s ≤ 2 ^ lpRD_cls s := by
  unfold lpRD_cls
  constructor
  · by_cases h : Nat.clog 2 s ≤ 1
    · rw [max_eq_left h]; simpa using hs
    · rw [not_le] at h
      rw [max_eq_right h.le]
      have hs1 : 1 < s := by
        by_contra hc
        rw [not_lt] at hc
        have : s = 1 := by omega
        subst this
        simp at h
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hs1
      rw [Nat.pred_eq_sub_one] at this
      exact this.le
  · calc s ≤ 2 ^ Nat.clog 2 s := Nat.le_pow_clog (by norm_num) s
      _ ≤ 2 ^ max 1 (Nat.clog 2 s) := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)

theorem lpRD_cls_mem (n s : ℕ) (hn : 0 < n) (hs : s ≤ 2 ^ n) :
    lpRD_cls s ∈ Finset.Icc 1 n := by
  unfold lpRD_cls
  rw [Finset.mem_Icc]
  refine ⟨le_max_left _ _, max_le hn ?_⟩
  exact Nat.clog_le_of_le_pow hs

theorem lpRD_fib_le (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) (x : LiuPass.BitStr) :
    lpRD_fib f n x ≤ 2 ^ n := by
  unfold lpRD_fib
  calc _ ≤ (Finset.univ : Finset (Fin n → Bool)).card := Finset.card_filter_le _ _
    _ = 2 ^ n := by simp

theorem lpRD_exists_v (n : ℕ) (x : LiuPass.BitStr) (hx : x.length = n) :
    ∃ v : Fin n → Bool, List.ofFn v = x := by
  subst hx
  exact ⟨x.get, List.ofFn_get x⟩

theorem lpRD_fib_pos (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) (x : LiuPass.BitStr)
    (hx : x.length = n) : 1 ≤ lpRD_fib f n x := by
  obtain ⟨v, hv⟩ := lpRD_exists_v n x hx
  unfold lpRD_fib
  apply Finset.card_pos.mpr
  exact ⟨v, by simp [hv]⟩

theorem lpRD_fib_congr (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) (x y : LiuPass.BitStr)
    (h : f y = f x) : lpRD_fib f n y = lpRD_fib f n x := by
  unfold lpRD_fib
  rw [h]

theorem lpRD_pigeon (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) (hn : 0 < n) :
    ∃ r ∈ Finset.Icc 1 n, (2 : ℝ) ^ n / (n : ℝ) ≤
      ((Finset.univ.filter fun v : Fin n → Bool =>
        lpRD_cls (lpRD_fib f n (List.ofFn v)) = r).card : ℝ) := by
  have hmaps : ∀ v ∈ (Finset.univ : Finset (Fin n → Bool)),
      lpRD_cls (lpRD_fib f n (List.ofFn v)) ∈ Finset.Icc 1 n :=
    fun v _ => lpRD_cls_mem n _ hn (lpRD_fib_le f n _)
  have hne : (Finset.Icc 1 n).Nonempty := ⟨1, by simp; omega⟩
  have hb : (Finset.Icc 1 n).card • ((2 : ℝ) ^ n / (n : ℝ)) ≤
      ((Finset.univ : Finset (Fin n → Bool)).card : ℝ) := by
    rw [nsmul_eq_mul]
    simp only [Nat.card_Icc, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin]
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [Nat.add_sub_cancel]
    push_cast
    rw [mul_div_cancel₀ _ hn']
  exact Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to hmaps hne hb

noncomputable def lpRD_r (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) : ℕ :=
  if h : 0 < n then Classical.choose (lpRD_pigeon f n h) else 0

def lpRD_S (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) (x : LiuPass.BitStr) : Prop :=
  x.length = n ∧ lpRD_cls (lpRD_fib f n x) = lpRD_r f n

theorem lpRD_density (f : LiuPass.BitStr → LiuPass.BitStr) (n : ℕ) (hn : 0 < n) :
    (2 : ℝ) ^ n / (n : ℝ) ≤
      ((Finset.univ.filter fun v : Fin n → Bool => lpRD_S f n (List.ofFn v)).card : ℝ) := by
  have hspec := (Classical.choose_spec (lpRD_pigeon f n hn)).2
  have hr : lpRD_r f n = Classical.choose (lpRD_pigeon f n hn) := by
    unfold lpRD_r; rw [dif_pos hn]
  have heq : (Finset.univ.filter fun v : Fin n → Bool => lpRD_S f n (List.ofFn v)) =
      (Finset.univ.filter fun v : Fin n → Bool =>
        lpRD_cls (lpRD_fib f n (List.ofFn v)) = Classical.choose (lpRD_pigeon f n hn)) := by
    apply Finset.filter_congr
    intro v _
    simp [lpRD_S, hr]
  rw [heq]
  exact hspec

theorem lpRD_regular (f : LiuPass.BitStr → LiuPass.BitStr) :
    LiuPass.IsRegularOver (lpRD_S f) f (lpRD_r f) := by
  refine ⟨0, fun n _ x hx hS => ?_⟩
  have hpc : LiuPass.preimageCard n (lpRD_S f n) f (f x) = lpRD_fib f n x := by
    unfold LiuPass.preimageCard lpRD_fib
    congr 1
    apply Finset.filter_congr
    intro v _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨⟨by simp, ?_⟩, h⟩
      rw [lpRD_fib_congr f n _ _ h]
      exact hS.2
  rw [hpc, ← hS.2]
  exact lpRD_cls_bounds _ (lpRD_fib_pos f n x hx)

theorem lpRD_prUnif₂_mono (n m : ℕ) (P Q : LiuPass.BitStr → LiuPass.BitStr → Prop)
    (h : ∀ x r, P x r → Q x r) : LiuPass.prUnif₂ n m P ≤ LiuPass.prUnif₂ n m Q := by
  unfold LiuPass.prUnif₂
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Finset.card_le_card (fun v hv => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    exact h _ _ hv)

theorem lpRD_prUnif₂_nonneg (n m : ℕ) (P : LiuPass.BitStr → LiuPass.BitStr → Prop) :
    0 ≤ LiuPass.prUnif₂ n m P := by
  unfold LiuPass.prUnif₂; positivity

open LiuPass Finset Classical in
theorem solution (U : UMachine) (f : BitStr → BitStr) (hf : IsOWF U f) :
    ∃ (r : ℕ → ℕ) (S : ℕ → BitStr → Prop),
      (∀ (n : ℕ) (x : BitStr), S n x → x.length = n) ∧
      (∀ n : ℕ, 0 < n →
        (2 : ℝ) ^ n / (n : ℝ) ≤
          ((univ.filter fun v : Fin n → Bool => S n (List.ofFn v)).card : ℝ)) ∧
      IsOWFOver U S f ∧ IsRegularOver S f r := by
  refine ⟨lpRD_r f, lpRD_S f, fun n x hx => hx.1, fun n hn => lpRD_density f n hn,
    ⟨hf.1, fun A => ?_⟩, lpRD_regular f⟩
  obtain ⟨mu, hmu, hbound⟩ := hf.2 A
  refine ⟨fun n => if n = 0 then invSuccOver U (lpRD_S f) f A 0 else (n : ℝ) * mu n, ?_, ?_⟩
  · intro k
    obtain ⟨n₀, hn₀⟩ := hmu (k + 1)
    refine ⟨max n₀ 1, fun n hn => ?_⟩
    have hn1 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < n := by positivity
    simp only [hn1, if_false]
    have h1 := hn₀ n (le_trans (le_max_left _ _) hn)
    calc (n : ℝ) * mu n ≤ (n : ℝ) * (1 / (n : ℝ) ^ (k + 1)) :=
          mul_le_mul_of_nonneg_left h1 hnpos.le
      _ = 1 / (n : ℝ) ^ k := by
          field_simp
          ring
  · intro n
    by_cases hn : n = 0
    · subst hn; simp
    · simp only [hn, if_false]
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn
      have hN : prUnif₂ n (A.tape n)
          (fun x r => lpRD_S f n x ∧ f (A.out r (U.pair (unary n) (f x))) = f x) ≤ mu n := by
        refine le_trans ?_ (hbound n)
        exact lpRD_prUnif₂_mono _ _ _ _ (fun x r h => h.2)
      have hN0 := lpRD_prUnif₂_nonneg n (A.tape n)
          (fun x r => lpRD_S f n x ∧ f (A.out r (U.pair (unary n) (f x))) = f x)
      have hD : 1 / (n : ℝ) ≤ prUnif n (lpRD_S f n) := by
        unfold prUnif
        have := lpRD_density f n hnpos
        rw [le_div_iff₀ (by positivity)]
        calc 1 / (n : ℝ) * 2 ^ n = 2 ^ n / (n : ℝ) := by ring
          _ ≤ _ := this
      have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hDpos : 0 < prUnif n (lpRD_S f n) := lt_of_lt_of_le (by positivity) hD
      unfold invSuccOver
      rw [div_le_iff₀ hDpos]
      have hmu0 : 0 ≤ mu n := le_trans hN0 hN
      have : 1 ≤ (n : ℝ) * prUnif n (lpRD_S f n) := by
        rw [div_le_iff₀ hnR] at hD
        linarith
      nlinarith
