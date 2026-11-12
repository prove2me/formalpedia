-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_A_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:20:38.443761+00:00
-- url     : https://prove2.me/submissions/6e763ab7-bb0d-4127-b5d6-d8002fcf3d60

import Mathlib
import Definitions.Def_MonoABPWidth_Hierarchy_simplicity

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy
namespace MonoABPWidth.Dev.Basic

noncomputable def peelEquiv {I J : Type} (F : I → Type) (k : I) (inj : J → I)
    (hinj : Function.Injective inj) (hne : ∀ j, inj j ≠ k) (hcov : ∀ i, i = k ∨ ∃ j, inj j = i) :
    (∀ i, F i) ≃ F k × ∀ j, F (inj j) := by
  classical
  let e : J ≃ {i : I // i ≠ k} :=
    Equiv.ofBijective (fun j => ⟨inj j, hne j⟩)
      ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨i, hi⟩ => by
        rcases hcov i with h | ⟨j, hj⟩
        · exact absurd h hi
        · exact ⟨j, Subtype.ext hj⟩⟩
  exact (Equiv.piSplitAt k F).trans
    (Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrLeft (fun i : {i : I // i ≠ k} => F i) e).symm)

theorem peelEquiv_apply {I J : Type} (F : I → Type) (k : I) (inj : J → I)
    (hinj : Function.Injective inj) (hne : ∀ j, inj j ≠ k) (hcov : ∀ i, i = k ∨ ∃ j, inj j = i)
    (p : ∀ i, F i) : peelEquiv F k inj hinj hne hcov p = (p k, fun j => p (inj j)) := by
  unfold peelEquiv
  simp only [Equiv.trans_apply, Equiv.piSplitAt_apply]
  refine Prod.ext rfl ?_
  funext j
  rfl

theorem sum_peel {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] {R : Type} [AddCommMonoid R]
    (L : I → ℕ) (k : I) (inj : J → I)
    (hinj : Function.Injective inj) (hne : ∀ j, inj j ≠ k) (hcov : ∀ i, i = k ∨ ∃ j, inj j = i)
    (f : (∀ i, Fin (L i)) → R) (g : Fin (L k) → (∀ j, Fin (L (inj j))) → R)
    (h : ∀ p, f p = g (p k) (fun j => p (inj j))) :
    ∑ p, f p = ∑ x, ∑ q, g x q := by
  rw [← Fintype.sum_prod_type' (fun x q => g x q)]
  exact Fintype.sum_equiv (peelEquiv (fun i => Fin (L i)) k inj hinj hne hcov) f (fun y => g y.1 y.2)
    (fun p => by rw [peelEquiv_apply]; exact h p)

abbrev Sub {σ : Type} (A : MABP σ) (a b : Fin (A.depth + 1)) :=
  {i : Fin (A.depth + 1) // a ≤ i ∧ i ≤ b}

noncomputable def term {σ : Type} (A : MABP σ) (a b : Fin (A.depth + 1))
    (p : (i : Sub A a b) → Fin (A.layerSize i.val)) : MvPolynomial σ ℝ :=
  ∏ e : Fin A.depth,
    if he : a.val ≤ e.val ∧ e.val < b.val then
      (A.label e (p ⟨e.castSucc, ⟨he.1, Nat.le_of_lt he.2⟩⟩)
        (p ⟨e.succ, ⟨Nat.le_succ_of_le he.1, he.2⟩⟩)).poly
    else 1

theorem seg_eq {σ : Type} (A : MABP σ) (a b : Fin (A.depth + 1)) (hab : a ≤ b)
    (u : Fin (A.layerSize a)) (v : Fin (A.layerSize b)) :
    A.segment a b u v = ∑ p : (i : Sub A a b) → Fin (A.layerSize i.val),
      if p ⟨a, le_rfl, hab⟩ = u ∧ p ⟨b, hab, le_rfl⟩ = v then term A a b p else 0 := by
  classical
  unfold MABP.segment
  rw [dif_pos hab]
  rfl


section
variable {σ : Type} (A : MABP σ)

theorem cs_le_succ (e : Fin A.depth) : e.castSucc ≤ e.succ := by
  rw [Fin.le_def]; simp

def injR (a : Fin (A.depth + 1)) (e : Fin A.depth) : Sub A a e.castSucc → Sub A a e.succ :=
  fun j => ⟨j.1, j.2.1, le_trans j.2.2 (cs_le_succ A e)⟩

def injL (b : Fin (A.depth + 1)) (e : Fin A.depth) : Sub A e.succ b → Sub A e.castSucc b :=
  fun j => ⟨j.1, le_trans (cs_le_succ A e) j.2.1, j.2.2⟩

theorem term_succ (a : Fin (A.depth + 1)) (e : Fin A.depth) (ha : a ≤ e.castSucc)
    (p : (i : Sub A a e.succ) → Fin (A.layerSize i.val)) :
    term A a e.succ p = term A a e.castSucc (fun j => p (injR A a e j)) *
      (A.label e (p ⟨e.castSucc, ha, cs_le_succ A e⟩) (p ⟨e.succ, le_trans ha (cs_le_succ A e), le_rfl⟩)).poly := by
  unfold term
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ (fun e' : Fin A.depth => if he : a.val ≤ e'.val ∧ e'.val < (e.castSucc).val then
      (A.label e' ((fun j => p (injR A a e j)) ⟨e'.castSucc, ⟨he.1, Nat.le_of_lt he.2⟩⟩)
        ((fun j => p (injR A a e j)) ⟨e'.succ, ⟨Nat.le_succ_of_le he.1, he.2⟩⟩)).poly
    else 1) (Finset.mem_univ e)]
  have h1 : ¬ (a.val ≤ e.val ∧ e.val < (e.castSucc).val) := by simp
  have h2 : a.val ≤ e.val ∧ e.val < (e.succ).val := ⟨by simpa [Fin.le_def] using ha, by simp⟩
  rw [dif_neg h1, dif_pos h2, one_mul, mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro e' he'
  have hne : e' ≠ e := Finset.ne_of_mem_erase he'
  have hne' : e'.val ≠ e.val := fun h => hne (Fin.ext h)
  by_cases c : a.val ≤ e'.val ∧ e'.val < (e.castSucc).val
  · have c' : a.val ≤ e'.val ∧ e'.val < (e.succ).val := ⟨c.1, by simp at c ⊢; omega⟩
    rw [dif_pos c, dif_pos c']
    rfl
  · have c' : ¬ (a.val ≤ e'.val ∧ e'.val < (e.succ).val) := by
      simp at c ⊢; omega
    rw [dif_neg c, dif_neg c']

theorem term_pred (b : Fin (A.depth + 1)) (e : Fin A.depth) (hb : e.succ ≤ b)
    (p : (i : Sub A e.castSucc b) → Fin (A.layerSize i.val)) :
    term A e.castSucc b p =
      (A.label e (p ⟨e.castSucc, le_rfl, le_trans (cs_le_succ A e) hb⟩) (p ⟨e.succ, cs_le_succ A e, hb⟩)).poly *
      term A e.succ b (fun j => p (injL A b e j)) := by
  unfold term
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e),
    ← Finset.mul_prod_erase Finset.univ (fun e' : Fin A.depth => if he : (e.succ).val ≤ e'.val ∧ e'.val < b.val then
      (A.label e' ((fun j => p (injL A b e j)) ⟨e'.castSucc, ⟨he.1, Nat.le_of_lt he.2⟩⟩)
        ((fun j => p (injL A b e j)) ⟨e'.succ, ⟨Nat.le_succ_of_le he.1, he.2⟩⟩)).poly
    else 1) (Finset.mem_univ e)]
  have h1 : ¬ ((e.succ).val ≤ e.val ∧ e.val < b.val) := by simp
  have h2 : (e.castSucc).val ≤ e.val ∧ e.val < b.val := ⟨by simp, by simpa [Fin.le_def] using hb⟩
  rw [dif_neg h1, dif_pos h2, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro e' he'
  have hne : e' ≠ e := Finset.ne_of_mem_erase he'
  have hne' : e'.val ≠ e.val := fun h => hne (Fin.ext h)
  by_cases c : (e.succ).val ≤ e'.val ∧ e'.val < b.val
  · have c' : (e.castSucc).val ≤ e'.val ∧ e'.val < b.val := ⟨by simp at c ⊢; omega, c.2⟩
    rw [dif_pos c, dif_pos c']
    rfl
  · have c' : ¬ ((e.castSucc).val ≤ e'.val ∧ e'.val < b.val) := by
      simp at c ⊢; omega
    rw [dif_neg c, dif_neg c']

theorem term_self (a : Fin (A.depth + 1)) (p : (i : Sub A a a) → Fin (A.layerSize i.val)) :
    term A a a p = 1 := by
  unfold term
  apply Finset.prod_eq_one
  intro e _
  rw [dif_neg]
  omega

theorem seg_self (a : Fin (A.depth + 1)) (u v : Fin (A.layerSize a)) :
    A.segment a a u v = if u = v then 1 else 0 := by
  classical
  rw [seg_eq A a a le_rfl]
  let inj : Empty → Sub A a a := fun j => nomatch j
  have hinj : Function.Injective inj := fun x => nomatch x
  have hne : ∀ j, inj j ≠ ⟨a, le_rfl, le_rfl⟩ := fun j => nomatch j
  have hcov : ∀ i : Sub A a a, i = ⟨a, le_rfl, le_rfl⟩ ∨ ∃ j, inj j = i :=
    fun i => Or.inl (Subtype.ext (le_antisymm i.2.2 i.2.1))
  rw [sum_peel (fun i : Sub A a a => A.layerSize i.val) ⟨a, le_rfl, le_rfl⟩ inj hinj hne hcov _
    (fun x _ => if x = u ∧ x = v then (1 : MvPolynomial σ ℝ) else 0)]
  · by_cases h : u = v
    · subst h; simp
    · simp [h]
  · intro p
    rw [term_self]

theorem seg_R (a : Fin (A.depth + 1)) (e : Fin A.depth) (ha : a ≤ e.castSucc)
    (u : Fin (A.layerSize a)) (w : Fin (A.layerSize e.succ)) :
    A.segment a e.succ u w =
      ∑ v : Fin (A.layerSize e.castSucc), A.segment a e.castSucc u v * (A.label e v w).poly := by
  classical
  have hs : a ≤ e.succ := le_trans ha (cs_le_succ A e)
  rw [seg_eq A a e.succ hs]
  simp only [seg_eq A a e.castSucc ha, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hinj : Function.Injective (injR A a e) := fun x y h => Subtype.ext (by have := congrArg Subtype.val h; exact this)
  have hne : ∀ j, injR A a e j ≠ ⟨e.succ, hs, le_rfl⟩ := by
    intro j h
    have := congrArg (fun x : Sub A a e.succ => x.1.val) h
    have h2 := j.2.2
    simp [injR, Fin.le_def] at this h2
    omega
  have hcov : ∀ i : Sub A a e.succ, i = ⟨e.succ, hs, le_rfl⟩ ∨ ∃ j, injR A a e j = i := by
    intro i
    by_cases h : i.1 = e.succ
    · exact Or.inl (Subtype.ext h)
    · right
      refine ⟨⟨i.1, i.2.1, ?_⟩, Subtype.ext rfl⟩
      have h1 := i.2.2
      rw [Fin.le_def] at h1 ⊢
      have h3 : i.1.val ≠ e.succ.val := fun h' => h (Fin.ext h')
      simp at h1 h3 ⊢
      omega
  rw [sum_peel (fun i : Sub A a e.succ => A.layerSize i.val) ⟨e.succ, hs, le_rfl⟩ (injR A a e) hinj hne hcov _
    (fun x q => if x = w then (if q ⟨a, le_rfl, ha⟩ = u then term A a e.castSucc q else 0) *
      (A.label e (q ⟨e.castSucc, ha, le_rfl⟩) x).poly else 0)]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    symm
    refine (Finset.sum_eq_single (q ⟨e.castSucc, ha, le_rfl⟩) ?_ ?_).trans ?_
    · intro v _ hv
      rw [if_neg (fun h => hv h.2.symm), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · by_cases hq : q ⟨a, le_rfl, ha⟩ = u
      · rw [if_pos ⟨hq, rfl⟩]
        symm
        refine (Finset.sum_eq_single w ?_ ?_).trans ?_
        · intro x _ hx
          rw [if_neg hx]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · rw [if_pos rfl, if_pos hq]
      · rw [if_neg (fun h => hq h.1)]
        symm
        refine (Finset.sum_eq_single w ?_ ?_).trans ?_
        · intro x _ hx
          rw [if_neg hx]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · rw [if_pos rfl, if_neg hq, zero_mul]
  · intro p
    by_cases h1 : p ⟨e.succ, hs, le_rfl⟩ = w
    · by_cases h2 : p ⟨a, le_rfl, hs⟩ = u
      · rw [if_pos ⟨h2, h1⟩, term_succ A a e ha p]
        dsimp only [injR]
        rw [if_pos h1]
        congr 1
        exact (if_pos h2).symm
      · rw [if_neg (fun h => h2 h.1)]
        dsimp only [injR]
        rw [if_pos h1]
        symm
        refine mul_eq_zero_of_left ?_ _
        exact if_neg h2
    · rw [if_neg (fun h => h1 h.2)]
      dsimp only [injR]
      rw [if_neg h1]

theorem seg_L (e : Fin A.depth) (b : Fin (A.depth + 1)) (hb : e.succ ≤ b)
    (u : Fin (A.layerSize e.castSucc)) (w : Fin (A.layerSize b)) :
    A.segment e.castSucc b u w =
      ∑ v : Fin (A.layerSize e.succ), (A.label e u v).poly * A.segment e.succ b v w := by
  classical
  have hs : e.castSucc ≤ b := le_trans (cs_le_succ A e) hb
  rw [seg_eq A e.castSucc b hs]
  simp only [seg_eq A e.succ b hb, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinj : Function.Injective (injL A b e) := fun x y h => Subtype.ext (by have := congrArg Subtype.val h; exact this)
  have hne : ∀ j, injL A b e j ≠ ⟨e.castSucc, le_rfl, hs⟩ := by
    intro j h
    have := congrArg (fun x : Sub A e.castSucc b => x.1.val) h
    have h2 := j.2.1
    simp [injL, Fin.le_def] at this h2
    omega
  have hcov : ∀ i : Sub A e.castSucc b, i = ⟨e.castSucc, le_rfl, hs⟩ ∨ ∃ j, injL A b e j = i := by
    intro i
    by_cases h : i.1 = e.castSucc
    · exact Or.inl (Subtype.ext h)
    · right
      refine ⟨⟨i.1, ?_, i.2.2⟩, Subtype.ext rfl⟩
      have h1 := i.2.1
      rw [Fin.le_def] at h1 ⊢
      have h3 : i.1.val ≠ e.castSucc.val := fun h' => h (Fin.ext h')
      simp at h1 h3 ⊢
      omega
  rw [sum_peel (fun i : Sub A e.castSucc b => A.layerSize i.val) ⟨e.castSucc, le_rfl, hs⟩ (injL A b e) hinj hne hcov _
    (fun x q => if x = u then (if q ⟨b, hb, le_rfl⟩ = w then
      (A.label e x (q ⟨e.succ, le_rfl, hb⟩)).poly * term A e.succ b q else 0) else 0)]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q _
    symm
    refine (Finset.sum_eq_single (q ⟨e.succ, le_rfl, hb⟩) ?_ ?_).trans ?_
    · intro v _ hv
      rw [if_neg (fun h => hv h.1.symm), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
    · by_cases hq : q ⟨b, hb, le_rfl⟩ = w
      · rw [if_pos ⟨rfl, hq⟩]
        symm
        refine (Finset.sum_eq_single u ?_ ?_).trans ?_
        · intro x _ hx
          rw [if_neg hx]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · rw [if_pos rfl, if_pos hq]
      · rw [if_neg (fun h => hq h.2), mul_zero]
        symm
        refine (Finset.sum_eq_single u ?_ ?_).trans ?_
        · intro x _ hx
          rw [if_neg hx]
        · intro h
          exact absurd (Finset.mem_univ _) h
        · rw [if_pos rfl, if_neg hq]
  · intro p
    by_cases h1 : p ⟨e.castSucc, le_rfl, hs⟩ = u
    · by_cases h2 : p ⟨b, hs, le_rfl⟩ = w
      · rw [if_pos ⟨h1, h2⟩, term_pred A b e hb p]
        dsimp only [injL]
        rw [if_pos h1]
        exact (if_pos h2).symm
      · rw [if_neg (fun h => h2 h.2)]
        dsimp only [injL]
        rw [if_pos h1]
        exact (if_neg h2).symm
    · rw [if_neg (fun h => h1 h.1)]
      dsimp only [injL]
      rw [if_neg h1]

theorem fin_src (x y : Fin (A.layerSize 0)) : x = y := by
  apply Fin.ext
  have h1 := x.2
  have h2 := y.2
  have h3 := A.source_singleton
  omega

theorem fin_snk (x y : Fin (A.layerSize (Fin.last A.depth))) : x = y := by
  apply Fin.ext
  have h1 := x.2
  have h2 := y.2
  have h3 := A.sink_singleton
  omega

def e0 : Fin (A.depth + 1) ≃ Sub A 0 (Fin.last A.depth) where
  toFun i := ⟨i, Fin.zero_le _, Fin.le_last _⟩
  invFun j := j.1
  left_inv _ := rfl
  right_inv _ := rfl

theorem output_eq_seg : A.output = A.segment 0 (Fin.last A.depth) A.source A.sink := by
  classical
  rw [seg_eq A 0 (Fin.last A.depth) (Fin.zero_le _)]
  unfold MABP.output
  refine Fintype.sum_equiv (Equiv.piCongrLeft (fun j : Sub A 0 (Fin.last A.depth) => Fin (A.layerSize j.val)) (e0 A)) _ _ ?_
  intro p
  rw [if_pos ⟨fin_src A _ _, fin_snk A _ _⟩]
  unfold term
  apply Finset.prod_congr rfl
  intro e _
  rw [dif_pos ⟨Nat.zero_le _, by simp⟩]
  have key : ∀ i, (Equiv.piCongrLeft (fun j : Sub A 0 (Fin.last A.depth) => Fin (A.layerSize j.val)) (e0 A) p) (e0 A i) = p i :=
    fun i => Equiv.piCongrLeft_apply_apply _ _ _ i
  show _ = (A.label e ((Equiv.piCongrLeft (fun j : Sub A 0 (Fin.last A.depth) => Fin (A.layerSize j.val)) (e0 A) p) (e0 A e.castSucc))
    ((Equiv.piCongrLeft (fun j : Sub A 0 (Fin.last A.depth) => Fin (A.layerSize j.val)) (e0 A) p) (e0 A e.succ))).poly
  rw [key, key]

theorem prefix_zero (v : Fin (A.layerSize 0)) : A.prefix 0 v = 1 := by
  unfold MABP.prefix
  rw [seg_self, if_pos (fin_src A _ _)]

theorem suffix_last (v : Fin (A.layerSize (Fin.last A.depth))) :
    A.suffix (Fin.last A.depth) v = 1 := by
  unfold MABP.suffix
  rw [seg_self, if_pos (fin_snk A _ _)]

theorem prefix_succ (e : Fin A.depth) (w : Fin (A.layerSize e.succ)) :
    A.prefix e.succ w = ∑ v : Fin (A.layerSize e.castSucc), A.prefix e.castSucc v * (A.label e v w).poly := by
  unfold MABP.prefix
  exact seg_R A 0 e (Fin.zero_le _) _ _

theorem suffix_castSucc (e : Fin A.depth) (u : Fin (A.layerSize e.castSucc)) :
    A.suffix e.castSucc u = ∑ w : Fin (A.layerSize e.succ), (A.label e u w).poly * A.suffix e.succ w := by
  unfold MABP.suffix
  exact seg_L A e (Fin.last _) (Fin.le_last _) _ _

theorem sum_prefix_suffix (i : Fin (A.depth + 1)) :
    ∑ v : Fin (A.layerSize i), A.prefix i v * A.suffix i v = A.output := by
  induction i using Fin.induction with
  | zero =>
    rw [Finset.sum_eq_single A.source]
    · rw [prefix_zero, one_mul, output_eq_seg]
      rfl
    · intro b _ hb
      exact absurd (fin_src A _ _) hb
    · intro h
      exact absurd (Finset.mem_univ _) h
  | succ i ih =>
    rw [← ih]
    simp only [prefix_succ, suffix_castSucc, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro v _
    apply Finset.sum_congr rfl
    intro w _
    ring

theorem output_eq_edges (e : Fin A.depth) :
    A.output = ∑ u : Fin (A.layerSize e.castSucc), ∑ v : Fin (A.layerSize e.succ),
      A.prefix e.castSucc u * (A.label e u v).poly * A.suffix e.succ v := by
  rw [← sum_prefix_suffix A e.castSucc]
  apply Finset.sum_congr rfl
  intro u _
  rw [suffix_castSucc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring
end

section Mono
variable {σ : Type}

theorem mono_C (c : ℝ) (hc : 0 ≤ c) : MonotonePolynomial (MvPolynomial.C c : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C]
  split_ifs <;> simp [hc]

theorem mono_one : MonotonePolynomial (1 : MvPolynomial σ ℝ) := by
  have := mono_C (σ := σ) 1 zero_le_one
  simpa using this

theorem mono_X (x : σ) : MonotonePolynomial (MvPolynomial.X x : MvPolynomial σ ℝ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_X']
  split_ifs <;> simp

theorem mono_add {p q : MvPolynomial σ ℝ} (hp : MonotonePolynomial p) (hq : MonotonePolynomial q) :
    MonotonePolynomial (p + q) := by
  intro m
  rw [MvPolynomial.coeff_add]
  exact add_nonneg (hp m) (hq m)

theorem mono_mul {p q : MvPolynomial σ ℝ} (hp : MonotonePolynomial p) (hq : MonotonePolynomial q) :
    MonotonePolynomial (p * q) := by
  classical
  intro m
  rw [MvPolynomial.coeff_mul]
  exact Finset.sum_nonneg (fun x _ => mul_nonneg (hp _) (hq _))

theorem mono_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, MonotonePolynomial (f i)) : MonotonePolynomial (∑ i ∈ s, f i) := by
  intro m
  rw [MvPolynomial.coeff_sum]
  exact Finset.sum_nonneg (fun i hi => h i hi m)

theorem mono_label (l : AffineLabel σ) : MonotonePolynomial l.poly := by
  unfold AffineLabel.poly
  refine mono_add (mono_C _ (by positivity)) ?_
  unfold Finsupp.sum
  exact mono_sum _ _ (fun x _ => mono_mul (mono_C _ (by positivity)) (mono_X x))

theorem support_nonempty_of_ne_zero {p : MvPolynomial σ ℝ} (h : p ≠ 0) : ∃ m, m ∈ p.support := by
  by_contra hc
  push_neg at hc
  apply h
  ext m
  have := hc m
  rw [MvPolynomial.mem_support_iff] at this
  simpa using this

theorem mem_support_sum_of_mono {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, MonotonePolynomial (f i)) (m : σ →₀ ℕ) :
    m ∈ (∑ i ∈ s, f i).support ↔ ∃ i ∈ s, m ∈ (f i).support := by
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]
  constructor
  · intro hne
    by_contra hc
    push_neg at hc
    exact hne (Finset.sum_eq_zero hc)
  · rintro ⟨i, hi, hne⟩
    have hpos : 0 < MvPolynomial.coeff m (f i) := lt_of_le_of_ne (h i hi m) (Ne.symm hne)
    have := Finset.single_le_sum (f := fun i => MvPolynomial.coeff m (f i))
      (fun j hj => h j hj m) hi
    exact ne_of_gt (lt_of_lt_of_le hpos this)

theorem mem_support_mul_of_mono {p q : MvPolynomial σ ℝ} (hp : MonotonePolynomial p)
    (hq : MonotonePolynomial q) (m : σ →₀ ℕ) :
    m ∈ (p * q).support ↔ ∃ a ∈ p.support, ∃ b ∈ q.support, a + b = m := by
  classical
  constructor
  · intro h
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul] at h
    obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    refine ⟨x.1, ?_, x.2, ?_, hx⟩
    · rw [MvPolynomial.mem_support_iff]; exact left_ne_zero_of_mul hne
    · rw [MvPolynomial.mem_support_iff]; exact right_ne_zero_of_mul hne
  · rintro ⟨a, ha, b, hb, rfl⟩
    rw [MvPolynomial.mem_support_iff] at ha hb ⊢
    rw [MvPolynomial.coeff_mul]
    have hpos : 0 < MvPolynomial.coeff a p * MvPolynomial.coeff b q :=
      mul_pos (lt_of_le_of_ne (hp a) (Ne.symm ha)) (lt_of_le_of_ne (hq b) (Ne.symm hb))
    have := Finset.single_le_sum (f := fun x : (σ →₀ ℕ) × (σ →₀ ℕ) =>
      MvPolynomial.coeff x.1 p * MvPolynomial.coeff x.2 q)
      (fun x _ => mul_nonneg (hp _) (hq _)) (Finset.HasAntidiagonal.mem_antidiagonal.2 (rfl : (a, b).1 + (a, b).2 = a + b))
    exact ne_of_gt (lt_of_lt_of_le hpos this)

end Mono

section Mono2
variable {σ : Type} (A : MABP σ)

theorem prefix_mono (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) : MonotonePolynomial (A.prefix i v) := by
  induction i using Fin.induction with
  | zero => rw [prefix_zero]; exact mono_one
  | succ i ih =>
    rw [prefix_succ]
    exact mono_sum _ _ (fun u _ => mono_mul (ih u) (mono_label _))

theorem suffix_mono (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) : MonotonePolynomial (A.suffix i v) := by
  induction i using Fin.reverseInduction with
  | last => rw [suffix_last]; exact mono_one
  | cast i ih =>
    rw [suffix_castSucc]
    exact mono_sum _ _ (fun u _ => mono_mul (mono_label _) (ih u))

theorem vertex_support_subset (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) (m : σ →₀ ℕ)
    (hm : m ∈ (A.prefix i v * A.suffix i v).support) : m ∈ A.output.support := by
  rw [← sum_prefix_suffix A i, mem_support_sum_of_mono _ _
    (fun u _ => mono_mul (prefix_mono A _ u) (suffix_mono A _ u))]
  exact ⟨v, Finset.mem_univ _, hm⟩

theorem edge_support_subset (e : Fin A.depth) (u : Fin (A.layerSize e.castSucc))
    (v : Fin (A.layerSize e.succ)) (m : σ →₀ ℕ)
    (hm : m ∈ (A.prefix e.castSucc u * (A.label e u v).poly * A.suffix e.succ v).support) :
    m ∈ A.output.support := by
  have hmono : ∀ u v, MonotonePolynomial
      (A.prefix e.castSucc u * (A.label e u v).poly * A.suffix e.succ v) :=
    fun u v => mono_mul (mono_mul (prefix_mono A _ u) (mono_label _)) (suffix_mono A _ v)
  rw [output_eq_edges A e, mem_support_sum_of_mono _ _
    (fun u _ => mono_sum _ _ (fun v _ => hmono u v))]
  refine ⟨u, Finset.mem_univ _, ?_⟩
  rw [mem_support_sum_of_mono _ _ (fun v _ => hmono u v)]
  exact ⟨v, Finset.mem_univ _, hm⟩

end Mono2
end MonoABPWidth.Dev.Basic
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.Basic2
open MonoABPWidth.Dev.Basic

variable {σ : Type}

end MonoABPWidth.Dev.Basic2
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.LA3
open MonoABPWidth.Dev.Basic

variable {σ : Type}

theorem isHom_of_support (p : MvPolynomial σ ℝ) (n : ℕ)
    (h : ∀ m ∈ p.support, m.degree = n) : p.IsHomogeneous n := by
  intro d hd
  have e : Finsupp.degree d = Finsupp.weight 1 d := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [← e]
  exact h d (MvPolynomial.mem_support_iff.2 hd)

theorem degree_of_isHom {p : MvPolynomial σ ℝ} {n : ℕ} (h : p.IsHomogeneous n) {m : σ →₀ ℕ}
    (hm : m ∈ p.support) : m.degree = n := by
  by_contra hc
  exact (MvPolynomial.mem_support_iff.1 hm) (h.coeff_eq_zero hc)

theorem hom_pair (P S : MvPolynomial σ ℝ) (hP : MonotonePolynomial P) (hS : MonotonePolynomial S)
    (hP0 : P ≠ 0) (hS0 : S ≠ 0) (q : ℕ) (hq : ∀ m ∈ (P * S).support, m.degree = q) :
    Homogeneous P ∧ Homogeneous S := by
  obtain ⟨a0, ha0⟩ := support_nonempty_of_ne_zero hP0
  obtain ⟨b0, hb0⟩ := support_nonempty_of_ne_zero hS0
  have key : ∀ a ∈ P.support, ∀ b ∈ S.support, a.degree + b.degree = q := by
    intro a ha b hb
    have := hq (a + b) ((mem_support_mul_of_mono hP hS _).2 ⟨a, ha, b, hb, rfl⟩)
    rw [map_add] at this
    exact this
  refine ⟨⟨q - b0.degree, isHom_of_support _ _ fun a ha => ?_⟩,
    ⟨q - a0.degree, isHom_of_support _ _ fun b hb => ?_⟩⟩
  · have := key a ha b0 hb0
    omega
  · have := key a0 ha0 b hb
    omega

theorem label_totalDegree_le (l : AffineLabel σ) : l.poly.totalDegree ≤ 1 := by
  unfold AffineLabel.poly
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]; omega
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun x _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

theorem hom_middle (P L S : MvPolynomial σ ℝ) (hP : MonotonePolynomial P) (hL : MonotonePolynomial L)
    (hS : MonotonePolynomial S)
    (hP0 : P ≠ 0) (hS0 : S ≠ 0) (q : ℕ) (hq : ∀ m ∈ (P * L * S).support, m.degree = q) :
    ∃ d, L.IsHomogeneous d := by
  obtain ⟨a0, ha0⟩ := support_nonempty_of_ne_zero hP0
  obtain ⟨b0, hb0⟩ := support_nonempty_of_ne_zero hS0
  refine ⟨q - a0.degree - b0.degree, isHom_of_support _ _ fun m hm => ?_⟩
  have h1 : a0 + m ∈ (P * L).support :=
    (mem_support_mul_of_mono hP hL _).2 ⟨a0, ha0, m, hm, rfl⟩
  have h2 : a0 + m + b0 ∈ (P * L * S).support :=
    (mem_support_mul_of_mono (mono_mul hP hL) hS _).2 ⟨_, h1, b0, hb0, rfl⟩
  have := hq _ h2
  rw [map_add, map_add] at this
  omega

end MonoABPWidth.Dev.LA3

namespace MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.LA3 in
theorem chk_lemma_A_3 {σ : Type} [Fintype σ] (A : MABP σ)
    (hrel : A.Relevant) (hhom : Homogeneous A.output) :
    (∀ (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)),
      Homogeneous (A.prefix i v) ∧ Homogeneous (A.suffix i v)) ∧
    (∀ (e : Fin A.depth) (u : Fin (A.layerSize e.castSucc))
      (v : Fin (A.layerSize e.succ)),
      ∃ q : ℕ, q ≤ 1 ∧ (A.label e u v).poly.IsHomogeneous q) := by
  obtain ⟨q, hq⟩ := hhom
  have hout : ∀ m ∈ A.output.support, m.degree = q := fun m hm => degree_of_isHom hq hm
  refine ⟨fun i v => ?_, fun e u v => ?_⟩
  · exact hom_pair _ _ (prefix_mono A i v) (suffix_mono A i v) (hrel i v).1 (hrel i v).2 q
      (fun m hm => hout m (vertex_support_subset A i v m hm))
  · by_cases h0 : (A.label e u v).poly = 0
    · exact ⟨0, zero_le_one, by rw [h0]; exact MvPolynomial.isHomogeneous_zero _ _ _⟩
    · obtain ⟨d, hd⟩ := hom_middle _ _ _ (prefix_mono A _ u) (mono_label _) (suffix_mono A _ v)
        (hrel _ u).1 (hrel _ v).2 q
        (fun m hm => hout m (edge_support_subset A e u v m hm))
      refine ⟨d, ?_, hd⟩
      rw [← hd.totalDegree h0]
      exact label_totalDegree_le _
end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_A_3 := @MonoABPWidth.Hierarchy.chk_lemma_A_3
