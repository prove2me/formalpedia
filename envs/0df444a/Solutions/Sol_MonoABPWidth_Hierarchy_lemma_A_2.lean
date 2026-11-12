-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:05:35.352496+00:00
-- url     : https://prove2.me/submissions/d1981137-9fed-46d9-9d5c-ae383f2e2017

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

end Mono2
end MonoABPWidth.Dev.Basic
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.L45a

variable {σ : Type}

/-- weight of a full path -/
noncomputable def wt (A : MABP σ) (p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i)) : MvPolynomial σ ℝ :=
  ∏ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly

/-- restriction of `A` to allowed vertex sets -/
noncomputable def restr (A : MABP σ) (S : ∀ i, Finset (Fin (A.layerSize i)))
    (h0 : (S 0).card = 1) (hl : (S (Fin.last A.depth)).card = 1) : MABP σ where
  depth := A.depth
  layerSize i := (S i).card
  source_singleton := h0
  sink_singleton := hl
  label e u v := A.label e (((S e.castSucc).equivFin.symm u : Fin (A.layerSize e.castSucc)))
    (((S e.succ).equivFin.symm v : Fin (A.layerSize e.succ)))

theorem restr_output (A : MABP σ) (S : ∀ i, Finset (Fin (A.layerSize i)))
    (h0 : (S 0).card = 1) (hl : (S (Fin.last A.depth)).card = 1) :
    (restr A S h0 hl).output = ∑ p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i),
      if (∀ i, p i ∈ S i) then wt A p else 0 := by
  classical
  rw [← Finset.sum_filter]
  unfold MABP.output
  refine Finset.sum_bij (fun q _ i => (((S i).equivFin.symm (q i) : (S i)) : Fin (A.layerSize i))) ?_ ?_ ?_ ?_
  · intro q _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro i
    exact ((S i).equivFin.symm (q i)).2
  · intro q1 _ q2 _ h
    funext i
    have := congrFun h i
    have h2 := Subtype.ext this
    exact (S i).equivFin.symm.injective h2
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    refine ⟨fun i => (S i).equivFin ⟨p i, hp i⟩, Finset.mem_univ _, ?_⟩
    funext i
    simp
  · intro q _
    rfl

theorem restr_width (A : MABP σ) (S : ∀ i, Finset (Fin (A.layerSize i)))
    (h0 : (S 0).card = 1) (hl : (S (Fin.last A.depth)).card = 1) (b : ℕ)
    (hb : ∀ i, (S i).card ≤ b) : (restr A S h0 hl).width ≤ b := by
  unfold MABP.width
  exact Finset.sup_le (fun i _ => hb i)

end MonoABPWidth.Dev.L45a
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.LA2a
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.L45a

variable {σ : Type}

/-- total number of vertices -/
def size (A : MABP σ) : ℕ := ∑ i, A.layerSize i

/-- replace the labels on one edge layer -/
def setL (A : MABP σ) (e : Fin A.depth)
    (L : Fin (A.layerSize e.castSucc) → Fin (A.layerSize e.succ) → AffineLabel σ) : MABP σ :=
  { A with label := Function.update A.label e L }

theorem setL_label_self (A : MABP σ) (e : Fin A.depth)
    (L : Fin (A.layerSize e.castSucc) → Fin (A.layerSize e.succ) → AffineLabel σ) :
    (setL A e L).label e = L := by
  show Function.update A.label e L e = L
  exact Function.update_self _ _ _

theorem setL_label_ne (A : MABP σ) (e : Fin A.depth)
    (L : Fin (A.layerSize e.castSucc) → Fin (A.layerSize e.succ) → AffineLabel σ)
    (e' : Fin A.depth) (h : e' ≠ e) : (setL A e L).label e' = A.label e' := by
  show Function.update A.label e L e' = A.label e'
  exact Function.update_of_ne h _ _

theorem setL_prefix (A : MABP σ) (e : Fin A.depth)
    (L : Fin (A.layerSize e.castSucc) → Fin (A.layerSize e.succ) → AffineLabel σ) :
    ∀ j : Fin (A.depth + 1), j ≤ e.castSucc → ∀ v : Fin (A.layerSize j),
      (setL A e L).prefix j v = A.prefix j v := by
  intro j
  induction j using Fin.induction with
  | zero => intro _ v; exact (prefix_zero (setL A e L) v).trans (prefix_zero A v).symm
  | succ j ih =>
    intro hj v
    refine (prefix_succ (setL A e L) j v).trans ?_
    rw [prefix_succ A j v]
    apply Finset.sum_congr rfl
    intro x _
    have hne : j ≠ e := by
      intro h; subst h
      have : j.succ ≤ j.castSucc := hj
      rw [Fin.le_def] at this; simp at this
    have h1 : j.castSucc ≤ e.castSucc := by
      have : j.succ ≤ e.castSucc := hj
      rw [Fin.le_def] at this ⊢; simp at this ⊢; omega
    exact congrArg₂ (fun a b => a * b) (ih h1 x)
      (congrArg AffineLabel.poly (congrFun (congrFun (setL_label_ne A e L j hne) x) v))

theorem setL_suffix (A : MABP σ) (e : Fin A.depth)
    (L : Fin (A.layerSize e.castSucc) → Fin (A.layerSize e.succ) → AffineLabel σ) :
    ∀ j : Fin (A.depth + 1), e.succ ≤ j → ∀ v : Fin (A.layerSize j),
      (setL A e L).suffix j v = A.suffix j v := by
  intro j
  induction j using Fin.reverseInduction with
  | last => intro _ v; exact (suffix_last (setL A e L) v).trans (suffix_last A v).symm
  | cast j ih =>
    intro hj v
    refine (suffix_castSucc (setL A e L) j v).trans ?_
    rw [suffix_castSucc A j v]
    apply Finset.sum_congr rfl
    intro x _
    have hne : j ≠ e := by
      intro h; subst h
      have : j.succ ≤ j.castSucc := hj
      rw [Fin.le_def] at this; simp at this
    have h1 : e.succ ≤ j.succ := by
      have : e.succ ≤ j.castSucc := hj
      rw [Fin.le_def] at this ⊢; simp at this ⊢; omega
    exact congrArg₂ (fun a b => a * b)
      (congrArg AffineLabel.poly (congrFun (congrFun (setL_label_ne A e L j hne) v) x)) (ih h1 x)

theorem setL_output (A : MABP σ) (e : Fin A.depth)
    (L : Fin (A.layerSize e.castSucc) → Fin (A.layerSize e.succ) → AffineLabel σ) :
    (setL A e L).output = ∑ u : Fin (A.layerSize e.castSucc), ∑ v : Fin (A.layerSize e.succ),
      A.prefix e.castSucc u * (L u v).poly * A.suffix e.succ v := by
  rw [output_eq_edges (setL A e L) e]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg₂ (fun a b => a * b)
    (congrArg₂ (fun a b => a * b) (setL_prefix A e L _ le_rfl u)
      (congrArg AffineLabel.poly (congrFun (congrFun (setL_label_self A e L) u) v)))
    (setL_suffix A e L _ le_rfl v)

/-- the zero label -/
def lz : AffineLabel σ := ⟨0, 0⟩

theorem lz_poly : (lz : AffineLabel σ).poly = 0 := by
  simp [lz, AffineLabel.poly]

/-- `l1 + c * l2` -/
noncomputable def ladd (c : NNReal) (l1 l2 : AffineLabel σ) : AffineLabel σ :=
  ⟨l1.constant + c * l2.constant, l1.linear + c • l2.linear⟩

theorem ladd_poly (c : NNReal) (l1 l2 : AffineLabel σ) :
    (ladd c l1 l2).poly = l1.poly + MvPolynomial.C (c : ℝ) * l2.poly := by
  unfold ladd AffineLabel.poly
  simp only
  rw [Finsupp.sum_add_index' (by intro a; simp) (by intro a b₁ b₂; simp [add_mul, mul_add])]
  have : (c • l2.linear).sum (fun x d => MvPolynomial.C (d : ℝ) * MvPolynomial.X x)
      = MvPolynomial.C (c : ℝ) * l2.linear.sum (fun x d => MvPolynomial.C (d : ℝ) * MvPolynomial.X x) := by
    rw [Finsupp.sum_smul_index' (by intro a; simp), Finsupp.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp [mul_assoc]
  rw [this]
  push_cast
  simp only [map_add, map_mul]
  ring

/-- dropping one vertex of an inner layer, given that all paths through it weigh zero -/
theorem drop_general (A : MABP σ) (i : Fin (A.depth + 1)) (u : Fin (A.layerSize i))
    (hi0 : i ≠ 0) (hil : i ≠ Fin.last A.depth)
    (hz : ∀ p : (j : Fin (A.depth + 1)) → Fin (A.layerSize j), p i = u → wt A p = 0) :
    ∃ A' : MABP σ, A'.depth = A.depth ∧ A'.width ≤ A.width ∧ A'.output = A.output ∧
      size A' < size A := by
  classical
  let S : ∀ j, Finset (Fin (A.layerSize j)) :=
    fun j => Finset.univ.filter (fun x => ¬ (j = i ∧ x.val = u.val))
  have hS : ∀ j, j ≠ i → S j = Finset.univ := by
    intro j hj
    apply Finset.filter_true_of_mem
    rintro x _ ⟨h1, _⟩; exact hj h1
  have hS0 : (S 0).card = 1 := by
    rw [hS 0 (Ne.symm hi0)]; simpa using A.source_singleton
  have hSl : (S (Fin.last A.depth)).card = 1 := by
    rw [hS _ (Ne.symm hil)]; simpa using A.sink_singleton
  refine ⟨restr A S hS0 hSl, rfl, ?_, ?_, ?_⟩
  · exact restr_width A S hS0 hSl _ (fun j => by
      refine (Finset.card_le_univ _).trans ?_
      simp only [Fintype.card_fin]
      exact Finset.le_sup (f := A.layerSize) (Finset.mem_univ j))
  · rw [restr_output]
    unfold MABP.output
    apply Finset.sum_congr rfl
    intro p _
    split_ifs with h
    · rfl
    · have : p i = u := by
        by_contra hne
        apply h
        intro j
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
        rintro ⟨rfl, hv⟩
        exact hne (Fin.ext hv)
      exact (hz p this).symm
  · unfold size
    show ∑ j, (S j).card < ∑ j, A.layerSize j
    apply Finset.sum_lt_sum
    · intro j _
      refine (Finset.card_le_univ _).trans ?_
      simp
    · refine ⟨i, Finset.mem_univ _, ?_⟩
      have : (S i).card < (Finset.univ : Finset (Fin (A.layerSize i))).card := by
        apply Finset.card_lt_card
        refine ⟨Finset.subset_univ _, ?_⟩
        intro h
        have := h (Finset.mem_univ u)
        simp [S] at this
      simpa using this

theorem wt_eq_zero_of_label (A : MABP σ) (p : (j : Fin (A.depth + 1)) → Fin (A.layerSize j))
    (e : Fin A.depth) (h : (A.label e (p e.castSucc) (p e.succ)).poly = 0) : wt A p = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ e) h

theorem dropOut (B : MABP σ) (e : Fin B.depth)
    (L : Fin (B.layerSize e.castSucc) → Fin (B.layerSize e.succ) → AffineLabel σ)
    (hout : (setL B e L).output = B.output) (u : Fin (B.layerSize e.castSucc))
    (hi0 : e.castSucc ≠ 0) (hz : ∀ w, (L u w).poly = 0) :
    ∃ A' : MABP σ, A'.depth = B.depth ∧ A'.width ≤ B.width ∧ A'.output = B.output ∧
      size A' < size B := by
  obtain ⟨A', h1, h2, h3, h4⟩ := drop_general (setL B e L) e.castSucc u hi0
    (Fin.castSucc_ne_last e) (by
      intro p hp
      apply wt_eq_zero_of_label (setL B e L) p e
      subst hp
      exact (congrArg AffineLabel.poly (congrFun (congrFun (setL_label_self B e L) _) _)).trans
        (hz _))
  exact ⟨A', h1, h2, h3.trans hout, h4⟩

theorem dropIn (B : MABP σ) (e : Fin B.depth)
    (L : Fin (B.layerSize e.castSucc) → Fin (B.layerSize e.succ) → AffineLabel σ)
    (hout : (setL B e L).output = B.output) (u : Fin (B.layerSize e.succ))
    (hil : e.succ ≠ Fin.last B.depth) (hz : ∀ x, (L x u).poly = 0) :
    ∃ A' : MABP σ, A'.depth = B.depth ∧ A'.width ≤ B.width ∧ A'.output = B.output ∧
      size A' < size B := by
  obtain ⟨A', h1, h2, h3, h4⟩ := drop_general (setL B e L) e.succ u (Fin.succ_ne_zero e) hil (by
      intro p hp
      apply wt_eq_zero_of_label (setL B e L) p e
      subst hp
      exact (congrArg AffineLabel.poly (congrFun (congrFun (setL_label_self B e L) _) _)).trans
        (hz _))
  exact ⟨A', h1, h2, h3.trans hout, h4⟩

end MonoABPWidth.Dev.LA2a
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.LA2
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.LA2a

variable {σ : Type}

theorem nonneg_scalar {P Q : MvPolynomial σ ℝ} (hP : MonotonePolynomial P) (hQ : MonotonePolynomial Q)
    (hP0 : P ≠ 0) (c : ℝ) (h : Q = MvPolynomial.C c * P) : 0 ≤ c := by
  obtain ⟨m, hm⟩ := support_nonempty_of_ne_zero hP0
  have h1 := hQ m
  rw [h, MvPolynomial.coeff_C_mul] at h1
  have h2 : 0 < MvPolynomial.coeff m P :=
    lt_of_le_of_ne (hP m) (Ne.symm (MvPolynomial.mem_support_iff.1 hm))
  exact nonneg_of_mul_nonneg_left h1 h2

theorem single_out (B : MABP σ) (i : Fin (B.depth + 1)) (hs : ∀ x y : Fin (B.layerSize i), x = y)
    (v : Fin (B.layerSize i)) : B.output = B.prefix i v * B.suffix i v := by
  rw [← sum_prefix_suffix B i]
  exact Finset.sum_eq_single v (fun b _ hb => absurd (hs b v) hb) (fun h => absurd (Finset.mem_univ _) h)

theorem endpoints (B : MABP σ) (h0 : B.output ≠ 0) (i : Fin (B.depth + 1))
    (v : Fin (B.layerSize i)) (h : B.prefix i v = 0 ∨ B.suffix i v = 0) :
    i ≠ 0 ∧ i ≠ Fin.last B.depth := by
  constructor
  · rintro rfl
    apply h0
    rw [single_out B 0 (fin_src B) v]
    rcases h with h | h
    · rw [h]; simp
    · rw [h]; simp
  · rintro rfl
    apply h0
    rw [single_out B _ (fin_snk B) v]
    rcases h with h | h
    · rw [h]; simp
    · rw [h]; simp

theorem kill_pre (B : MABP σ) (h0 : B.output ≠ 0) (i : Fin (B.depth + 1)) (v : Fin (B.layerSize i))
    (h : B.prefix i v = 0) :
    ∃ A' : MABP σ, A'.depth = B.depth ∧ A'.width ≤ B.width ∧ A'.output = B.output ∧
      size A' < size B := by
  obtain ⟨hi0, hil⟩ := endpoints B h0 i v (Or.inl h)
  obtain ⟨e, rfl⟩ := Fin.exists_castSucc_eq.2 hil
  classical
  let L : Fin (B.layerSize e.castSucc) → Fin (B.layerSize e.succ) → AffineLabel σ :=
    fun x w => if x = v then lz else B.label e x w
  have hout : (setL B e L).output = B.output := by
    rw [setL_output, output_eq_edges B e]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro w _
    by_cases hx : x = v
    · subst hx; rw [h]; simp
    · simp [L, hx]
  exact dropOut B e L hout v hi0 (fun w => by simp [L, lz_poly])

theorem kill_suf (B : MABP σ) (h0 : B.output ≠ 0) (i : Fin (B.depth + 1)) (v : Fin (B.layerSize i))
    (h : B.suffix i v = 0) :
    ∃ A' : MABP σ, A'.depth = B.depth ∧ A'.width ≤ B.width ∧ A'.output = B.output ∧
      size A' < size B := by
  obtain ⟨hi0, hil⟩ := endpoints B h0 i v (Or.inr h)
  obtain ⟨e, rfl⟩ := Fin.exists_succ_eq.2 hi0
  classical
  let L : Fin (B.layerSize e.castSucc) → Fin (B.layerSize e.succ) → AffineLabel σ :=
    fun x w => if w = v then lz else B.label e x w
  have hout : (setL B e L).output = B.output := by
    rw [setL_output, output_eq_edges B e]
    apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro w _
    by_cases hx : w = v
    · subst hx; rw [h]; simp
    · simp [L, hx]
  exact dropIn B e L hout v hil (fun x => by simp [L, lz_poly])

theorem merge_pre (B : MABP σ) (hr : B.Relevant) (i : Fin (B.depth + 1))
    (u v : Fin (B.layerSize i)) (huv : u ≠ v) (c : ℝ) (hc : c ≠ 0)
    (hp : B.prefix i u = MvPolynomial.C c * B.prefix i v) :
    ∃ A' : MABP σ, A'.depth = B.depth ∧ A'.width ≤ B.width ∧ A'.output = B.output ∧
      size A' < size B := by
  classical
  have hi0 : i ≠ 0 := by rintro rfl; exact huv (fin_src B u v)
  have hil : i ≠ Fin.last B.depth := by rintro rfl; exact huv (fin_snk B u v)
  have hc0 : 0 ≤ c := nonneg_scalar (prefix_mono B i v) (prefix_mono B i u) (hr i v).1 c hp
  obtain ⟨e, rfl⟩ := Fin.exists_castSucc_eq.2 hil
  let c' : NNReal := c.toNNReal
  have hc' : (c' : ℝ) = c := Real.coe_toNNReal c hc0
  let L : Fin (B.layerSize e.castSucc) → Fin (B.layerSize e.succ) → AffineLabel σ :=
    fun x w => if x = v then ladd c' (B.label e v w) (B.label e u w)
      else if x = u then lz else B.label e x w
  have pw : ∀ w, ∑ x, B.prefix e.castSucc x * (L x w).poly * B.suffix e.succ w
      = ∑ x, B.prefix e.castSucc x * (B.label e x w).poly * B.suffix e.succ w := by
    intro w
    have h1 : ∀ x, B.prefix e.castSucc x * (L x w).poly * B.suffix e.succ w =
        B.prefix e.castSucc x * (B.label e x w).poly * B.suffix e.succ w
        + (if x = v then MvPolynomial.C c * B.prefix e.castSucc v * (B.label e u w).poly
            * B.suffix e.succ w else 0)
        - (if x = u then B.prefix e.castSucc u * (B.label e u w).poly * B.suffix e.succ w else 0) := by
      intro x
      by_cases hx : x = v
      · subst hx
        simp only [L, if_true, ladd_poly, if_neg (Ne.symm huv), hc']
        ring
      · by_cases hx2 : x = u
        · subst hx2
          simp [L, hx, lz_poly]
        · simp [L, hx, hx2]
    rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [hp]; ring
  have hout : (setL B e L).output = B.output := by
    rw [setL_output, output_eq_edges B e, Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun w _ => pw w)
  exact dropOut B e L hout u hi0 (fun w => by simp [L, huv, lz_poly])

theorem merge_suf (B : MABP σ) (hr : B.Relevant) (i : Fin (B.depth + 1))
    (u v : Fin (B.layerSize i)) (huv : u ≠ v) (c : ℝ) (hc : c ≠ 0)
    (hp : B.suffix i u = MvPolynomial.C c * B.suffix i v) :
    ∃ A' : MABP σ, A'.depth = B.depth ∧ A'.width ≤ B.width ∧ A'.output = B.output ∧
      size A' < size B := by
  classical
  have hi0 : i ≠ 0 := by rintro rfl; exact huv (fin_src B u v)
  have hil : i ≠ Fin.last B.depth := by rintro rfl; exact huv (fin_snk B u v)
  have hc0 : 0 ≤ c := nonneg_scalar (suffix_mono B i v) (suffix_mono B i u) (hr i v).2 c hp
  obtain ⟨e, rfl⟩ := Fin.exists_succ_eq.2 hi0
  let c' : NNReal := c.toNNReal
  have hc' : (c' : ℝ) = c := Real.coe_toNNReal c hc0
  let L : Fin (B.layerSize e.castSucc) → Fin (B.layerSize e.succ) → AffineLabel σ :=
    fun x y => if y = v then ladd c' (B.label e x v) (B.label e x u)
      else if y = u then lz else B.label e x y
  have pw : ∀ x, ∑ y, B.prefix e.castSucc x * (L x y).poly * B.suffix e.succ y
      = ∑ y, B.prefix e.castSucc x * (B.label e x y).poly * B.suffix e.succ y := by
    intro x
    have h1 : ∀ y, B.prefix e.castSucc x * (L x y).poly * B.suffix e.succ y =
        B.prefix e.castSucc x * (B.label e x y).poly * B.suffix e.succ y
        + (if y = v then B.prefix e.castSucc x * (B.label e x u).poly * MvPolynomial.C c
            * B.suffix e.succ v else 0)
        - (if y = u then B.prefix e.castSucc x * (B.label e x u).poly * B.suffix e.succ u else 0) := by
      intro y
      by_cases hx : y = v
      · subst hx
        simp only [L, if_true, ladd_poly, if_neg (Ne.symm huv), hc']
        ring
      · by_cases hx2 : y = u
        · subst hx2
          simp [L, hx, lz_poly]
        · simp [L, hx, hx2]
    rw [Finset.sum_congr rfl (fun y _ => h1 y), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      Finset.sum_ite_eq', Finset.sum_ite_eq']
    simp only [Finset.mem_univ, if_true]
    rw [hp]; ring
  have hout : (setL B e L).output = B.output := by
    rw [setL_output, output_eq_edges B e]
    exact Finset.sum_congr rfl (fun x _ => pw x)
  exact dropIn B e L hout u hil (fun x => by simp [L, huv, lz_poly])

theorem reduce_core (B : MABP σ) (h0 : B.output ≠ 0) (hn : ¬ (B.Relevant ∧ B.Nonproportional)) :
    ∃ A' : MABP σ, A'.depth = B.depth ∧ A'.width ≤ B.width ∧ A'.output = B.output ∧
      size A' < size B := by
  by_cases hr : B.Relevant
  · have hn' : ¬ B.Nonproportional := fun h => hn ⟨hr, h⟩
    have key : (∃ i u v, u ≠ v ∧ ∃ c : ℝ, c ≠ 0 ∧ B.prefix i u = MvPolynomial.C c * B.prefix i v) ∨
        (∃ i u v, u ≠ v ∧ ∃ c : ℝ, c ≠ 0 ∧ B.suffix i u = MvPolynomial.C c * B.suffix i v) := by
      by_contra h
      push Not at h
      apply hn'
      intro i u v huv c hc
      exact ⟨h.1 i u v huv c hc, h.2 i u v huv c hc⟩
    rcases key with ⟨i, u, v, huv, c, hc, h⟩ | ⟨i, u, v, huv, c, hc, h⟩
    · exact merge_pre B hr i u v huv c hc h
    · exact merge_suf B hr i u v huv c hc h
  · unfold MABP.Relevant at hr
    push Not at hr
    obtain ⟨i, v, hiv⟩ := hr
    by_cases hp : B.prefix i v = 0
    · exact kill_pre B h0 i v hp
    · exact kill_suf B h0 i v (hiv hp)

/-- the class of programs we may replace `A` by -/
def Cls (A B : MABP σ) : Prop := B.depth = A.depth ∧ B.width ≤ A.width ∧ B.output = A.output

theorem exists_good (A : MABP σ) (hA : A.output ≠ 0) :
    ∃ B : MABP σ, Cls A B ∧ B.Relevant ∧ B.Nonproportional := by
  suffices h : ∀ n, ∀ B : MABP σ, Cls A B → size B = n → ∃ B : MABP σ, Cls A B ∧ B.Relevant ∧ B.Nonproportional from
    h _ A ⟨rfl, le_rfl, rfl⟩ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro B hB hs
    by_cases hg : B.Relevant ∧ B.Nonproportional
    · exact ⟨B, hB, hg⟩
    · have h0 : B.output ≠ 0 := by rw [hB.2.2]; exact hA
      obtain ⟨B', h1, h2, h3, h4⟩ := reduce_core B h0 hg
      exact ih (size B') (hs ▸ h4) B' ⟨h1.trans hB.1, h2.trans hB.2.1, h3.trans hB.2.2⟩ rfl

end MonoABPWidth.Dev.LA2

namespace MonoABPWidth.Hierarchy

open MonoABPWidth.Dev.LA2 in
theorem chk_lemma_A_2 {σ : Type} [Fintype σ] (A : MABP σ) (hzero : A.output ≠ 0) :
    ∃ B : MABP σ, B.width ≤ A.width ∧ B.depth ≤ A.depth ∧
      B.Relevant ∧ B.Nonproportional ∧ B.output = A.output := by
  obtain ⟨B, ⟨hd, hw, ho⟩, hr, hn⟩ := exists_good A hzero
  exact ⟨B, hw, hd.le, hr, hn, ho⟩

end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_A_2 := @MonoABPWidth.Hierarchy.chk_lemma_A_2
