-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.theorem_4_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:07:09.343462+00:00
-- url     : https://prove2.me/submissions/6acf5d96-8e44-4578-8f17-4dec5cd6326d

import Mathlib
import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm
import Definitions.Def_MonoABPWidth_Hierarchy_projection
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_1
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_3
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_5
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_7

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

theorem output_mono : MonotonePolynomial A.output := by
  rw [← sum_prefix_suffix A 0]
  exact mono_sum _ _ (fun u _ => mono_mul (prefix_mono A _ u) (suffix_mono A _ u))

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

theorem label_totalDegree_le (l : AffineLabel σ) : l.poly.totalDegree ≤ 1 := by
  unfold AffineLabel.poly
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]; omega
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun x _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

end MonoABPWidth.Dev.Basic2
end

section
set_option autoImplicit false
namespace MonoABPWidth.Dev.IMM
open SetMultCost

variable {k n : ℕ}

/-- the variable of part `j` along the chain `a` -/
def pv (a : ℕ → Fin k) (j : Fin n) : IMMVar k n := (j, a (j : ℕ), a ((j : ℕ) + 1))

/-- monomial: product of the variables of the parts in `S` along chain `a` -/
noncomputable def pathOn (a : ℕ → Fin k) (S : Finset (Fin n)) : IMMVar k n →₀ ℕ :=
  ∑ j ∈ S, Finsupp.single (pv a j) 1

/-- the path monomial -/
noncomputable def path (a : ℕ → Fin k) (n : ℕ) : IMMVar k n →₀ ℕ :=
  pathOn a (Finset.univ : Finset (Fin n))

theorem pv_fst (a : ℕ → Fin k) (j : Fin n) : (pv a j).1 = j := rfl

theorem pathOn_apply (a : ℕ → Fin k) (S : Finset (Fin n)) (x : IMMVar k n) :
    pathOn a S x = if x.1 ∈ S ∧ pv a x.1 = x then 1 else 0 := by
  unfold pathOn
  rw [Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  by_cases hx : pv a x.1 = x
  · have : ∀ j : Fin n, (pv a j = x) ↔ (x.1 = j) := by
      intro j
      constructor
      · intro h; rw [← h]; rfl
      · intro h; rw [← h]; exact hx
    simp only [this]
    rw [Finset.sum_ite_eq]
    simp
  · have : ∀ j : Fin n, ¬ (pv a j = x) := by
      intro j h
      apply hx
      have : j = x.1 := by rw [← h]; rfl
      rw [← this]; exact h
    simp [this]

theorem pathOn_eq_imp {a b : ℕ → Fin k} {S T : Finset (Fin n)}
    (h : pathOn a S = pathOn b T) : ∀ j ∈ S, j ∈ T ∧ pv b j = pv a j := by
  intro j hj
  have := congrArg (fun p => p (pv a j)) h
  simp only [pathOn_apply, pv_fst, hj, true_and, if_true] at this
  by_contra hc
  simp [hc] at this

theorem pathOn_inj {a b : ℕ → Fin k} {S T : Finset (Fin n)}
    (h : pathOn a S = pathOn b T) : S = T ∧ ∀ j ∈ S, pv a j = pv b j := by
  refine ⟨?_, fun j hj => ((pathOn_eq_imp h j hj).2).symm⟩
  ext j
  constructor
  · intro hj; exact (pathOn_eq_imp h j hj).1
  · intro hj; exact (pathOn_eq_imp h.symm j hj).1

theorem pv_inj_iff {a b : ℕ → Fin k} (j : Fin n) :
    pv a j = pv b j ↔ a j = b j ∧ a (j + 1) = b (j + 1) := by
  unfold pv
  simp [Prod.ext_iff]


theorem pathOn_congr {a b : ℕ → Fin k} {S : Finset (Fin n)}
    (h : ∀ j ∈ S, a j = b j ∧ a ((j : ℕ) + 1) = b ((j : ℕ) + 1)) : pathOn a S = pathOn b S := by
  unfold pathOn
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(pv_inj_iff j).2 (h j hj)]

/-! ### Nonnegative polynomials -/

def NN {σ : Type} (p : MvPolynomial σ ℝ) : Prop := ∀ m, 0 ≤ p.coeff m

theorem NN_zero {σ : Type} : NN (0 : MvPolynomial σ ℝ) := fun m => by simp
theorem NN_one {σ : Type} : NN (1 : MvPolynomial σ ℝ) := fun m => by
  classical
  rw [MvPolynomial.coeff_one]; split_ifs <;> norm_num
theorem NN_sum {σ ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℝ) (h : ∀ i ∈ s, NN (f i)) :
    NN (∑ i ∈ s, f i) := fun m => by
  rw [MvPolynomial.coeff_sum]; exact Finset.sum_nonneg fun i hi => h i hi m
theorem NN_mul_X {σ : Type} [DecidableEq σ] {p : MvPolynomial σ ℝ} (hp : NN p) (s : σ) :
    NN (p * MvPolynomial.X s) := fun m => by
  rw [MvPolynomial.coeff_mul_X']; split_ifs
  · exact hp _
  · exact le_rfl

theorem mem_support_sum_NN {σ ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, NN (f i)) (q : σ →₀ ℕ) :
    q ∈ (∑ i ∈ s, f i).support ↔ ∃ i ∈ s, q ∈ (f i).support := by
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]
  rw [Ne, Finset.sum_eq_zero_iff_of_nonneg (fun i hi => h i hi q)]
  push Not
  rfl

theorem mem_support_mul_X {σ : Type} [DecidableEq σ] (p : MvPolynomial σ ℝ) (s : σ) (q : σ →₀ ℕ) :
    q ∈ (p * MvPolynomial.X s).support ↔ ∃ q' ∈ p.support, q = q' + Finsupp.single s 1 := by
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_mul_X']
  constructor
  · intro h
    split_ifs at h with hs
    · refine ⟨q - Finsupp.single s 1, h, ?_⟩
      ext i
      simp only [Finsupp.coe_add, Finsupp.coe_tsub, Pi.add_apply, Pi.sub_apply, Finsupp.single_apply]
      have : 0 < q s := by simpa [Finsupp.mem_support_iff, Nat.pos_iff_ne_zero] using hs
      split_ifs with hi
      · subst hi; omega
      · omega
    · exact absurd rfl h
  · rintro ⟨q', hq', rfl⟩
    have hs : s ∈ (q' + Finsupp.single s 1).support := by
      simp [Finsupp.mem_support_iff]
    rw [if_pos hs]
    have : q' + Finsupp.single s 1 - Finsupp.single s 1 = q' := by
      ext i; simp
    rw [this]; exact hq'

/-! ### Expansion of the product -/

/-- the `i`-th matrix, in the polynomial ring with `N` matrices -/
noncomputable def mat (N : ℕ) (k : ℕ) (i : Fin N) :
    Matrix (Fin k) (Fin k) (MvPolynomial (IMMVar k N) ℝ) :=
  Matrix.of fun a b => MvPolynomial.X (i, a, b)

/-- product of the first `m` matrices -/
noncomputable def pr (N k m : ℕ) (hm : m ≤ N) : Matrix (Fin k) (Fin k) (MvPolynomial (IMMVar k N) ℝ) :=
  (List.ofFn fun i : Fin m => mat N k (Fin.castLE hm i)).prod

theorem pr_zero (N k : ℕ) (h : 0 ≤ N) : pr N k 0 h = 1 := by
  simp [pr]

theorem pr_succ (N k m : ℕ) (hm : m + 1 ≤ N) :
    pr N k (m + 1) hm = pr N k m (by omega) * mat N k ⟨m, by omega⟩ := by
  unfold pr
  rw [List.ofFn_succ', List.prod_concat]
  rfl

theorem pr_apply_succ (N k m : ℕ) (hm : m + 1 ≤ N) (u v : Fin k) :
    pr N k (m + 1) hm u v = ∑ e : Fin k, pr N k m (by omega) u e *
      MvPolynomial.X ((⟨m, by omega⟩ : Fin N), e, v) := by
  rw [pr_succ, Matrix.mul_apply]
  rfl

/-- the set of the first `m` parts -/
def lt (N m : ℕ) : Finset (Fin N) := Finset.univ.filter (fun j => (j : ℕ) < m)

theorem pr_NN (N k : ℕ) : ∀ (m : ℕ) (hm : m ≤ N) (u v : Fin k), NN (pr N k m hm u v) := by
  intro m
  induction m with
  | zero =>
    intro hm u v
    rw [pr_zero, Matrix.one_apply]; split_ifs
    · exact NN_one
    · exact NN_zero
  | succ m ih =>
    intro hm u v
    rw [pr_apply_succ]
    exact NN_sum _ _ fun e _ => NN_mul_X (ih _ _ _) _

theorem mem_support_pr (N k : ℕ) : ∀ (m : ℕ) (hm : m ≤ N) (u v : Fin k) (q : IMMVar k N →₀ ℕ),
    q ∈ (pr N k m hm u v).support ↔
      ∃ a : ℕ → Fin k, a 0 = u ∧ a m = v ∧ q = pathOn a (lt N m) := by
  intro m
  induction m with
  | zero =>
    intro hm u v q
    rw [pr_zero, Matrix.one_apply]
    have h0 : lt N 0 = ∅ := by simp [lt]
    split_ifs with huv
    · subst huv
      simp only [MvPolynomial.support_one, Finset.mem_singleton, h0]
      constructor
      · rintro rfl; exact ⟨fun _ => u, rfl, rfl, by simp [pathOn]⟩
      · rintro ⟨a, _, _, rfl⟩; simp [pathOn]
    · simp only [MvPolynomial.support_zero, Finset.notMem_empty, false_iff]
      rintro ⟨a, h1, h2, _⟩
      exact huv (h1.symm.trans h2)
  | succ m ih =>
    intro hm u v q
    classical
    rw [pr_apply_succ, mem_support_sum_NN _ _ (fun e _ => NN_mul_X (pr_NN N k m _ u e) _)]
    simp only [Finset.mem_univ, true_and, mem_support_mul_X, ih]
    have hlt : lt N (m + 1) = insert ⟨m, by omega⟩ (lt N m) := by
      ext j
      simp only [lt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Fin.ext_iff]
      omega
    have hnot : (⟨m, by omega⟩ : Fin N) ∉ lt N m := by simp [lt]
    have hpv : ∀ (a : ℕ → Fin k), pathOn a (lt N (m + 1)) =
        Finsupp.single (pv a ⟨m, by omega⟩) 1 + pathOn a (lt N m) := by
      intro a
      rw [hlt]; unfold pathOn; rw [Finset.sum_insert hnot]
    constructor
    · rintro ⟨e, q', ⟨a, h0, hm', rfl⟩, rfl⟩
      refine ⟨fun j => if j = m + 1 then v else a j, h0, by simp, ?_⟩
      rw [hpv, add_comm]
      have e2 : pathOn (fun j => if j = m + 1 then v else a j) (lt N m) = pathOn a (lt N m) := by
        symm
        refine pathOn_congr fun j hj => ?_
        simp only [lt, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        have h1 : (j : ℕ) ≠ m + 1 := by omega
        have h2 : (j : ℕ) + 1 ≠ m + 1 := by omega
        have h3 : (j : ℕ) ≠ m := by omega
        simp [h1, h3]
      rw [e2]
      congr 1
      simp [pv, hm']
    · rintro ⟨a, h0, hm', rfl⟩
      refine ⟨a m, pathOn a (lt N m), ⟨a, h0, rfl, rfl⟩, ?_⟩
      rw [hpv, add_comm]
      simp [pv, hm']


theorem path_inj {a b : ℕ → Fin k} (hn : 0 < n) (h : path a n = path b n) :
    ∀ j ≤ n, a j = b j := by
  intro j hj
  have := (pathOn_inj h).2
  rcases Nat.lt_or_ge j n with hjn | hjn
  · exact ((pv_inj_iff (⟨j, hjn⟩ : Fin n)).1 (this _ (Finset.mem_univ _))).1
  · have hj' : j = n := le_antisymm hj hjn
    have := ((pv_inj_iff (⟨n - 1, by omega⟩ : Fin n)).1 (this _ (Finset.mem_univ _))).2
    simp only [show n - 1 + 1 = n by omega] at this
    rw [hj']; exact this

/-- the zero of `Fin k` -/
def z (hk : 0 < k) : Fin k := ⟨0, hk⟩

theorem imm_eq (hk : 0 < k) (hn : 0 < n) :
    imm ℝ k n = pr n k n le_rfl (z hk) (z hk) := by
  simp [imm, hk, pr, mat, z]

theorem lt_self (N : ℕ) : lt N N = Finset.univ := by
  ext j; simp [lt]

/-- **Characterisation of the support of `imm`.** -/
theorem mem_support_imm (hk : 0 < k) (hn : 0 < n) (p : IMMVar k n →₀ ℕ) :
    p ∈ (imm ℝ k n).support ↔
      ∃ a : ℕ → Fin k, a 0 = z hk ∧ a n = z hk ∧ p = path a n := by
  rw [imm_eq hk hn, mem_support_pr, lt_self]
  rfl

/-- every chain gives a support monomial after zeroing the endpoints -/
def ext (hk : 0 < k) (n : ℕ) (c : Fin (n - 1) → Fin k) : ℕ → Fin k := fun j =>
  if h : 1 ≤ j ∧ j ≤ n - 1 then c ⟨j - 1, by omega⟩ else z hk

theorem card_support_imm (hk : 0 < k) (hn : 0 < n) :
    (imm ℝ k n).support.card = k ^ (n - 1) := by
  classical
  have hinj : Function.Injective (fun c : Fin (n - 1) → Fin k => path (ext hk n c) n) := by
    intro c c' h
    have := path_inj hn h
    funext i
    have h1 := this (i.1 + 1) (by omega)
    simpa [ext, show 1 ≤ i.1 + 1 by omega, show i.1 + 1 ≤ n - 1 by omega] using h1
  have himg : (imm ℝ k n).support =
      Finset.univ.image (fun c : Fin (n - 1) → Fin k => path (ext hk n c) n) := by
    ext p
    rw [mem_support_imm hk hn]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, h0, hn', rfl⟩
      refine ⟨fun i => a (i.1 + 1), ?_⟩
      symm
      unfold path
      refine pathOn_congr fun j _ => ?_
      have key : ∀ i : ℕ, i ≤ n → ext hk n (fun i : Fin (n - 1) => a (i.1 + 1)) i = a i := by
        intro i hi
        by_cases h : 1 ≤ i ∧ i ≤ n - 1
        · simp [ext, h, show i - 1 + 1 = i by omega]
        · have : i = 0 ∨ i = n := by omega
          rcases this with rfl | rfl
          · simp only [ext, dif_neg h]; exact h0.symm
          · simp only [ext, dif_neg h]; exact hn'.symm
      exact ⟨(key j (by omega)).symm, (key _ (by omega)).symm⟩
    · rintro ⟨c, rfl⟩
      refine ⟨ext hk n c, ?_, ?_, rfl⟩
      · simp [ext, z]
      · simp only [ext]; rw [dif_neg (by omega)]
  rw [himg, Finset.card_image_of_injective _ hinj]
  simp

end MonoABPWidth.Dev.IMM
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy
namespace MonoABPWidth.Dev.T48a
open MonoABPWidth.Dev.Basic

variable {σ τ : Type}

noncomputable def phi (π : MonotoneProjection σ τ) (x : σ) : MvPolynomial τ ℝ :=
  match π.image x with
  | Sum.inl y => MvPolynomial.X y
  | Sum.inr c => MvPolynomial.C (c : ℝ)

theorem apply_eq (π : MonotoneProjection σ τ) (f : MvPolynomial σ ℝ) :
    π.apply f = MvPolynomial.bind₁ (phi π) f := by
  unfold MonotoneProjection.apply phi
  rfl

noncomputable def mapLabel (π : MonotoneProjection σ τ) (l : AffineLabel σ) : AffineLabel τ where
  constant := l.constant + l.linear.sum (fun x c => match π.image x with
    | Sum.inl _ => 0
    | Sum.inr r => c * r)
  linear := l.linear.sum (fun x c => match π.image x with
    | Sum.inl y => Finsupp.single y c
    | Sum.inr _ => 0)

theorem mapLabel_poly (π : MonotoneProjection σ τ) (l : AffineLabel σ) :
    (mapLabel π l).poly = π.apply l.poly := by
  classical
  rw [apply_eq]
  have hlin : ((mapLabel π l).linear).sum (fun y c => MvPolynomial.C (c : ℝ) * MvPolynomial.X y)
      = ∑ x ∈ l.linear.support, (match π.image x with
          | Sum.inl y => MvPolynomial.C (l.linear x : ℝ) * MvPolynomial.X y
          | Sum.inr _ => 0) := by
    have e : (mapLabel π l).linear = ∑ x ∈ l.linear.support, (match π.image x with
      | Sum.inl y => Finsupp.single y (l.linear x)
      | Sum.inr _ => 0) := rfl
    rw [e, ← Finsupp.sum_finsetSum_index]
    · refine Finset.sum_congr rfl fun x _ => ?_
      cases h : π.image x with
      | inl y => simp [Finsupp.sum_single_index]
      | inr r => simp
    · intro a; simp
    · intros; simp [mul_add, add_mul]
  have hc : (((mapLabel π l).constant : NNReal) : ℝ) = (l.constant : ℝ) +
      ∑ x ∈ l.linear.support, (match π.image x with
          | Sum.inl _ => 0
          | Sum.inr r => (l.linear x : ℝ) * r) := by
    show ((l.constant + l.linear.sum (fun x c => match π.image x with
      | Sum.inl _ => 0
      | Sum.inr r => c * r) : NNReal) : ℝ) = _
    unfold Finsupp.sum
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    cases h : π.image x <;> simp
  unfold AffineLabel.poly
  rw [hlin, hc]
  simp only [map_add, MvPolynomial.bind₁_C_right, MvPolynomial.C_add]
  unfold Finsupp.sum
  simp only [map_sum, map_mul, MvPolynomial.bind₁_C_right, MvPolynomial.bind₁_X_right]
  rw [add_assoc, ← Finset.sum_add_distrib]
  · congr 1
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold phi
    cases h : π.image x <;> simp

/-- apply a monotone projection to every edge label -/
noncomputable def pmap (π : MonotoneProjection σ τ) (A : MABP σ) : MABP τ where
  depth := A.depth
  layerSize := A.layerSize
  source_singleton := A.source_singleton
  sink_singleton := A.sink_singleton
  label e u v := mapLabel π (A.label e u v)

theorem pmap_depth (π : MonotoneProjection σ τ) (A : MABP σ) : (pmap π A).depth = A.depth := rfl

theorem pmap_width (π : MonotoneProjection σ τ) (A : MABP σ) : (pmap π A).width = A.width := rfl

theorem pmap_output (π : MonotoneProjection σ τ) (A : MABP σ) :
    (pmap π A).output = π.apply A.output := by
  classical
  rw [apply_eq]
  unfold MABP.output
  simp only [map_sum, map_prod]
  refine Finset.sum_congr rfl fun p _ => Finset.prod_congr rfl fun e _ => ?_
  rw [← apply_eq]
  exact mapLabel_poly π _

theorem mono_pow {f : MvPolynomial τ ℝ} (hf : MonotonePolynomial f) (e : ℕ) :
    MonotonePolynomial (f ^ e) := by
  induction e with
  | zero => rw [pow_zero]; exact mono_one
  | succ e ih => rw [pow_succ]; exact mono_mul ih hf

theorem phi_mono (π : MonotoneProjection σ τ) (x : σ) : MonotonePolynomial (phi π x) := by
  unfold phi
  cases π.image x with
  | inl y => exact mono_X y
  | inr c => exact mono_C _ c.2

theorem apply_monomial_mono (π : MonotoneProjection σ τ) (p : σ →₀ ℕ) :
    MonotonePolynomial (π.apply (MvPolynomial.monomial p 1)) := by
  rw [apply_eq, MvPolynomial.bind₁_monomial]
  simp only [map_one, one_mul]
  exact Finset.prod_induction _ MonotonePolynomial (fun a b ha hb => mono_mul ha hb) mono_one
    (fun x _ => mono_pow (phi_mono π x) _)

theorem apply_mem_support (π : MonotoneProjection σ τ) {f : MvPolynomial σ ℝ}
    (hf : MonotonePolynomial f) (q : τ →₀ ℕ) :
    q ∈ (π.apply f).support ↔ ∃ p ∈ f.support, q ∈ (π.apply (MvPolynomial.monomial p 1)).support := by
  classical
  have h1 : π.apply f = ∑ p ∈ f.support,
      MvPolynomial.C (f.coeff p) * π.apply (MvPolynomial.monomial p 1) := by
    simp only [apply_eq]
    conv_lhs => rw [f.as_sum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have : (MvPolynomial.monomial p) (MvPolynomial.coeff p f) = MvPolynomial.C (MvPolynomial.coeff p f) * MvPolynomial.monomial p 1 := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [this, map_mul, MvPolynomial.bind₁_C_right]
  have hm : ∀ p ∈ f.support, MonotonePolynomial
      (MvPolynomial.C (f.coeff p) * π.apply (MvPolynomial.monomial p 1)) := fun p _ =>
    mono_mul (mono_C _ (hf p)) (apply_monomial_mono π p)
  rw [h1, mem_support_sum_of_mono _ _ hm]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  have hne : f.coeff p ≠ 0 := MvPolynomial.mem_support_iff.1 hp
  simp only [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul]
  simp [hne]

theorem apply_support_congr (π : MonotoneProjection σ τ) {f g : MvPolynomial σ ℝ}
    (hf : MonotonePolynomial f) (hg : MonotonePolynomial g) (h : f.support = g.support) :
    (π.apply f).support = (π.apply g).support := by
  ext q
  rw [apply_mem_support π hf, apply_mem_support π hg, h]

end MonoABPWidth.Dev.T48a
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy SetMultCost
namespace MonoABPWidth.Dev.T48b
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.Basic2 MonoABPWidth.Dev.IMM MonoABPWidth.Dev.T48a

variable {k : ℕ}

/-- keep the first `n'` matrices, replace the others by the unit matrix `E₀₀` -/
noncomputable def red (k n n' : ℕ) : MonotoneProjection (IMMVar k n) (IMMVar k n') where
  image x := if h : (x.1 : ℕ) < n' then Sum.inl (⟨x.1, h⟩, x.2.1, x.2.2)
    else Sum.inr (if x.2.1.val = 0 ∧ x.2.2.val = 0 then 1 else 0)

theorem phi_red_lt (n n' : ℕ) (x : IMMVar k n) (h : (x.1 : ℕ) < n') :
    phi (red k n n') x = MvPolynomial.X (⟨x.1, h⟩, x.2.1, x.2.2) := by
  simp [phi, red, h]

theorem phi_red_ge (n n' : ℕ) (x : IMMVar k n) (h : ¬ (x.1 : ℕ) < n') :
    phi (red k n n') x = if x.2.1.val = 0 ∧ x.2.2.val = 0 then 1 else 0 := by
  simp only [phi, red, h, dif_neg, not_false_eq_true]
  split_ifs <;> simp

theorem red_pr_lt (n n' : ℕ) (hn : n' ≤ n) : ∀ (m : ℕ) (hm : m ≤ n') (u v : Fin k),
    MvPolynomial.bind₁ (phi (red k n n')) (pr n k m (hm.trans hn) u v) = pr n' k m hm u v := by
  intro m
  induction m with
  | zero =>
    intro hm u v
    rw [pr_zero, pr_zero, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  | succ m ih =>
    intro hm u v
    rw [pr_apply_succ, pr_apply_succ, map_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [map_mul, ih (by omega), MvPolynomial.bind₁_X_right]
    congr 1
    exact phi_red_lt n n' (⟨m, by omega⟩, e, v) (by simp; omega)

theorem red_pr_col (hk : 0 < k) (n n' : ℕ) (hn : n' ≤ n) : ∀ (j : ℕ) (hj : n' + j ≤ n) (u : Fin k),
    MvPolynomial.bind₁ (phi (red k n n')) (pr n k (n' + j) hj u (z hk)) =
      pr n' k n' le_rfl u (z hk) := by
  intro j
  induction j with
  | zero =>
    intro hj u
    exact red_pr_lt n n' hn n' le_rfl u (z hk)
  | succ j ih =>
    intro hj u
    have e0 := pr_apply_succ n k (n' + j) hj u (z hk)
    change MvPolynomial.bind₁ (phi (red k n n')) (pr n k (n' + j + 1) hj u (z hk)) = _
    rw [e0, map_sum]
    have : ∀ e : Fin k, MvPolynomial.bind₁ (phi (red k n n'))
        (pr n k (n' + j) (by omega) u e * MvPolynomial.X ((⟨n' + j, by omega⟩ : Fin n), e, z hk))
        = if e = z hk then pr n' k n' le_rfl u (z hk) else 0 := by
      intro e
      rw [map_mul, MvPolynomial.bind₁_X_right, phi_red_ge n n' _ (by simp)]
      by_cases he : e = z hk
      · subst he
        rw [ih (by omega)]
        simp [z]
      · have : ¬ (e.val = 0) := fun h0 => he (Fin.ext h0)
        simp [this, he]
    rw [Finset.sum_congr rfl (fun e _ => this e)]
    simp

theorem red_imm (hk : 0 < k) (n n' : ℕ) (hn' : 0 < n') (hn : n' ≤ n) :
    (red k n n').apply (imm ℝ k n) = imm ℝ k n' := by
  have hn0 : 0 < n := by omega
  rw [apply_eq, imm_eq hk hn0, imm_eq hk hn']
  obtain ⟨j, rfl⟩ : ∃ j, n = n' + j := ⟨n - n', by omega⟩
  exact red_pr_col hk (n' + j) n' hn j le_rfl (z hk)

theorem imm_mono (hk : 0 < k) (n : ℕ) (hn : 0 < n) : MonotonePolynomial (imm ℝ k n) := by
  rw [imm_eq hk hn]
  exact pr_NN n k n le_rfl _ _

theorem reduce_support (hk : 0 < k) (n n' : ℕ) (hn' : 0 < n') (hn : n' ≤ n)
    (f : MvPolynomial (IMMVar k n) ℝ) (hf : MonotonePolynomial f)
    (hs : f.support = (imm ℝ k n).support) :
    ((red k n n').apply f).support = (imm ℝ k n').support := by
  rw [apply_support_congr (red k n n') hf (imm_mono hk n (by omega)) hs, red_imm hk n n' hn' hn]

/-! ### degree -/

theorem deg_le_depth {σ : Type} (A : MABP σ) {m : σ →₀ ℕ} (hm : m ∈ A.output.support) :
    m.degree ≤ A.depth := by
  classical
  unfold MABP.output at hm
  have h1 := MvPolynomial.support_sum (s := (Finset.univ : Finset ((i : Fin (A.depth + 1)) → Fin (A.layerSize i))))
    (f := fun p => ∏ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly) hm
  obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 h1
  have h2 := MvPolynomial.le_totalDegree hp
  have h3 := MvPolynomial.totalDegree_finset_prod (Finset.univ : Finset (Fin A.depth))
    (fun e => (A.label e (p e.castSucc) (p e.succ)).poly)
  have h4 : ∑ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly.totalDegree ≤ A.depth := by
    calc _ ≤ ∑ _e : Fin A.depth, 1 := Finset.sum_le_sum fun e _ => label_totalDegree_le _
      _ = A.depth := by simp
  have h5 : m.degree = m.sum (fun _ e => e) := by
    rw [Finsupp.degree_apply]; rfl
  omega

theorem deg_path (a : ℕ → Fin k) (n : ℕ) : (path a n).degree = n := by
  unfold path pathOn
  rw [map_sum]
  simp [Finsupp.degree_single]

theorem depth_ge (hk : 0 < k) (n : ℕ) (hn : 0 < n) (A : MABP (IMMVar k n))
    (hs : A.output.support = (imm ℝ k n).support) : n ≤ A.depth := by
  have hc := card_support_imm hk hn
  have hpos : 0 < (imm ℝ k n).support.card := by rw [hc]; positivity
  obtain ⟨m, hm⟩ := Finset.card_pos.1 hpos
  have h1 := deg_le_depth A (hs ▸ hm)
  obtain ⟨a, _, _, rfl⟩ := (mem_support_imm hk hn m).1 hm
  rwa [deg_path] at h1

end MonoABPWidth.Dev.T48b
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy SetMultCost
namespace MonoABPWidth.Dev.T48c

variable {σ : Type}

theorem card_mul_le [DecidableEq σ] (f g : MvPolynomial σ ℝ) :
    (f * g).support.card ≤ f.support.card * g.support.card :=
  (Finset.card_le_card (MvPolynomial.support_mul f g)).trans Finset.card_add_le

theorem single_card {f : MvPolynomial σ ℝ} (h : SingleTerm f) : f.support.card ≤ 1 := by
  classical
  rcases h with ⟨c, rfl⟩ | ⟨c, x, rfl⟩
  · rw [MvPolynomial.C_apply]
    exact (Finset.card_le_card MvPolynomial.support_monomial_subset).trans (by simp)
  · rw [MvPolynomial.C_mul_X_eq_monomial]
    exact (Finset.card_le_card MvPolynomial.support_monomial_subset).trans (by simp)

theorem prod_card {ι : Type} [DecidableEq σ] (s : Finset ι) (f : ι → MvPolynomial σ ℝ)
    (h : ∀ i ∈ s, (f i).support.card ≤ 1) : (∏ i ∈ s, f i).support.card ≤ 1 := by
  refine Finset.prod_induction f (fun p => p.support.card ≤ 1) ?_ ?_ h
  · intro a b ha hb
    exact (card_mul_le a b).trans (by nlinarith)
  · simp

theorem card_le_paths (A : MABP σ) (h : A.SingleTermEdges) :
    A.output.support.card ≤ ∏ i : Fin (A.depth + 1), A.layerSize i := by
  classical
  unfold MABP.output
  refine (Finset.card_le_card (MvPolynomial.support_sum)).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  calc _ ≤ ∑ _p : ((i : Fin (A.depth + 1)) → Fin (A.layerSize i)), 1 :=
        Finset.sum_le_sum fun p _ => prod_card _ _ fun e _ => single_card (h e _ _)
    _ = _ := by simp [Fintype.card_pi]

theorem prod_fin (d : ℕ) (s : Fin (d + 1) → ℕ) (h2 : ∀ i, s i ≤ 2) (h0 : s 0 = 1)
    (hl : s (Fin.last d) = 1) (hd : 1 ≤ d) : ∏ i, s i ≤ 2 ^ (d - 1) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [Fin.prod_univ_castSucc, hl, mul_one, Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, h0, one_mul]
  calc ∏ j : Fin d', s (Fin.castSucc (Fin.succ j)) ≤ ∏ _j : Fin d', 2 :=
        Finset.prod_le_prod' (fun j _ => h2 _)
    _ = 2 ^ (d' + 1 - 1) := by simp

theorem count_simple (A : MABP σ) (h : A.SingleTermEdges) (h2 : A.width ≤ 2) (hd : 1 ≤ A.depth) :
    A.output.support.card ≤ 2 ^ (A.depth - 1) := by
  refine (card_le_paths A h).trans (prod_fin A.depth A.layerSize ?_ ?_ ?_ hd)
  · intro i
    exact le_trans (Finset.le_sup (f := A.layerSize) (Finset.mem_univ i)) h2
  · exact A.source_singleton
  · exact A.sink_singleton

theorem count_le (k n : ℕ) (hk : 0 < k) (hn : 0 < n) (A : MABP (IMMVar k n)) (hw : A.width ≤ 2)
    (hsub : A.output.support ⊆ (imm ℝ k n).support) : A.output.support.card ≤ 2 ^ (n - 1) := by
  obtain ⟨B, _, hBw, hBd, hAB, hBsub⟩ := MonoABPWidth.Hierarchy.lemma_4_3 k n hk hn A hw hsub
  by_cases hz : B.output = 0
  · have : A.output.support = ∅ := by
      apply Finset.subset_empty.1
      simpa [hz] using hAB
    simp [this]
  · obtain ⟨C, hCw, hCd, hCs, hCo⟩ := MonoABPWidth.Hierarchy.lemma_4_1 k n hk hn B hz hBsub
    have hle : A.output.support.card ≤ C.output.support.card := by
      rw [hCo]; exact Finset.card_le_card hAB
    refine hle.trans ?_
    by_cases hd0 : C.depth = 0
    · refine (card_le_paths C hCs.2.2).trans ?_
      have : ∏ i : Fin (C.depth + 1), C.layerSize i = 1 := by
        refine Finset.prod_eq_one fun i _ => ?_
        have : i = Fin.last C.depth := Fin.ext (by have := i.2; simp only [Fin.val_last]; omega)
        rw [this]; exact C.sink_singleton
      rw [this]; exact Nat.one_le_two_pow
    · refine (count_simple C hCs.2.2 (hCw.trans hBw) (by omega)).trans ?_
      exact Nat.pow_le_pow_right (by norm_num) (by omega)

end MonoABPWidth.Dev.T48c
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy SetMultCost
namespace MonoABPWidth.Dev.T48d
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.T48a MonoABPWidth.Dev.IMM

theorem K_pos (k n : ℕ) (hk : 0 < k) (hn : 0 < n) : 0 < ((imm ℝ k n).support.card : ℝ) := by
  rw [card_support_imm hk hn]; positivity

theorem step (k n m q v D : ℕ) (hk : 0 < k) (hm : 0 < m) (hn : n = m * q) (hq : 1 ≤ q)
    (hv : 3 ≤ v) (hvk : v < k) (hD : 2 ≤ D) (γ : ℝ) (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hγv : ((v - 1 : ℕ) : ℝ) / k ≤ γ) (hγq : γ ^ q * (D : ℝ) ^ 2 ≤ γ)
    (A : MABP (IMMVar k n)) (hw : A.width ≤ v) (hd : A.depth ≤ D)
    (hsub : A.output.support ⊆ (imm ℝ k n).support)
    (h1 : (v : ℝ) / k * ((imm ℝ k n).support.card : ℝ) < (A.output.support.card : ℝ))
    (h2 : γ * ((imm ℝ k n).support.card : ℝ) ≤ (A.output.support.card : ℝ)) :
    ∃ A' : MABP (IMMVar k m), A'.width ≤ v - 1 ∧ A'.depth ≤ D ∧
      A'.output.support ⊆ (imm ℝ k m).support ∧
      ((v - 1 : ℕ) : ℝ) / k * ((imm ℝ k m).support.card : ℝ) < (A'.output.support.card : ℝ) ∧
      γ * ((imm ℝ k m).support.card : ℝ) ≤ (A'.output.support.card : ℝ) := by
  classical
  have hn0 : 0 < n := by rw [hn]; exact Nat.mul_pos hm (by omega)
  have hKn := K_pos k n hk hn0
  have hKm := K_pos k m hk hm
  obtain ⟨r, B, c, hr1, hr2, hB, hout⟩ :=
    MonoABPWidth.Hierarchy.lemma_4_5 k n v hn0 (by omega) hvk A hw hsub h1
  have hrD : r < D ^ 2 := by
    by_cases h : 2 ≤ A.depth
    · exact lt_of_lt_of_le (hr2 h) (Nat.pow_le_pow_left hd 2)
    · have : A.depth ≤ 1 := by omega
      have : A.depth ^ 2 ≤ 1 := by nlinarith
      nlinarith
  -- support covering
  have hcov : A.output.support ⊆ Finset.univ.biUnion (fun j : Fin r => (B j).output.support) := by
    intro x hx
    rw [hout] at hx
    have := MvPolynomial.support_sum hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 this
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, ?_⟩
    rw [MvPolynomial.mem_support_iff] at hj ⊢
    rw [MvPolynomial.coeff_C_mul] at hj
    exact right_ne_zero_of_mul hj
  have hcard : A.output.support.card ≤ ∑ j : Fin r, (B j).output.support.card :=
    (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have hApos : 0 < A.output.support.card := by
    have : (0 : ℝ) < (A.output.support.card : ℝ) := lt_of_lt_of_le (by positivity) h2
    exact_mod_cast this
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      have : A.output.support.card ≤ 0 := by simpa using hcard
      omega
    · exact h
  haveI : Nonempty (Fin r) := ⟨⟨0, hr0⟩⟩
  obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin r => (B j).output.support.card) Finset.univ_nonempty
  have hsum : ∑ i : Fin r, (B i).output.support.card ≤ r * (B j).output.support.card := by
    calc _ ≤ ∑ _i : Fin r, (B j).output.support.card :=
          Finset.sum_le_sum fun i _ => hj i (Finset.mem_univ _)
      _ = _ := by simp
  have hBj : A.output.support.card ≤ r * (B j).output.support.card := hcard.trans hsum
  have hBjpos : 0 < (B j).output.support.card := by
    rcases Nat.eq_zero_or_pos (B j).output.support.card with h | h
    · rw [h, mul_zero] at hBj; omega
    · exact h
  -- real inequality: |supp g| D^2 > |supp A|
  have hD2 : (4 : ℝ) ≤ (D : ℝ) ^ 2 := by
    have : (2 : ℝ) ≤ D := by exact_mod_cast hD
    nlinarith
  have hrDr : (r : ℝ) < (D : ℝ) ^ 2 := by exact_mod_cast hrD
  have hBjr : (A.output.support.card : ℝ) < (D : ℝ) ^ 2 * ((B j).output.support.card : ℝ) := by
    have h3 : (A.output.support.card : ℝ) ≤ (r : ℝ) * ((B j).output.support.card : ℝ) := by
      exact_mod_cast hBj
    have h4 : (0 : ℝ) < ((B j).output.support.card : ℝ) := by exact_mod_cast hBjpos
    nlinarith
  set α : ℝ := γ / (D : ℝ) ^ 2 with hα
  have hD2pos : (0 : ℝ) < (D : ℝ) ^ 2 := by linarith
  have hα0 : 0 < α := by positivity
  have hα1 : α < 1 := by
    rw [hα, div_lt_one hD2pos]; linarith
  have hdense : α * ((imm ℝ k n).support.card : ℝ) < ((B j).output.support.card : ℝ) := by
    have : γ * ((imm ℝ k n).support.card : ℝ) < (D : ℝ) ^ 2 * ((B j).output.support.card : ℝ) :=
      lt_of_le_of_lt h2 hBjr
    rw [hα, div_mul_eq_mul_div, div_lt_iff₀ hD2pos]
    linarith
  obtain ⟨-, hBjw, hBjd, hBjsub⟩ := hB j
  have hBjsub' : (B j).output.support ⊆ (imm ℝ k n).support := hBjsub.trans hsub
  obtain ⟨π, hπs, hπc⟩ := MonoABPWidth.Hierarchy.lemma_4_7 k n hk hn0 (B j).output
    (output_mono _) hBjsub' α hα0 hα1 hdense m hm ⟨q, by rw [hn]⟩
  have hqr : (m : ℝ) / (n : ℝ) = ((q : ℕ) : ℝ)⁻¹ := by
    rw [hn]; push_cast
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (0 : ℝ) < q := by exact_mod_cast hq
    field_simp
  have hγα : γ ≤ α ^ ((m : ℝ) / (n : ℝ)) := by
    have h5 : γ ^ q ≤ α := by
      rw [hα, le_div_iff₀ hD2pos]; exact hγq
    have h6 : (γ ^ q) ^ ((q : ℝ)⁻¹) = γ := Real.pow_rpow_inv_natCast hγ0.le (by omega)
    rw [hqr, ← h6]
    exact Real.rpow_le_rpow (by positivity) h5 (by positivity)
  have hlow : γ * ((imm ℝ k m).support.card : ℝ) < (π.apply (B j).output).support.card := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hγα hKm.le) hπc
  have hγv' : ((v - 1 : ℕ) : ℝ) / k ≤ γ := hγv
  refine ⟨pmap π (B j), ?_, ?_, ?_, ?_, ?_⟩
  · rw [pmap_width]; exact hBjw
  · rw [pmap_depth]; exact hBjd.trans hd
  · rw [pmap_output]; exact hπs
  · rw [pmap_output]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hγv' hKm.le) hlow
  · rw [pmap_output]
    exact hlow.le

end MonoABPWidth.Dev.T48d
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy SetMultCost
namespace MonoABPWidth.Dev.T48e
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.T48a MonoABPWidth.Dev.IMM MonoABPWidth.Dev.T48c
  MonoABPWidth.Dev.T48d

/-- last stage: a width-3 program has fewer than `D² 2^(N-1)` monomials -/
theorem final_stage (k N D : ℕ) (hk : 0 < k) (hN : 0 < N) (hk3 : 3 < k) (hD : 2 ≤ D)
    (A : MABP (IMMVar k N)) (hw : A.width ≤ 3) (hd : A.depth ≤ D)
    (hsub : A.output.support ⊆ (imm ℝ k N).support)
    (h1 : (3 : ℝ) / k * ((imm ℝ k N).support.card : ℝ) < (A.output.support.card : ℝ)) :
    (A.output.support.card : ℝ) < (D : ℝ) ^ 2 * 2 ^ (N - 1) := by
  classical
  obtain ⟨r, B, c, hr1, hr2, hB, hout⟩ :=
    MonoABPWidth.Hierarchy.lemma_4_5 k N 3 hN le_rfl hk3 A hw hsub (by exact_mod_cast h1)
  have hrD : r < D ^ 2 := by
    by_cases h : 2 ≤ A.depth
    · exact lt_of_lt_of_le (hr2 h) (Nat.pow_le_pow_left hd 2)
    · have : A.depth ≤ 1 := by omega
      have : A.depth ^ 2 ≤ 1 := by nlinarith
      nlinarith
  have hcov : A.output.support ⊆ Finset.univ.biUnion (fun j : Fin r => (B j).output.support) := by
    intro x hx
    rw [hout] at hx
    have := MvPolynomial.support_sum hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.1 this
    refine Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, ?_⟩
    rw [MvPolynomial.mem_support_iff] at hj ⊢
    rw [MvPolynomial.coeff_C_mul] at hj
    exact right_ne_zero_of_mul hj
  have hcard : A.output.support.card ≤ ∑ j : Fin r, (B j).output.support.card :=
    (Finset.card_le_card hcov).trans Finset.card_biUnion_le
  have hj : ∀ j : Fin r, (B j).output.support.card ≤ 2 ^ (N - 1) := fun j => by
    obtain ⟨-, hw2, -, hsj⟩ := hB j
    exact count_le k N hk hN (B j) (by simpa using hw2) (hsj.trans hsub)
  have hsum : ∑ j : Fin r, (B j).output.support.card ≤ r * 2 ^ (N - 1) := by
    calc _ ≤ ∑ _j : Fin r, 2 ^ (N - 1) := Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  have h3 : A.output.support.card ≤ r * 2 ^ (N - 1) := hcard.trans hsum
  have h4 : r * 2 ^ (N - 1) < D ^ 2 * 2 ^ (N - 1) :=
    Nat.mul_lt_mul_of_pos_right hrD (by positivity)
  exact_mod_cast lt_of_le_of_lt h3 h4

end MonoABPWidth.Dev.T48e
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy SetMultCost
namespace MonoABPWidth.Dev.T48f
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.T48a MonoABPWidth.Dev.IMM MonoABPWidth.Dev.T48d
  MonoABPWidth.Dev.T48e

/-- the arithmetic of the final contradiction -/
theorem arith (k t D w : ℕ) (hw : 3 ≤ w) (hwk : w < k) (ht : 1 ≤ t)
    (hD : (D : ℝ) ^ 2 < ((k : ℝ) / ((w - 1 : ℕ) : ℝ)) ^ t) (S : ℝ)
    (h1 : ((w - 1 : ℕ) : ℝ) / k * (k : ℝ) ^ (t + 1) ≤ S) (h2 : S < (D : ℝ) ^ 2 * 2 ^ (t + 1)) :
    False := by
  have ha : (2 : ℝ) ≤ ((w - 1 : ℕ) : ℝ) := by
    have : 2 ≤ w - 1 := by omega
    exact_mod_cast this
  have hk : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  set a : ℝ := ((w - 1 : ℕ) : ℝ) with ha_def
  have ha0 : 0 < a := by linarith
  rw [div_pow] at hD
  have hD' : (D : ℝ) ^ 2 * a ^ t < (k : ℝ) ^ t := by
    rw [lt_div_iff₀ (by positivity)] at hD; exact hD
  have h2t : (2 : ℝ) ^ t ≤ a ^ t := pow_le_pow_left₀ (by norm_num) ha t
  have hkt : 0 < (k : ℝ) ^ t := by positivity
  have e1 : a / k * (k : ℝ) ^ (t + 1) = a * (k : ℝ) ^ t := by
    field_simp
    ring
  rw [e1] at h1
  have hD0 : 0 ≤ (D : ℝ) ^ 2 := by positivity
  have : (D : ℝ) ^ 2 * 2 ^ (t + 1) ≤ 2 * ((D : ℝ) ^ 2 * a ^ t) := by
    have e : (2 : ℝ) ^ (t + 1) = 2 ^ t * 2 := pow_succ 2 t
    rw [e]; nlinarith [mul_le_mul_of_nonneg_left h2t hD0]
  nlinarith [mul_le_mul_of_nonneg_right ha hkt.le]

theorem main_ind (k w N D : ℕ) (hk : 0 < k) (hw : 3 ≤ w) (hwk : w < k) (hN : 3 ≤ N) (hD : 2 ≤ D)
    (hDN : (D : ℝ) ^ 2 < ((k : ℝ) / ((w - 1 : ℕ) : ℝ)) ^ (N - 2))
    (A : MABP (IMMVar k (N ^ (w - 2)))) (hwid : A.width ≤ w) (hdep : A.depth ≤ D)
    (hs : A.output.support = (imm ℝ k (N ^ (w - 2))).support) : False := by
  obtain ⟨t, rfl⟩ : ∃ t, N = t + 2 := ⟨N - 2, by omega⟩
  simp only [Nat.add_sub_cancel] at hDN
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  have har : (0 : ℝ) < ((w - 1 : ℕ) : ℝ) := by
    have : 0 < w - 1 := by omega
    exact_mod_cast this
  set γ : ℝ := ((w - 1 : ℕ) : ℝ) / k with hγ
  have hγ0 : 0 < γ := by positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγ, div_le_one hkr]
    have : w - 1 ≤ k := by omega
    exact_mod_cast this
  have hγt : γ ^ t * (D : ℝ) ^ 2 < 1 := by
    have e : (k : ℝ) / ((w - 1 : ℕ) : ℝ) = γ⁻¹ := by rw [hγ, inv_div]
    rw [e, inv_pow] at hDN
    have h := mul_lt_mul_of_pos_right hDN (pow_pos hγ0 t)
    rw [inv_mul_cancel₀ (by positivity)] at h
    linarith
  have hγq : γ ^ (t + 2) * (D : ℝ) ^ 2 ≤ γ := by
    have e : γ ^ (t + 2) * (D : ℝ) ^ 2 = γ ^ 2 * (γ ^ t * (D : ℝ) ^ 2) := by ring
    rw [e]
    nlinarith [mul_pos hγ0 hγ0]
  have hDpos : (2 : ℝ) ≤ D := by exact_mod_cast hD
  -- induction
  have key : ∀ j : ℕ, j ≤ w - 3 → ∃ n : ℕ, n = (t + 2) ^ (w - 2 - j) ∧
      ∃ A' : MABP (IMMVar k n), A'.width ≤ w - j ∧ A'.depth ≤ D ∧
        A'.output.support ⊆ (imm ℝ k n).support ∧
        ((w - j : ℕ) : ℝ) / k * ((imm ℝ k n).support.card : ℝ) < (A'.output.support.card : ℝ) ∧
        γ * ((imm ℝ k n).support.card : ℝ) ≤ (A'.output.support.card : ℝ) := by
    intro j
    induction j with
    | zero =>
      intro _
      refine ⟨_, rfl, A, by simpa using hwid, hdep, hs.subset, ?_, ?_⟩
      · rw [hs]
        simp only [Nat.sub_zero]
        have hK := K_pos k ((t + 2) ^ (w - 2)) hk (by positivity)
        have : ((w - 0 : ℕ) : ℝ) / k < 1 := by
          rw [div_lt_one hkr]; exact_mod_cast (by omega : w - 0 < k)
        simp only [Nat.sub_zero] at this
        nlinarith
      · rw [hs]
        simp only [Nat.sub_zero]
        have hK := K_pos k ((t + 2) ^ (w - 2)) hk (by positivity)
        nlinarith
    | succ j ih =>
      intro hj
      obtain ⟨n, hn, A', hw', hd', hsub', h1', h2'⟩ := ih (by omega)
      have hnm : n = (t + 2) ^ (w - 2 - (j + 1)) * (t + 2) := by
        rw [hn, show w - 2 - j = (w - 2 - (j + 1)) + 1 by omega, pow_succ]
      obtain ⟨A'', hw'', hd'', hsub'', h1'', h2''⟩ := step k n ((t + 2) ^ (w - 2 - (j + 1))) (t + 2)
        (w - j) D hk (by positivity) hnm (by omega) (by omega) (by omega) hD γ hγ0 hγ1
        (by
          rw [hγ]
          apply div_le_div_of_nonneg_right _ hkr.le
          exact_mod_cast (by omega : w - j - 1 ≤ w - 1))
        hγq A' hw' hd' hsub' h1' h2'
      refine ⟨_, rfl, A'', by omega, hd'', hsub'', ?_, h2''⟩
      have : w - j - 1 = w - (j + 1) := by omega
      rw [this] at h1''
      exact h1''
  obtain ⟨n, hn, A', hw', hd', hsub', h1', h2'⟩ := key (w - 3) le_rfl
  have hn1 : n = t + 2 := by
    rw [hn, show w - 2 - (w - 3) = 1 by omega, pow_one]
  subst hn1
  have hfin := final_stage k (t + 2) D hk (by omega) (by omega) hD A' (by omega) hd' hsub'
    (by
      have : w - (w - 3) = 3 := by omega
      rw [this] at h1'
      exact_mod_cast h1')
  rw [card_support_imm hk (by omega)] at h2'
  have e : t + 2 - 1 = t + 1 := by omega
  rw [e] at h2'
  push_cast at h2'
  exact arith k t D w hw hwk (by omega) hDN _ h2' hfin

end MonoABPWidth.Dev.T48f
end

section
set_option autoImplicit false
open scoped BigOperators
namespace MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.T48a MonoABPWidth.Dev.T48b MonoABPWidth.Dev.T48f in
theorem chk_theorem_4_8 (k n w : ℕ) (hn : 0 < n) (hw : 3 ≤ w) (hwk : w < k)
    (A : MABP (SetMultCost.IMMVar k n)) (hwidth : A.width ≤ w)
    (hsupport : A.output.support = (SetMultCost.imm ℝ k n).support) :
    Real.rpow ((k : ℝ) / ((w : ℝ) - 1))
      (((Nat.floor (Real.rpow (n : ℝ) (1 / ((w : ℝ) - 2))) : ℝ) / 2) - 1) ≤
        (A.depth : ℝ) := by
  classical
  have hk : 0 < k := by omega
  have hD1 : n ≤ A.depth := depth_ge hk n hn A hsupport
  have hc1 : (1 : ℝ) ≤ (k : ℝ) / ((w : ℝ) - 1) := by
    have : (0 : ℝ) < (w : ℝ) - 1 := by
      have : (3 : ℝ) ≤ w := by exact_mod_cast hw
      linarith
    rw [le_div_iff₀ this]
    have : (w : ℝ) < k := by exact_mod_cast hwk
    linarith
  set N : ℕ := Nat.floor (Real.rpow (n : ℝ) (1 / ((w : ℝ) - 2))) with hNdef
  by_cases hN : N ≤ 2
  · have hx : (N : ℝ) / 2 - 1 ≤ 0 := by
      have : (N : ℝ) ≤ 2 := by exact_mod_cast hN
      linarith
    have h1 := Real.rpow_le_one_of_one_le_of_nonpos hc1 hx
    have h2 : (1 : ℝ) ≤ A.depth := by exact_mod_cast (by omega : 1 ≤ A.depth)
    exact h1.trans h2
  · push_neg at hN
    by_contra hcon
    push_neg at hcon
    have hw2 : (0 : ℝ) < (w : ℝ) - 2 := by
      have : (3 : ℝ) ≤ w := by exact_mod_cast hw
      linarith
    -- N^(w-2) ≤ n
    have hNle : (N : ℝ) ≤ Real.rpow (n : ℝ) (1 / ((w : ℝ) - 2)) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hpow : ((N ^ (w - 2) : ℕ) : ℝ) ≤ n := by
      push_cast
      have h1 : (N : ℝ) ^ (w - 2) ≤ (Real.rpow (n : ℝ) (1 / ((w : ℝ) - 2))) ^ (w - 2) :=
        pow_le_pow_left₀ (by positivity) hNle _
      refine h1.trans (le_of_eq ?_)
      rw [← Real.rpow_natCast]
      change ((n : ℝ) ^ (1 / ((w : ℝ) - 2))) ^ ((w - 2 : ℕ) : ℝ) = n
      rw [← Real.rpow_mul (by positivity)]
      have : ((w - 2 : ℕ) : ℝ) = (w : ℝ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ w)]; ring
      rw [this]
      rw [one_div, inv_mul_cancel₀ hw2.ne', Real.rpow_one]
    have hn' : N ^ (w - 2) ≤ n := by exact_mod_cast hpow
    have hn'3 : 3 ≤ N ^ (w - 2) := by
      calc 3 ≤ N := by omega
        _ = N ^ 1 := (pow_one N).symm
        _ ≤ N ^ (w - 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have hn'0 : 0 < N ^ (w - 2) := by omega
    -- reduce to n' matrices
    have hmono := output_mono A
    have hred := reduce_support hk n (N ^ (w - 2)) hn'0 hn' A.output hmono hsupport
    have hDge : 2 ≤ A.depth := by omega
    -- D^2 < c^(N-2)
    have hDr : (A.depth : ℝ) ^ 2 < ((k : ℝ) / ((w - 1 : ℕ) : ℝ)) ^ (N - 2) := by
      have hcast : ((w - 1 : ℕ) : ℝ) = (w : ℝ) - 1 := by push_cast [Nat.cast_sub (by omega : 1 ≤ w)]; ring
      rw [hcast]
      have hc0 : (0 : ℝ) ≤ (k : ℝ) / ((w : ℝ) - 1) := by linarith
      have h1 : (A.depth : ℝ) ^ 2 < (((k : ℝ) / ((w : ℝ) - 1)) ^ ((N : ℝ) / 2 - 1)) ^ 2 := by
        exact pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
      refine h1.trans_le (le_of_eq ?_)
      rw [← Real.rpow_mul_natCast hc0, ← Real.rpow_natCast]
      congr 1
      have : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by push_cast [Nat.cast_sub (by omega : 2 ≤ N)]; ring
      rw [this]; push_cast; ring
    exact main_ind k w N A.depth hk hw hwk (by omega) hDge hDr (pmap (red k n (N ^ (w - 2))) A)
      (by rw [pmap_width]; exact hwidth) (by rw [pmap_depth])
      (by rw [pmap_output]; exact hred)

end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_theorem_4_8 := @MonoABPWidth.Hierarchy.chk_theorem_4_8
