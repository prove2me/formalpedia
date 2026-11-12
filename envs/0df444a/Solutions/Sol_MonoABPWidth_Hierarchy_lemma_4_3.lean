-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:43:08.577802+00:00
-- url     : https://prove2.me/submissions/b611d833-84b5-4d6c-96da-896640860553

import Mathlib
import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_1
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_2

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

theorem mono_zero : MonotonePolynomial (0 : MvPolynomial σ ℝ) := fun m => by simp

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

theorem output_mono : MonotonePolynomial A.output := by
  rw [← sum_prefix_suffix A 0]
  exact mono_sum _ _ (fun u _ => mono_mul (prefix_mono A _ u) (suffix_mono A _ u))

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

theorem label_totalDegree_le (l : AffineLabel σ) : l.poly.totalDegree ≤ 1 := by
  unfold AffineLabel.poly
  refine (MvPolynomial.totalDegree_add _ _).trans (max_le ?_ ?_)
  · rw [MvPolynomial.totalDegree_C]; omega
  · refine (MvPolynomial.totalDegree_finsetSum _ _).trans (Finset.sup_le fun x _ => ?_)
    refine (MvPolynomial.totalDegree_mul _ _).trans ?_
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X]

/-- every monomial of an edge label has degree at most one -/
theorem label_degree_le_one (l : AffineLabel σ) {m : σ →₀ ℕ} (hm : m ∈ l.poly.support) :
    m.degree ≤ 1 := by
  have h1 := MvPolynomial.le_totalDegree hm
  have h2 := label_totalDegree_le l
  have h3 : m.degree = m.sum (fun _ e => e) := by
    rw [Finsupp.degree_apply]; rfl
  omega

/-- no cancellation along an edge: `a + m + b` is an output monomial -/
theorem triple_mem_output {σ : Type} (A : MABP σ) (e : Fin A.depth) (u : Fin (A.layerSize e.castSucc))
    (v : Fin (A.layerSize e.succ)) {a m b : σ →₀ ℕ}
    (ha : a ∈ (A.prefix e.castSucc u).support) (hm : m ∈ (A.label e u v).poly.support)
    (hb : b ∈ (A.suffix e.succ v).support) : a + m + b ∈ A.output.support := by
  apply edge_support_subset A e u v
  have h1 : a + m ∈ (A.prefix e.castSucc u * (A.label e u v).poly).support :=
    (mem_support_mul_of_mono (prefix_mono A _ u) (mono_label _) _).2 ⟨a, ha, m, hm, rfl⟩
  exact (mem_support_mul_of_mono (mono_mul (prefix_mono A _ u) (mono_label _)) (suffix_mono A _ v) _).2
    ⟨_, h1, b, hb, rfl⟩

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

end MonoABPWidth.Dev.IMM
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.L43a
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.Basic2

variable {σ : Type}

theorem mem_support_label (l : AffineLabel σ) (m : σ →₀ ℕ) :
    m ∈ l.poly.support ↔ (m = 0 ∧ l.constant ≠ 0) ∨ ∃ z ∈ l.linear.support, m = Finsupp.single z 1 := by
  classical
  unfold AffineLabel.poly
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_add, MvPolynomial.coeff_C]
  unfold Finsupp.sum
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  constructor
  · intro h
    by_cases h0 : (0 : σ →₀ ℕ) = m
    · by_cases hc : l.constant = 0
      · right
        rw [if_pos h0, hc] at h
        simp only [NNReal.coe_zero, zero_add] at h
        obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
        by_cases hxm : Finsupp.single x 1 = m
        · exact ⟨x, by simpa using hx, hxm.symm⟩
        · simp [hxm] at hne
      · left
        exact ⟨h0.symm, hc⟩
    · right
      rw [if_neg h0, zero_add] at h
      obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      by_cases hxm : Finsupp.single x 1 = m
      · exact ⟨x, hx, hxm.symm⟩
      · simp [hxm] at hne
  · rintro (⟨rfl, hc⟩ | ⟨z, hz, rfl⟩)
    · rw [if_pos rfl]
      have h1 : ∑ x ∈ l.linear.support, (l.linear x : ℝ) * (if Finsupp.single x 1 = (0 : σ →₀ ℕ) then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        have : Finsupp.single x 1 ≠ (0 : σ →₀ ℕ) := by simp
        simp [this]
      rw [h1, add_zero]
      exact_mod_cast hc
    · have hne : (0 : σ →₀ ℕ) ≠ Finsupp.single z 1 := by simp [eq_comm]
      rw [if_neg hne, zero_add, Finset.sum_eq_single z]
      · simp only [if_true, mul_one]
        have : l.linear z ≠ 0 := by simpa using hz
        exact_mod_cast this
      · intro x _ hxz
        have : Finsupp.single x 1 ≠ Finsupp.single z 1 := by
          intro h
          exact hxz (Finsupp.single_left_injective one_ne_zero h)
        simp [this]
      · intro h; exact absurd hz h

theorem mem_support_suffix_castSucc (B : MABP σ) (e : Fin B.depth) (u : Fin (B.layerSize e.castSucc))
    (m : σ →₀ ℕ) :
    m ∈ (B.suffix e.castSucc u).support ↔
      ∃ w : Fin (B.layerSize e.succ), ∃ l ∈ (B.label e u w).poly.support,
        ∃ m' ∈ (B.suffix e.succ w).support, l + m' = m := by
  rw [suffix_castSucc, mem_support_sum_of_mono _ _
    (fun w _ => mono_mul (mono_label _) (suffix_mono B _ w))]
  constructor
  · rintro ⟨w, _, hw⟩
    rw [mem_support_mul_of_mono (mono_label _) (suffix_mono B _ w)] at hw
    obtain ⟨a, ha, b, hb, hab⟩ := hw
    exact ⟨w, a, ha, b, hb, hab⟩
  · rintro ⟨w, a, ha, b, hb, hab⟩
    refine ⟨w, Finset.mem_univ _, ?_⟩
    rw [mem_support_mul_of_mono (mono_label _) (suffix_mono B _ w)]
    exact ⟨a, ha, b, hb, hab⟩

theorem mem_support_prefix_succ (B : MABP σ) (e : Fin B.depth) (w : Fin (B.layerSize e.succ))
    (m : σ →₀ ℕ) :
    m ∈ (B.prefix e.succ w).support ↔
      ∃ u : Fin (B.layerSize e.castSucc), ∃ m' ∈ (B.prefix e.castSucc u).support,
        ∃ l ∈ (B.label e u w).poly.support, m' + l = m := by
  rw [prefix_succ, mem_support_sum_of_mono _ _
    (fun u _ => mono_mul (prefix_mono B _ u) (mono_label _))]
  constructor
  · rintro ⟨u, _, hu⟩
    rw [mem_support_mul_of_mono (prefix_mono B _ u) (mono_label _)] at hu
    obtain ⟨a, ha, b, hb, hab⟩ := hu
    exact ⟨u, a, ha, b, hb, hab⟩
  · rintro ⟨u, a, ha, b, hb, hab⟩
    refine ⟨u, Finset.mem_univ _, ?_⟩
    rw [mem_support_mul_of_mono (prefix_mono B _ u) (mono_label _)]
    exact ⟨a, ha, b, hb, hab⟩

theorem support_sum_nnreal {ι : Type} (s : Finset ι) (f : ι → σ →₀ NNReal) (z : σ) :
    z ∈ (∑ i ∈ s, f i).support ↔ ∃ i ∈ s, z ∈ (f i).support := by
  classical
  simp only [Finsupp.mem_support_iff, Finsupp.finset_sum_apply]
  rw [Ne, Finset.sum_eq_zero_iff]
  push_neg
  rfl

end MonoABPWidth.Dev.L43a
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.L43b
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.Basic2 MonoABPWidth.Dev.L43a

variable {σ : Type}

structure Ctx (A : MABP σ) (M : Set (σ →₀ ℕ)) (n : ℕ) : Prop where
  rel : A.Relevant
  sub : ∀ m ∈ A.output.support, m ∈ M
  deg : ∀ m ∈ M, m.degree = n
  cl : ∀ f1 f2 g1 g2 : σ →₀ ℕ, f1 + g1 ∈ M → f1 + g2 ∈ M → f2 + g2 ∈ M → f2 + g1 ∈ M
  wd : ∀ i, A.layerSize i ≤ 2

variable (A : MABP σ)

abbrev V := (i : Fin (A.depth + 1)) × Fin (A.layerSize i)

abbrev vx (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc)) : V A := ⟨e.castSucc, x⟩
abbrev vy (e : Fin A.depth) (y : Fin (A.layerSize e.succ)) : V A := ⟨e.succ, y⟩

noncomputable def pick (v : V A) : σ →₀ ℕ := by
  classical
  exact if h : ∃ p, p ∈ (A.prefix v.1 v.2).support then h.choose else 0

noncomputable def dg (v : V A) : ℕ := (pick A v).degree

variable {A}
variable {M : Set (σ →₀ ℕ)} {n : ℕ}

theorem Ctx.pre_ne (C : Ctx A M n) (v : V A) : ∃ p, p ∈ (A.prefix v.1 v.2).support :=
  support_nonempty_of_ne_zero (C.rel v.1 v.2).1

theorem Ctx.suf_ne (C : Ctx A M n) (v : V A) : ∃ p, p ∈ (A.suffix v.1 v.2).support :=
  support_nonempty_of_ne_zero (C.rel v.1 v.2).2

theorem Ctx.pre_suf (C : Ctx A M n) {v : V A} {p s : σ →₀ ℕ} (hp : p ∈ (A.prefix v.1 v.2).support)
    (hs : s ∈ (A.suffix v.1 v.2).support) : p + s ∈ M :=
  C.sub _ (vertex_support_subset A v.1 v.2 _
    ((mem_support_mul_of_mono (prefix_mono A _ _) (suffix_mono A _ _) _).2 ⟨p, hp, s, hs, rfl⟩))

theorem Ctx.pick_mem (C : Ctx A M n) (v : V A) : pick A v ∈ (A.prefix v.1 v.2).support := by
  classical
  unfold pick
  rw [dif_pos (C.pre_ne v)]
  exact (C.pre_ne v).choose_spec

theorem Ctx.deg_pre (C : Ctx A M n) {v : V A} {p : σ →₀ ℕ} (hp : p ∈ (A.prefix v.1 v.2).support) :
    p.degree = dg A v := by
  obtain ⟨s, hs⟩ := C.suf_ne v
  have h1 := C.deg _ (C.pre_suf hp hs)
  have h2 := C.deg _ (C.pre_suf (C.pick_mem v) hs)
  rw [map_add] at h1 h2
  unfold dg
  omega

theorem Ctx.deg_suf (C : Ctx A M n) {v : V A} {s : σ →₀ ℕ} (hs : s ∈ (A.suffix v.1 v.2).support) :
    s.degree + dg A v = n := by
  have h2 := C.deg _ (C.pre_suf (C.pick_mem v) hs)
  rw [map_add] at h2
  unfold dg
  omega

theorem Ctx.dg_le (C : Ctx A M n) (v : V A) : dg A v ≤ n := by
  obtain ⟨s, hs⟩ := C.suf_ne v
  have := C.deg_suf hs
  omega

theorem Ctx.edge_deg (C : Ctx A M n) (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc))
    (y : Fin (A.layerSize e.succ)) {l : σ →₀ ℕ} (hl : l ∈ (A.label e x y).poly.support) :
    dg A (vy A e y) = dg A (vx A e x) + l.degree := by
  have h : pick A (vx A e x) + l ∈ (A.prefix (vy A e y).1 (vy A e y).2).support :=
    (mem_support_prefix_succ A e y _).2 ⟨x, _, C.pick_mem (vx A e x), l, hl, rfl⟩
  rw [← C.deg_pre h, map_add]
  rfl

theorem Ctx.edge_deg_le (C : Ctx A M n) (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc))
    (y : Fin (A.layerSize e.succ)) (h : (A.label e x y).poly ≠ 0) :
    dg A (vx A e x) ≤ dg A (vy A e y) ∧ dg A (vy A e y) ≤ dg A (vx A e x) + 1 := by
  obtain ⟨l, hl⟩ := support_nonempty_of_ne_zero h
  have h1 := C.edge_deg e x y hl
  have h2 := label_degree_le_one _ hl
  omega

theorem Ctx.edge_zero (C : Ctx A M n) {e : Fin A.depth} {x : Fin (A.layerSize e.castSucc)}
    {y : Fin (A.layerSize e.succ)} {l : σ →₀ ℕ} (hl : l ∈ (A.label e x y).poly.support)
    (h : dg A (vy A e y) = dg A (vx A e x)) : l = 0 := by
  have := C.edge_deg e x y hl
  have h0 : l.degree = 0 := by omega
  exact ((Finsupp.degree_eq_zero_iff _).1 h0)

theorem Ctx.edge_zero_mem (C : Ctx A M n) {e : Fin A.depth} {x : Fin (A.layerSize e.castSucc)}
    {y : Fin (A.layerSize e.succ)} (hq : (A.label e x y).poly ≠ 0)
    (h : dg A (vy A e y) = dg A (vx A e x)) : (0 : σ →₀ ℕ) ∈ (A.label e x y).poly.support := by
  obtain ⟨l, hl⟩ := support_nonempty_of_ne_zero hq
  have := C.edge_zero hl h
  rw [this] at hl
  exact hl

theorem Ctx.edge_one (C : Ctx A M n) {e : Fin A.depth} {x : Fin (A.layerSize e.castSucc)}
    {y : Fin (A.layerSize e.succ)} {l : σ →₀ ℕ} (hl : l ∈ (A.label e x y).poly.support)
    (h : dg A (vy A e y) = dg A (vx A e x) + 1) : ∃ z ∈ (A.label e x y).linear.support,
      l = Finsupp.single z 1 := by
  have := C.edge_deg e x y hl
  have h1 : l.degree = 1 := by omega
  rcases (mem_support_label _ _).1 hl with ⟨rfl, _⟩ | h2
  · simp at h1
  · exact h2

/-- the good completions of a vertex -/
def Gd (M : Set (σ →₀ ℕ)) (v : V A) (m : σ →₀ ℕ) : Prop :=
  ∀ p ∈ (A.prefix v.1 v.2).support, p + m ∈ M

theorem Ctx.Gd_step (C : Ctx A M n) (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc))
    (y : Fin (A.layerSize e.succ)) {l m : σ →₀ ℕ} (hl : l ∈ (A.label e x y).poly.support)
    (h : Gd M (vy A e y) m) : Gd M (vx A e x) (l + m) := by
  intro p hp
  have h1 : p + l ∈ (A.prefix (vy A e y).1 (vy A e y).2).support :=
    (mem_support_prefix_succ A e y _).2 ⟨x, p, hp, l, hl, rfl⟩
  have := h _ h1
  rwa [add_assoc] at this

theorem Ctx.Gd_const (C : Ctx A M n) (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc))
    (y : Fin (A.layerSize e.succ)) (hq : (A.label e x y).poly ≠ 0)
    (hd : dg A (vy A e y) = dg A (vx A e x)) (m : σ →₀ ℕ) :
    Gd M (vx A e x) m ↔ Gd M (vy A e y) m := by
  have h0 := C.edge_zero_mem hq hd
  constructor
  · intro h py hpy
    obtain ⟨sy, hsy⟩ := C.suf_ne (vy A e y)
    have hx := h _ (C.pick_mem (vx A e x))
    have h2 : pick A (vx A e x) + sy ∈ M := by
      have := C.sub _ (triple_mem_output A e x y (C.pick_mem (vx A e x)) h0 hsy)
      simpa using this
    exact C.cl (pick A (vx A e x)) py m sy hx h2 (C.pre_suf hpy hsy)
  · intro h px hpx
    have h1 : px + 0 ∈ (A.prefix (vy A e y).1 (vy A e y).2).support :=
      (mem_support_prefix_succ A e y _).2 ⟨x, px, hpx, 0, h0, rfl⟩
    have := h _ h1
    simpa using this

def CR (A : MABP σ) (u v : V A) : Prop :=
  ∃ (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc)) (y : Fin (A.layerSize e.succ)),
    u = vx A e x ∧ v = vy A e y ∧ (A.label e x y).poly ≠ 0 ∧ dg A v = dg A u

def ER (A : MABP σ) (u v : V A) : Prop :=
  ∃ (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc)) (y : Fin (A.layerSize e.succ)),
    u = vx A e x ∧ v = vy A e y ∧ (A.label e x y).poly ≠ 0

def Reach (A : MABP σ) : V A → V A → Prop := Relation.ReflTransGen (ER A)

theorem Ctx.Gd_eqv (C : Ctx A M n) {u v : V A} (h : Relation.EqvGen (CR A) u v) (m : σ →₀ ℕ) :
    Gd M u m ↔ Gd M v m := by
  induction h with
  | rel a b hab =>
    obtain ⟨e, x, y, rfl, rfl, hq, hd⟩ := hab
    exact C.Gd_const e x y hq hd m
  | refl a => exact Iff.rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem dg_eqv {u v : V A} (h : Relation.EqvGen (CR A) u v) : dg A u = dg A v := by
  induction h with
  | rel a b hab =>
    obtain ⟨e, x, y, rfl, rfl, hq, hd⟩ := hab
    exact hd.symm
  | refl a => rfl
  | symm a b _ ih => exact ih.symm
  | trans a b c _ _ ih1 ih2 => exact ih1.trans ih2

theorem Ctx.reach_dg (C : Ctx A M n) {u v : V A} (h : Reach A u v) :
    dg A u ≤ dg A v ∧ (dg A u = dg A v → Relation.EqvGen (CR A) u v) := by
  induction h with
  | refl => exact ⟨le_rfl, fun _ => Relation.EqvGen.refl _⟩
  | tail hab hbc ih =>
    rename_i b c
    obtain ⟨e, x, y, rfl, rfl, hq⟩ := hbc
    have h1 := C.edge_deg_le e x y hq
    refine ⟨ih.1.trans h1.1, fun h2 => ?_⟩
    have h3 : dg A (vx A e x) = dg A (vy A e y) := by omega
    have h4 : dg A u = dg A (vx A e x) := by omega
    exact (ih.2 h4).trans _ _ _ (Relation.EqvGen.rel _ _ ⟨e, x, y, rfl, rfl, hq, h3.symm⟩)

theorem reach_cross {u v : V A} (h : Reach A u v) :
    ∀ m : Fin (A.depth + 1), u.1 ≤ m → m ≤ v.1 →
      ∃ w : V A, w.1 = m ∧ Reach A u w ∧ Reach A w v := by
  induction h with
  | refl =>
    intro m h1 h2
    exact ⟨u, le_antisymm h1 h2, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | tail hab hbc ih =>
    rename_i b c
    intro m h1 h2
    obtain ⟨e, x, y, rfl, rfl, hq⟩ := hbc
    by_cases hm : m ≤ (vx A e x).1
    · obtain ⟨w, hw, h3, h4⟩ := ih m h1 hm
      exact ⟨w, hw, h3, h4.tail ⟨e, x, y, rfl, rfl, hq⟩⟩
    · have : m = (vy A e y).1 := by
        apply le_antisymm h2
        have h5 : (vx A e x).1 < m := not_le.1 hm
        have h6 : (vy A e y).1.val = (vx A e x).1.val + 1 := rfl
        rw [Fin.le_def]
        rw [Fin.lt_def] at h5
        omega
      exact ⟨vy A e y, this.symm, hab.tail ⟨e, x, y, rfl, rfl, hq⟩, Relation.ReflTransGen.refl⟩


theorem reach_src_aux (A : MABP σ) : ∀ (i : Fin (A.depth + 1)) (x : Fin (A.layerSize i)),
    A.prefix i x ≠ 0 → Reach A ⟨0, A.source⟩ ⟨i, x⟩ := by
  intro i
  induction i using Fin.induction with
  | zero =>
    intro x _
    have := fin_src A x A.source
    subst this
    exact Relation.ReflTransGen.refl
  | succ e ih =>
    intro y hy
    rw [prefix_succ] at hy
    obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero hy
    have h1 : A.prefix e.castSucc x ≠ 0 := left_ne_zero_of_mul hx
    have h2 := right_ne_zero_of_mul hx
    exact (ih x h1).tail ⟨e, x, y, rfl, rfl, h2⟩

theorem reach_snk_aux (A : MABP σ) : ∀ (i : Fin (A.depth + 1)) (x : Fin (A.layerSize i)),
    A.suffix i x ≠ 0 → Reach A ⟨i, x⟩ ⟨Fin.last A.depth, A.sink⟩ := by
  intro i
  induction i using Fin.reverseInduction with
  | last =>
    intro x _
    have := fin_snk A x A.sink
    subst this
    exact Relation.ReflTransGen.refl
  | cast e ih =>
    intro x hx
    rw [suffix_castSucc] at hx
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
    have h1 := left_ne_zero_of_mul hy
    have h2 : A.suffix e.succ y ≠ 0 := right_ne_zero_of_mul hy
    exact Relation.ReflTransGen.head ⟨e, x, y, rfl, rfl, h1⟩ (ih y h2)

theorem Ctx.reach_src (C : Ctx A M n) (v : V A) : Reach A ⟨0, A.source⟩ v :=
  reach_src_aux A v.1 v.2 (C.rel _ _).1

theorem Ctx.reach_snk (C : Ctx A M n) (v : V A) : Reach A v ⟨Fin.last A.depth, A.sink⟩ :=
  reach_snk_aux A v.1 v.2 (C.rel _ _).2

theorem layer_trio (hw : ∀ i, A.layerSize i ≤ 2) (w w' b : V A) (h1 : w.1 = b.1) (h2 : w'.1 = b.1)
    (hwb : w ≠ b) (hw'b : w' ≠ b) : w = w' := by
  obtain ⟨i, x⟩ := w
  obtain ⟨i', x'⟩ := w'
  obtain ⟨j, y⟩ := b
  simp only at h1 h2
  have hi := hw i
  subst h1
  subst h2
  have a1 : x ≠ y := fun h => hwb (by rw [h])
  have a2 : x' ≠ y := fun h => hw'b (by rw [h])
  have e1 := Fin.val_ne_of_ne a1
  have e2 := Fin.val_ne_of_ne a2
  have := x.2
  have := x'.2
  have := y.2
  have : x = x' := Fin.ext (by omega)
  rw [this]

theorem Ctx.mid (C : Ctx A M n) {a b c : V A} (hab : a.1 ≤ b.1) (hbc : b.1 ≤ c.1)
    (d1 : dg A a = dg A b) (d2 : dg A b = dg A c)
    (n1 : ¬ Relation.EqvGen (CR A) a b) (n2 : ¬ Relation.EqvGen (CR A) b c) :
    Relation.EqvGen (CR A) a c := by
  obtain ⟨w, hw1, haw, hws⟩ := reach_cross (C.reach_snk a) b.1 hab (Fin.le_last _)
  obtain ⟨w', hw1', hsw', hw'c⟩ := reach_cross (C.reach_src c) b.1 (Fin.zero_le _) hbc
  have hwb : w ≠ b := by
    rintro rfl
    exact n1 ((C.reach_dg haw).2 d1)
  have hw'b : w' ≠ b := by
    rintro rfl
    exact n2 ((C.reach_dg hw'c).2 d2)
  have := layer_trio C.wd w w' b hw1 hw1' hwb hw'b
  subst this
  have r1 := C.reach_dg haw
  have r2 := C.reach_dg hw'c
  have e1 : dg A a = dg A w := by omega
  have e2 : dg A w = dg A c := by omega
  exact (r1.2 e1).trans _ _ _ (r2.2 e2)

theorem Ctx.tri (C : Ctx A M n) {a b c : V A} (d1 : dg A a = dg A b) (d2 : dg A b = dg A c)
    (n1 : ¬ Relation.EqvGen (CR A) a b) (n2 : ¬ Relation.EqvGen (CR A) b c)
    (n3 : ¬ Relation.EqvGen (CR A) a c) : False := by
  have s : ∀ x y : V A, ¬ Relation.EqvGen (CR A) x y → ¬ Relation.EqvGen (CR A) y x :=
    fun x y h h' => h (Relation.EqvGen.symm _ _ h')
  have T : ∀ x y z : V A, x.1 ≤ y.1 → y.1 ≤ z.1 → dg A x = dg A y → dg A y = dg A z →
      ¬ Relation.EqvGen (CR A) x y → ¬ Relation.EqvGen (CR A) y z →
      ¬ Relation.EqvGen (CR A) x z → False :=
    fun x y z h1 h2 e1 e2 m1 m2 m3 => m3 (C.mid h1 h2 e1 e2 m1 m2)
  have n1' := s _ _ n1
  have n2' := s _ _ n2
  have n3' := s _ _ n3
  rcases le_total a.1 b.1 with h1 | h1 <;> rcases le_total b.1 c.1 with h2 | h2 <;>
    rcases le_total a.1 c.1 with h3 | h3
  · exact T a b c h1 h2 (by omega) (by omega) n1 n2 n3
  · exact T a b c h1 h2 (by omega) (by omega) n1 n2 n3
  · exact T a c b h3 h2 (by omega) (by omega) n3 n2' n1
  · exact T c a b h3 h1 (by omega) (by omega) n3' n1 n2'
  · exact T b a c h1 h3 (by omega) (by omega) n1' n3 n2
  · exact T b c a h2 h3 (by omega) (by omega) n2 n3' n1'
  · exact T c b a h2 h1 (by omega) (by omega) n2' n1' n3'
  · exact T c b a h2 h1 (by omega) (by omega) n2' n1' n3'

theorem Ctx.cl2 (C : Ctx A M n) {u v w : V A} (h1 : dg A u = dg A v) (h2 : dg A u = dg A w)
    (n1 : ¬ Relation.EqvGen (CR A) u v) (n2 : ¬ Relation.EqvGen (CR A) u w) :
    Relation.EqvGen (CR A) v w := by
  by_contra h
  exact C.tri h1.symm h2 (fun h' => n1 (Relation.EqvGen.symm _ _ h')) n2 h |> fun x => x


theorem Ctx.dg_src (C : Ctx A M n) : dg A ⟨0, A.source⟩ = 0 := by
  have h := C.pick_mem (⟨0, A.source⟩ : V A)
  have h1 : (A.prefix (⟨0, A.source⟩ : V A).1 (⟨0, A.source⟩ : V A).2) = 1 := prefix_zero A _
  rw [h1] at h
  have : pick A ⟨0, A.source⟩ = 0 := by
    simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] using h
  unfold dg
  rw [this]
  simp

theorem Ctx.dg_snk (C : Ctx A M n) : dg A ⟨Fin.last A.depth, A.sink⟩ = n := by
  obtain ⟨s, hs0⟩ := C.suf_ne (⟨Fin.last A.depth, A.sink⟩ : V A)
  have h1 : (A.suffix (⟨Fin.last A.depth, A.sink⟩ : V A).1 (⟨Fin.last A.depth, A.sink⟩ : V A).2) = 1 :=
    suffix_last A _
  have hs := hs0
  rw [h1] at hs
  have : s = 0 := by
    simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] using hs
  have h2 := C.deg_suf hs0
  rw [this] at h2
  simpa using h2

theorem Ctx.eqv_src (C : Ctx A M n) {v : V A} (h : dg A v = 0) :
    Relation.EqvGen (CR A) ⟨0, A.source⟩ v :=
  (C.reach_dg (C.reach_src v)).2 (by rw [C.dg_src, h])

theorem Ctx.eqv_snk (C : Ctx A M n) {v : V A} (h : dg A v = n) :
    Relation.EqvGen (CR A) v ⟨Fin.last A.depth, A.sink⟩ :=
  (C.reach_dg (C.reach_snk v)).2 (by rw [C.dg_snk, h])

noncomputable def rep (A : MABP σ) (j : ℕ) : V A := by
  classical
  exact if h : ∃ v : V A, dg A v = j then h.choose else ⟨0, A.source⟩

theorem dg_rep (v : V A) : dg A (rep A (dg A v)) = dg A v := by
  classical
  unfold rep
  rw [dif_pos ⟨v, rfl⟩]
  exact (⟨v, rfl⟩ : ∃ w : V A, dg A w = dg A v).choose_spec

noncomputable def col (A : MABP σ) (v : V A) : ℕ := by
  classical
  exact if Relation.EqvGen (CR A) v (rep A (dg A v)) then 0 else 1

theorem col_le (v : V A) : col A v ≤ 1 := by
  classical
  unfold col
  split_ifs <;> omega

theorem col_congr {u v : V A} (h : Relation.EqvGen (CR A) u v) : col A u = col A v := by
  classical
  have hd := dg_eqv h
  unfold col
  rw [← hd]
  have : Relation.EqvGen (CR A) u (rep A (dg A u)) ↔ Relation.EqvGen (CR A) v (rep A (dg A u)) :=
    ⟨fun h' => (Relation.EqvGen.symm _ _ h).trans _ _ _ h',
     fun h' => h.trans _ _ _ h'⟩
  simp only [this]

theorem Ctx.same_class (C : Ctx A M n) {u v : V A} (hd : dg A u = dg A v) (hc : col A u = col A v) :
    Relation.EqvGen (CR A) u v := by
  classical
  have hr := dg_rep u
  have hr2 : dg A (rep A (dg A v)) = dg A v := dg_rep v
  unfold col at hc
  rw [← hd] at hc
  rw [← hd] at hr2
  by_cases h1 : Relation.EqvGen (CR A) u (rep A (dg A u))
  · rw [if_pos h1] at hc
    by_cases h2 : Relation.EqvGen (CR A) v (rep A (dg A u))
    · exact h1.trans _ _ _ (Relation.EqvGen.symm _ _ h2)
    · rw [if_neg h2] at hc; omega
  · rw [if_neg h1] at hc
    have h2 : ¬ Relation.EqvGen (CR A) v (rep A (dg A u)) := by
      intro h2; rw [if_pos h2] at hc; omega
    have := C.cl2 (u := rep A (dg A u)) (v := u) (w := v) (by rw [hr]) (by rw [hr, hd])
      (fun h => h1 (Relation.EqvGen.symm _ _ h)) (fun h => h2 (Relation.EqvGen.symm _ _ h))
    exact this

theorem Ctx.col_end (C : Ctx A M n) {v : V A} (h : dg A v = 0 ∨ dg A v = n) : col A v = 0 := by
  classical
  have hr := dg_rep v
  unfold col
  rw [if_pos]
  rcases h with h | h
  · have h1 := C.eqv_src h
    have h2 := C.eqv_src (v := rep A (dg A v)) (by rw [hr, h])
    exact (Relation.EqvGen.symm _ _ h1).trans _ _ _ h2
  · have h1 := C.eqv_snk h
    have h2 := C.eqv_snk (v := rep A (dg A v)) (by rw [hr, h])
    exact h1.trans _ _ _ (Relation.EqvGen.symm _ _ h2)

end MonoABPWidth.Dev.L43b
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy

namespace MonoABPWidth.Dev.L43
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.Basic2 MonoABPWidth.Dev.L43a MonoABPWidth.Dev.L43b

variable {σ : Type}

def Bsize (n : ℕ) (j : Fin (n + 1)) : ℕ := if j.val = 0 ∨ j.val = n then 1 else 2

/-- the edge `(e, x, y)` of `A` increases the degree -/
def Var (A : MABP σ) (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc))
    (y : Fin (A.layerSize e.succ)) : Prop :=
  (A.label e x y).poly ≠ 0 ∧ dg A (vy A e y) = dg A (vx A e x) + 1

open scoped Classical in
noncomputable def build (A : MABP σ) (n : ℕ) : MABP σ where
  depth := n
  layerSize := Bsize n
  source_singleton := by simp [Bsize]
  sink_singleton := by simp [Bsize]
  label i u v := ⟨0, ∑ e : Fin A.depth, ∑ x : Fin (A.layerSize e.castSucc),
    ∑ y : Fin (A.layerSize e.succ),
      if (Var A e x y ∧ dg A (vx A e x) = i.val ∧ col A (vx A e x) = u.val ∧
          col A (vy A e y) = v.val) then (A.label e x y).linear else 0⟩

theorem ite_support (c : Prop) [Decidable c] (f : σ →₀ NNReal) (z : σ) :
    z ∈ (if c then f else 0).support ↔ c ∧ z ∈ f.support := by
  by_cases h : c <;> simp [h]

theorem build_label_support (A : MABP σ) (n : ℕ) (i : Fin n)
    (u : Fin (Bsize n i.castSucc)) (v : Fin (Bsize n i.succ)) (m : σ →₀ ℕ) :
    m ∈ ((build A n).label i u v).poly.support ↔
      ∃ (e : Fin A.depth) (x : Fin (A.layerSize e.castSucc)) (y : Fin (A.layerSize e.succ)) (z : σ),
        Var A e x y ∧ dg A (vx A e x) = i.val ∧ col A (vx A e x) = u.val ∧
          col A (vy A e y) = v.val ∧ z ∈ (A.label e x y).linear.support ∧
          m = Finsupp.single z 1 := by
  classical
  have h : (build A n).label i u v = ⟨0, ∑ e : Fin A.depth, ∑ x : Fin (A.layerSize e.castSucc),
    ∑ y : Fin (A.layerSize e.succ),
      if (Var A e x y ∧ dg A (vx A e x) = i.val ∧ col A (vx A e x) = u.val ∧
          col A (vy A e y) = v.val) then (A.label e x y).linear else 0⟩ := by
    unfold build
    congr
  rw [h, mem_support_label]
  simp only [ne_eq, not_true_eq_false, and_false, false_or]
  simp only [support_sum_nnreal, Finset.mem_univ, true_and]
  simp only [ite_support]
  constructor
  · rintro ⟨z, ⟨e, x, y, hc, hz⟩, hm⟩
    exact ⟨e, x, y, z, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, hz, hm⟩
  · rintro ⟨e, x, y, z, h1, h2, h3, h4, hz, hm⟩
    exact ⟨z, ⟨e, x, y, ⟨h1, h2, h3, h4⟩, hz⟩, hm⟩


section
variable {A : MABP σ} {M : Set (σ →₀ ℕ)} {n : ℕ}

theorem claim2 (C : Ctx A M n) : ∀ (j : Fin (n + 1)) (u : Fin (Bsize n j)) (m : σ →₀ ℕ),
    m ∈ ((build A n).suffix j u).support → ∀ v : V A, dg A v = j.val → col A v = u.val →
      Gd M v m := by
  intro j
  induction j using Fin.reverseInduction with
  | last =>
    intro u m hm v hdv _
    have e : (build A n).suffix (Fin.last n) u = 1 := suffix_last (build A n) u
    rw [e] at hm
    have hm0 : m = 0 := by
      simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] using hm
    subst hm0
    intro p hp
    obtain ⟨s, hs⟩ := C.suf_ne v
    have h1 := C.deg_suf hs
    have h2 : s = 0 := by
      apply (Finsupp.degree_eq_zero_iff _).1
      simp at hdv
      omega
    subst h2
    simpa using C.pre_suf hp hs
  | cast e ih =>
    intro u m hm v hdv hcv
    obtain ⟨w, l, hl, m', hm', rfl⟩ := (mem_support_suffix_castSucc (build A n) e u m).1 hm
    obtain ⟨e0, x, y, z, hV, h1, h2, h3, hz, hlz⟩ := (build_label_support A n e u w l).1 hl
    have hy : Gd M (vy A e0 y) m' := ih w m' hm' _ (by rw [hV.2, h1]; simp) h3
    have hlsupp : l ∈ (A.label e0 x y).poly.support :=
      (mem_support_label _ _).2 (Or.inr ⟨z, hz, hlz⟩)
    have hx := C.Gd_step e0 x y hlsupp hy
    have heqv : Relation.EqvGen (CR A) v (vx A e0 x) :=
      C.same_class (by rw [hdv, h1]; rfl) (by rw [hcv, h2])
    exact (C.Gd_eqv heqv _).2 hx

theorem claim1 (C : Ctx A M n) : ∀ (i : Fin (A.depth + 1)) (x : Fin (A.layerSize i)) (m : σ →₀ ℕ),
    m ∈ (A.suffix i x).support → ∀ (j : Fin (n + 1)) (u : Fin (Bsize n j)),
      j.val = dg A ⟨i, x⟩ → u.val = col A ⟨i, x⟩ → m ∈ ((build A n).suffix j u).support := by
  intro i
  induction i using Fin.reverseInduction with
  | last =>
    intro x m hm j u hj hu
    have := fin_snk A x A.sink
    subst this
    have hm1 : m = 0 := by
      rw [suffix_last] at hm
      simpa [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] using hm
    have hjn : j = Fin.last n := Fin.ext (by rw [hj, C.dg_snk]; simp)
    subst hjn
    have e : (build A n).suffix (Fin.last n) u = 1 := suffix_last (build A n) u
    rw [hm1, e]
    simp
  | cast e ih =>
    intro x m hm j u hj hu
    obtain ⟨y, l, hl, m', hm', rfl⟩ := (mem_support_suffix_castSucc A e x m).1 hm
    have hq : (A.label e x y).poly ≠ 0 := fun h => by rw [h] at hl; simp at hl
    have hb := C.edge_deg_le e x y hq
    have hyn := C.dg_le (vy A e y)
    have hj' : j.val = dg A (vx A e x) := hj
    have hu' : u.val = col A (vx A e x) := hu
    by_cases hd : dg A (vy A e y) = dg A (vx A e x)
    · have hl0 := C.edge_zero hl hd
      have hc : col A (vx A e x) = col A (vy A e y) :=
        col_congr (Relation.EqvGen.rel _ _ ⟨e, x, y, rfl, rfl, hq, hd⟩)
      have := ih y m' hm' j u (by rw [hj']; exact hd.symm) (by rw [hu', hc])
      rw [hl0, zero_add]
      exact this
    · have h1 : dg A (vy A e y) = dg A (vx A e x) + 1 := by omega
      obtain ⟨z, hz, hlz⟩ := C.edge_one hl h1
      obtain ⟨jv, hjv⟩ := j
      have hjv0 : jv = dg A (vx A e x) := hj'
      have hjn : jv < n := by omega
      have hw : col A (vy A e y) < Bsize n (⟨jv, hjn⟩ : Fin n).succ := by
        unfold Bsize
        split_ifs with h
        · have h' : jv + 1 = 0 ∨ jv + 1 = n := h
          have := C.col_end (v := vy A e y) (Or.inr (by omega))
          omega
        · have := col_le (vy A e y)
          omega
      refine (mem_support_suffix_castSucc (build A n) ⟨jv, hjn⟩ u _).2
        ⟨⟨col A (vy A e y), hw⟩, l, ?_, m', ?_, rfl⟩
      · refine (build_label_support A n ⟨jv, hjn⟩ u _ l).2
          ⟨e, x, y, z, ⟨hq, h1⟩, by simpa using hj'.symm, hu'.symm, rfl, hz, hlz⟩
      · exact ih y m' hm' (⟨jv, hjn⟩ : Fin n).succ ⟨col A (vy A e y), hw⟩
          (by show jv + 1 = dg A (vy A e y); rw [h1, ← hjv0]) rfl

theorem out_eq (B : MABP σ) : B.output = B.suffix 0 B.source := output_eq_seg B

theorem sup_sub (C : Ctx A M n) : ∀ m ∈ (build A n).output.support, m ∈ M := by
  intro m hm
  rw [out_eq] at hm
  have hd : dg A (⟨0, A.source⟩ : V A) = (0 : Fin (n + 1)).val := by rw [C.dg_src]; rfl
  have hc : col A (⟨0, A.source⟩ : V A) = ((build A n).source : Fin (Bsize n 0)).val := by
    rw [C.col_end (Or.inl C.dg_src)]; rfl
  have := claim2 C 0 (build A n).source m hm ⟨0, A.source⟩ hd hc 0 (by
    have h1 : A.prefix (0 : Fin (A.depth + 1)) A.source = 1 := prefix_zero A _
    show (0 : σ →₀ ℕ) ∈ (A.prefix (0 : Fin (A.depth + 1)) A.source).support
    rw [h1]; simp)
  simpa using this

theorem sup_super (C : Ctx A M n) : ∀ m ∈ A.output.support, m ∈ (build A n).output.support := by
  intro m hm
  rw [out_eq] at hm ⊢
  have hd : (0 : Fin (n + 1)).val = dg A (⟨0, A.source⟩ : V A) := by rw [C.dg_src]; rfl
  have hc : ((build A n).source : Fin (Bsize n 0)).val = col A (⟨0, A.source⟩ : V A) := by
    rw [C.col_end (Or.inl C.dg_src)]; rfl
  exact claim1 C 0 A.source m hm 0 (build A n).source hd hc

end

/-- the zero program of depth `n` -/
def zeroProg (n : ℕ) : MABP σ where
  depth := n
  layerSize := fun _ => 1
  source_singleton := rfl
  sink_singleton := rfl
  label := fun _ _ _ => ⟨0, 0⟩

theorem zeroProg_output (n : ℕ) (hn : 0 < n) : (zeroProg n : MABP σ).output = 0 := by
  classical
  unfold MABP.output
  apply Finset.sum_eq_zero
  intro p _
  apply Finset.prod_eq_zero (i := (⟨0, hn⟩ : Fin n)) (Finset.mem_univ _)
  show (AffineLabel.poly ⟨0, 0⟩ : MvPolynomial σ ℝ) = 0
  simp [AffineLabel.poly]

theorem zeroProg_width (n : ℕ) : (zeroProg n : MABP σ).width ≤ 2 := by
  unfold MABP.width
  apply Finset.sup_le
  intro i _
  show 1 ≤ 2
  omega

theorem deg_path {k n : ℕ} (a : ℕ → Fin k) : (MonoABPWidth.Dev.IMM.path a n).degree = n := by
  unfold MonoABPWidth.Dev.IMM.path MonoABPWidth.Dev.IMM.pathOn
  rw [map_sum]
  simp [Finsupp.degree_single]

end MonoABPWidth.Dev.L43

namespace MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.L43 MonoABPWidth.Dev.L43b MonoABPWidth.Dev.Basic in
theorem chk_lemma_4_3 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (A : MABP (SetMultCost.IMMVar k n)) (hwidth : A.width ≤ 2)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support) :
    ∃ B : MABP (SetMultCost.IMMVar k n),
      MonotonePolynomial B.output ∧ B.width ≤ 2 ∧ B.depth = n ∧
      A.output.support ⊆ B.output.support ∧ B.output.support ⊆ (SetMultCost.imm ℝ k n).support := by
  by_cases hz : A.output = 0
  · refine ⟨zeroProg n, ?_, zeroProg_width n, rfl, ?_, ?_⟩
    · rw [zeroProg_output n hn]; exact mono_zero
    · rw [hz]; simp
    · rw [zeroProg_output n hn]; simp
  · obtain ⟨S, hw, hd, hsimp, hout⟩ := MonoABPWidth.Hierarchy.lemma_4_1 k n hk hn A hz hsub
    have C : Ctx S {m | m ∈ (SetMultCost.imm ℝ k n).support} n :=
      { rel := hsimp.1
        sub := fun m hm => hsub (hout ▸ hm)
        deg := fun m hm => by
          obtain ⟨a, _, _, rfl⟩ := (MonoABPWidth.Dev.IMM.mem_support_imm hk hn m).1 hm
          exact deg_path a
        cl := fun f1 f2 g1 g2 h11 h12 h22 =>
          MonoABPWidth.Hierarchy.lemma_4_2 k n hk hn f1 f2 g1 g2 h11 h12 h22
        wd := fun i => le_trans (Finset.le_sup (f := S.layerSize) (Finset.mem_univ i)) (hw.trans hwidth) }
    refine ⟨build S n, output_mono _, ?_, rfl, ?_, ?_⟩
    · unfold MABP.width
      apply Finset.sup_le
      intro i _
      show Bsize n i ≤ 2
      unfold Bsize
      split_ifs <;> omega
    · intro m hm
      exact sup_super C m (hout ▸ hm)
    · intro m hm
      exact sup_sub C m hm
end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_4_3 := @MonoABPWidth.Hierarchy.chk_lemma_4_3
