-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_4_5
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:43:08.494721+00:00
-- url     : https://prove2.me/submissions/72a83860-fc17-4ba5-b34e-e855dbba3cbb

import Mathlib
import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_A_3
import Theorems.Thm_MonoABPWidth_Hierarchy_lemma_4_1

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

theorem isHom_of_support (p : MvPolynomial σ ℝ) (n : ℕ)
    (h : ∀ m ∈ p.support, m.degree = n) : p.IsHomogeneous n := by
  intro d hd
  have e : Finsupp.degree d = Finsupp.weight 1 d := by
    rw [Finsupp.degree_eq_weight_one]; rfl
  rw [← e]
  exact h d (MvPolynomial.mem_support_iff.2 hd)

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

theorem path_apply (a : ℕ → Fin k) (x : IMMVar k n) :
    path a n x = if pv a x.1 = x then 1 else 0 := by
  unfold path; rw [pathOn_apply]; simp

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

/-- A decomposition of a path monomial into two submonomials splits the parts. -/
theorem split_path {a : ℕ → Fin k} {f g : IMMVar k n →₀ ℕ} (h : f + g = path a n) :
    ∃ S : Finset (Fin n), f = pathOn a S ∧ g = pathOn a Sᶜ := by
  classical
  refine ⟨Finset.univ.filter (fun j => f (pv a j) ≠ 0), ?_, ?_⟩
  · ext x
    have hx := congrArg (fun p => p x) h
    simp only [Finsupp.add_apply, path_apply] at hx
    rw [pathOn_apply]
    by_cases hv : pv a x.1 = x
    · rw [if_pos hv] at hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hv, and_true]
      split_ifs with h1 <;> omega
    · rw [if_neg hv] at hx
      rw [if_neg (by tauto)]; omega
  · ext x
    have hx := congrArg (fun p => p x) h
    simp only [Finsupp.add_apply, path_apply] at hx
    rw [pathOn_apply]
    by_cases hv : pv a x.1 = x
    · rw [if_pos hv] at hx
      simp only [Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and, hv, and_true]
      split_ifs with h1 <;> omega
    · rw [if_neg hv] at hx
      rw [if_neg (by tauto)]; omega


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
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.L45a

namespace MonoABPWidth.Dev.L45c

variable {σ : Type}

theorem card_pairs (m : ℕ) :
    Fintype.card {x : Fin m × Fin m // x.1 < x.2} * 2 = m * (m - 1) := by
  rw [Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  have : ∀ a : Fin m, (∑ b : Fin m, if a < b then 1 else 0) = m - 1 - a := by
    intro a
    rw [← Finset.card_filter, ← Fin.card_Ioi]
    congr 1
    ext b; simp
  simp only [this]
  rw [Fin.sum_univ_eq_sum_range (fun a => m - 1 - a) m, Finset.sum_range_reflect (fun j => j) m]
  exact Finset.sum_range_id_mul_two m

/-- constant polynomial: support within `{0}` -/
def Cn (p : MvPolynomial σ ℝ) : Prop := ∀ m ∈ p.support, m = 0

theorem cn_one : Cn (1 : MvPolynomial σ ℝ) := by
  classical
  intro m hm
  rw [MvPolynomial.mem_support_iff, ← MvPolynomial.C_1, MvPolynomial.coeff_C] at hm
  by_contra h
  exact hm (if_neg (Ne.symm h))

theorem cn_eq_C {p : MvPolynomial σ ℝ} (h : Cn p) : p = MvPolynomial.C (p.coeff 0) := by
  classical
  ext m
  rw [MvPolynomial.coeff_C]
  by_cases hm : m = 0
  · subst hm; simp
  · rw [if_neg (Ne.symm hm)]
    by_contra hc
    exact hm (h m (MvPolynomial.mem_support_iff.2 hc))

open scoped Classical in
noncomputable def Vs (A : MABP σ) (i : Fin (A.depth + 1)) : Finset (Fin (A.layerSize i)) :=
  Finset.univ.filter (fun v => Cn (A.prefix i v))

open scoped Classical in
noncomputable def Vt (A : MABP σ) (i : Fin (A.depth + 1)) : Finset (Fin (A.layerSize i)) :=
  Finset.univ.filter (fun v => Cn (A.suffix i v))

open scoped Classical in
noncomputable def Mid (A : MABP σ) (i : Fin (A.depth + 1)) : Finset (Fin (A.layerSize i)) :=
  Finset.univ.filter (fun v => v ∉ Vs A i ∧ v ∉ Vt A i)

open scoped Classical in
noncomputable def pat (A : MABP σ) (a b i : Fin (A.depth + 1)) : Finset (Fin (A.layerSize i)) :=
  if i ≤ a then Vs A i else if i < b then Mid A i else Vt A i

theorem mem_Vs (A : MABP σ) (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) :
    v ∈ Vs A i ↔ Cn (A.prefix i v) := by simp [Vs]

theorem mem_Vt (A : MABP σ) (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) :
    v ∈ Vt A i ↔ Cn (A.suffix i v) := by simp [Vt]

theorem mem_Mid (A : MABP σ) (i : Fin (A.depth + 1)) (v : Fin (A.layerSize i)) :
    v ∈ Mid A i ↔ (v ∉ Vs A i ∧ v ∉ Vt A i) := by simp [Mid]

theorem vs_card_le_one (A : MABP σ) (hrel : A.Relevant) (hnp : A.Nonproportional)
    (i : Fin (A.depth + 1)) : (Vs A i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  by_contra huv
  rw [mem_Vs] at hu hv
  have h1 := cn_eq_C hu
  have h2 := cn_eq_C hv
  have hu0 := (hrel i u).1
  have hv0 := (hrel i v).1
  have c1 : (A.prefix i u).coeff 0 ≠ 0 := by
    intro h; apply hu0; rw [h1, h]; simp
  have c2 : (A.prefix i v).coeff 0 ≠ 0 := by
    intro h; apply hv0; rw [h2, h]; simp
  apply (hnp i u v huv ((A.prefix i u).coeff 0 / (A.prefix i v).coeff 0) (div_ne_zero c1 c2)).1
  rw [h2, ← MvPolynomial.C_mul]
  nth_rewrite 1 [h1]
  congr 1
  rw [← h2]
  field_simp

theorem vt_card_le_one (A : MABP σ) (hrel : A.Relevant) (hnp : A.Nonproportional)
    (i : Fin (A.depth + 1)) : (Vt A i).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  by_contra huv
  rw [mem_Vt] at hu hv
  have h1 := cn_eq_C hu
  have h2 := cn_eq_C hv
  have hu0 := (hrel i u).2
  have hv0 := (hrel i v).2
  have c1 : (A.suffix i u).coeff 0 ≠ 0 := by
    intro h; apply hu0; rw [h1, h]; simp
  have c2 : (A.suffix i v).coeff 0 ≠ 0 := by
    intro h; apply hv0; rw [h2, h]; simp
  apply (hnp i u v huv ((A.suffix i u).coeff 0 / (A.suffix i v).coeff 0) (div_ne_zero c1 c2)).2
  rw [h2, ← MvPolynomial.C_mul]
  nth_rewrite 1 [h1]
  congr 1
  rw [← h2]
  field_simp

theorem step_pre (A : MABP σ) {e : Fin A.depth} {u : Fin (A.layerSize e.castSucc)}
    {v : Fin (A.layerSize e.succ)} (h : Cn (A.prefix e.succ v))
    (hl : (A.label e u v).poly ≠ 0) : Cn (A.prefix e.castSucc u) := by
  intro m hm
  obtain ⟨m0, hm0⟩ := support_nonempty_of_ne_zero hl
  have hmem : m + m0 ∈ (A.prefix e.succ v).support := by
    rw [prefix_succ, mem_support_sum_of_mono _ _
      (fun u _ => mono_mul (prefix_mono A _ u) (mono_label _))]
    exact ⟨u, Finset.mem_univ _, (mem_support_mul_of_mono (prefix_mono A _ u) (mono_label _) _).2
      ⟨m, hm, m0, hm0, rfl⟩⟩
  have := h _ hmem
  exact (add_eq_zero.1 this).1

theorem step_suf (A : MABP σ) {e : Fin A.depth} {u : Fin (A.layerSize e.castSucc)}
    {v : Fin (A.layerSize e.succ)} (h : Cn (A.suffix e.castSucc u))
    (hl : (A.label e u v).poly ≠ 0) : Cn (A.suffix e.succ v) := by
  intro m hm
  obtain ⟨m0, hm0⟩ := support_nonempty_of_ne_zero hl
  have hmem : m0 + m ∈ (A.suffix e.castSucc u).support := by
    rw [suffix_castSucc, mem_support_sum_of_mono _ _
      (fun w _ => mono_mul (mono_label _) (suffix_mono A _ w))]
    exact ⟨v, Finset.mem_univ _, (mem_support_mul_of_mono (mono_label _) (suffix_mono A _ v) _).2
      ⟨m0, hm0, m, hm, rfl⟩⟩
  have := h _ hmem
  exact (add_eq_zero.1 this).2

theorem pre_down (A : MABP σ) (p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i))
    (hw : ∀ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly ≠ 0)
    (i : Fin (A.depth + 1)) : ∀ j : Fin (A.depth + 1), j ≤ i → Cn (A.prefix i (p i)) →
      Cn (A.prefix j (p j)) := by
  induction i using Fin.induction with
  | zero =>
    intro j hj h
    have : j = 0 := le_antisymm hj (Fin.zero_le _)
    subst this; exact h
  | succ e ih =>
    intro j hj h
    rcases eq_or_lt_of_le hj with h1 | h1
    · subst h1; exact h
    · exact ih j (Fin.le_castSucc_iff.2 h1) (step_pre A h (hw e))

theorem suf_up (A : MABP σ) (p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i))
    (hw : ∀ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly ≠ 0)
    (i : Fin (A.depth + 1)) : ∀ j : Fin (A.depth + 1), i ≤ j → Cn (A.suffix i (p i)) →
      Cn (A.suffix j (p j)) := by
  induction i using Fin.reverseInduction with
  | last =>
    intro j hj h
    have : j = Fin.last _ := le_antisymm (Fin.le_last _) hj
    subst this; exact h
  | cast e ih =>
    intro j hj h
    rcases eq_or_lt_of_le hj with h1 | h1
    · subst h1; exact h
    · exact ih j (Fin.castSucc_lt_iff_succ_le.1 h1) (step_suf A h (hw e))

theorem exists_pat (A : MABP σ) (hdis : ∀ i v, ¬ (Cn (A.prefix i v) ∧ Cn (A.suffix i v)))
    (p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i))
    (hw : ∀ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly ≠ 0) :
    ∃ a b : Fin (A.depth + 1), a < b ∧ ∀ i, p i ∈ pat A a b i := by
  classical
  have hS : (Finset.univ.filter (fun i => p i ∈ Vs A i)).Nonempty :=
    ⟨0, by simp [mem_Vs, prefix_zero, cn_one]⟩
  have hT : (Finset.univ.filter (fun i => p i ∈ Vt A i)).Nonempty :=
    ⟨Fin.last _, by simp [mem_Vt, suffix_last, cn_one]⟩
  set a := (Finset.univ.filter (fun i => p i ∈ Vs A i)).max' hS with ha_def
  set b := (Finset.univ.filter (fun i => p i ∈ Vt A i)).min' hT with hb_def
  have ha : p a ∈ Vs A a := by
    have := Finset.max'_mem _ hS
    simpa using this
  have hb : p b ∈ Vt A b := by
    have := Finset.min'_mem _ hT
    simpa using this
  have hamax : ∀ i, p i ∈ Vs A i → i ≤ a := fun i hi =>
    Finset.le_max' _ i (by simpa using hi)
  have hbmin : ∀ i, p i ∈ Vt A i → b ≤ i := fun i hi =>
    Finset.min'_le _ i (by simpa using hi)
  have hdown : ∀ i, i ≤ a → p i ∈ Vs A i := fun i hi => by
    rw [mem_Vs] at ha ⊢
    exact pre_down A p hw a i hi ha
  have hup : ∀ i, b ≤ i → p i ∈ Vt A i := fun i hi => by
    rw [mem_Vt] at hb ⊢
    exact suf_up A p hw b i hi hb
  have hab : a < b := by
    by_contra hc
    have hc := not_lt.1 hc
    have h1 := (mem_Vs A _ _).1 (hdown b hc)
    have h2 := (mem_Vt A _ _).1 hb
    exact hdis b _ ⟨h1, h2⟩
  refine ⟨a, b, hab, fun i => ?_⟩
  unfold pat
  split_ifs with h1 h2
  · exact hdown i h1
  · rw [mem_Mid]
    refine ⟨fun hv => h1 (hamax i hv), fun hv => ?_⟩
    exact absurd (hbmin i hv) (not_le.2 h2)
  · exact hup i (not_lt.1 h2)

theorem pat_unique (A : MABP σ) (hdis : ∀ i v, ¬ (Cn (A.prefix i v) ∧ Cn (A.suffix i v)))
    (p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i))
    {a b a' b' : Fin (A.depth + 1)} (hab : a < b) (hab' : a' < b')
    (h : ∀ i, p i ∈ pat A a b i) (h' : ∀ i, p i ∈ pat A a' b' i) : a = a' ∧ b = b' := by
  have key : ∀ {a b a' b' : Fin (A.depth + 1)}, a' < b' →
      (∀ i, p i ∈ pat A a b i) → (∀ i, p i ∈ pat A a' b' i) → a' ≤ a ∧ b ≤ b' := by
    intro a b a' b' hab' h h'
    constructor
    · by_contra hc
      have hc := not_le.1 hc
      have h1 := h' a'
      have h2 := h a'
      unfold pat at h1 h2
      rw [if_pos le_rfl] at h1
      rw [if_neg (not_le.2 hc)] at h2
      split_ifs at h2 with h3
      · rw [mem_Mid] at h2; exact h2.1 h1
      · exact hdis a' _ ⟨(mem_Vs A _ _).1 h1, (mem_Vt A _ _).1 h2⟩
    · by_contra hc
      have hc := not_le.1 hc
      have h1 := h' b'
      have h2 := h b'
      unfold pat at h1 h2
      rw [if_neg (not_le.2 hab'), if_neg (lt_irrefl _)] at h1
      by_cases h3 : b' ≤ a
      · rw [if_pos h3] at h2
        exact hdis b' _ ⟨(mem_Vs A _ _).1 h2, (mem_Vt A _ _).1 h1⟩
      · rw [if_neg h3, if_pos hc] at h2
        rw [mem_Mid] at h2; exact h2.2 h1
  have k1 := key hab' h h'
  have k2 := key hab h' h
  exact ⟨le_antisymm k2.1 k1.1, le_antisymm k1.2 k2.2⟩

theorem decomp (A : MABP σ) (hrel : A.Relevant) (hnp : A.Nonproportional)
    (W : ℕ) (hW : 2 ≤ W) (hwid : ∀ i, A.layerSize i ≤ W)
    (hlay : ∀ i, ∃ v, Cn (A.prefix i v) ∨ Cn (A.suffix i v))
    (hdis : ∀ i v, ¬ (Cn (A.prefix i v) ∧ Cn (A.suffix i v))) :
    ∃ (r : ℕ) (B : Fin r → MABP σ), r * 2 ≤ (A.depth + 1) * A.depth ∧
      (∀ j, (B j).width ≤ W - 1 ∧ (B j).depth = A.depth) ∧
      A.output = ∑ j, (B j).output := by
  classical
  let Pr := {x : Fin (A.depth + 1) × Fin (A.depth + 1) // x.1 < x.2}
  have h0 : ∀ x : Pr, (pat A x.1.1 x.1.2 0).card = 1 := by
    intro x
    unfold pat
    rw [if_pos (Fin.zero_le _)]
    have : Vs A 0 = Finset.univ := by
      ext v; simp [mem_Vs, prefix_zero, cn_one]
    rw [this, Finset.card_univ, Fintype.card_fin, A.source_singleton]
  have hl : ∀ x : Pr, (pat A x.1.1 x.1.2 (Fin.last A.depth)).card = 1 := by
    intro x
    unfold pat
    have h1 : ¬ Fin.last A.depth ≤ x.1.1 := not_le.2 (lt_of_lt_of_le x.2 (Fin.le_last _))
    have h2 : ¬ Fin.last A.depth < x.1.2 := not_lt.2 (Fin.le_last _)
    rw [if_neg h1, if_neg h2]
    have : Vt A (Fin.last A.depth) = Finset.univ := by
      ext v; simp [mem_Vt, suffix_last, cn_one]
    rw [this, Finset.card_univ, Fintype.card_fin, A.sink_singleton]
  let g : Pr → MABP σ := fun x => restr A (pat A x.1.1 x.1.2) (h0 x) (hl x)
  let e : Fin (Fintype.card Pr) ≃ Pr := (Fintype.equivFin Pr).symm
  refine ⟨Fintype.card Pr, fun j => g (e j), ?_, ?_, ?_⟩
  · have := card_pairs (A.depth + 1)
    simp only [Nat.add_sub_cancel] at this
    exact this.le
  · intro j
    refine ⟨restr_width A _ _ _ (W - 1) (fun i => ?_), rfl⟩
    unfold pat
    split_ifs with h1 h2
    · exact (vs_card_le_one A hrel hnp i).trans (by omega)
    · obtain ⟨v, hv⟩ := hlay i
      have hsub : Mid A i ⊆ Finset.univ.erase v := by
        intro u hu
        rw [Finset.mem_erase]
        refine ⟨?_, Finset.mem_univ _⟩
        rintro rfl
        rw [mem_Mid] at hu
        rcases hv with hv | hv
        · exact hu.1 ((mem_Vs A _ _).2 hv)
        · exact hu.2 ((mem_Vt A _ _).2 hv)
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at this
      have := hwid i
      omega
    · exact (vt_card_le_one A hrel hnp i).trans (by omega)
  · have hsum : ∑ j : Fin (Fintype.card Pr), (g (e j)).output = ∑ x : Pr, (g x).output :=
      Equiv.sum_comp e (fun x => (g x).output)
    show A.output = ∑ j : Fin (Fintype.card Pr), (g (e j)).output
    rw [hsum]
    have hg : ∀ x : Pr, (g x).output = ∑ p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i),
        if (∀ i, p i ∈ pat A x.1.1 x.1.2 i) then wt A p else 0 :=
      fun x => restr_output A _ _ _
    simp only [hg]
    rw [Finset.sum_comm]
    show ∑ p : (i : Fin (A.depth + 1)) → Fin (A.layerSize i), wt A p = _
    refine Finset.sum_congr rfl (fun p _ => ?_)
    by_cases hw : ∀ e : Fin A.depth, (A.label e (p e.castSucc) (p e.succ)).poly ≠ 0
    · obtain ⟨a, b, hab, hp⟩ := exists_pat A hdis p hw
      rw [Finset.sum_eq_single (⟨(a, b), hab⟩ : Pr)]
      · exact (if_pos hp).symm
      · intro x _ hx
        rw [if_neg]
        intro hx'
        apply hx
        obtain ⟨h1, h2⟩ := pat_unique A hdis p x.2 hab hx' hp
        exact Subtype.ext (Prod.ext h1 h2)
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [not_forall] at hw
      obtain ⟨e, he⟩ := hw
      have : wt A p = 0 := Finset.prod_eq_zero (Finset.mem_univ e) (not_not.1 he)
      simp [this]

end MonoABPWidth.Dev.L45c
end

section
set_option autoImplicit false
open scoped BigOperators
open MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.Basic2 MonoABPWidth.Dev.IMM MonoABPWidth.Dev.L45c
open SetMultCost

namespace MonoABPWidth.Dev.L45b

variable {k n : ℕ}

theorem deg_pathOn (a : ℕ → Fin k) (S : Finset (Fin n)) : (pathOn a S).degree = S.card := by
  unfold pathOn
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, map_add, ih, Finset.card_insert_of_notMem hj]
    simp [Finsupp.degree_single]
    ring

theorem deg_path (a : ℕ → Fin k) : (path a n).degree = n := by
  unfold path
  rw [deg_pathOn]; simp

theorem pathOn_add_compl (a : ℕ → Fin k) (S : Finset (Fin n)) :
    pathOn a S + pathOn a Sᶜ = path a n := by
  unfold path pathOn
  exact Finset.sum_add_sum_compl S _

theorem pathOn_empty (a : ℕ → Fin k) : pathOn a (∅ : Finset (Fin n)) = 0 := by
  simp [pathOn]

theorem adj (n : ℕ) (P : ℕ → Prop) (i j : ℕ) (hi : i < n) (hj : j < n) (hPi : P i)
    (hPj : ¬ P j) :
    ∃ ℓ, ℓ + 1 < n ∧ ((P ℓ ∧ ¬ P (ℓ + 1)) ∨ (¬ P ℓ ∧ P (ℓ + 1))) := by
  by_contra hcon
  have hstep : ∀ ℓ, ℓ + 1 < n → (P ℓ ↔ P (ℓ + 1)) := by
    intro ℓ hℓ
    by_cases h1 : P ℓ <;> by_cases h2 : P (ℓ + 1)
    · exact ⟨fun _ => h2, fun _ => h1⟩
    · exact absurd ⟨ℓ, hℓ, Or.inl ⟨h1, h2⟩⟩ hcon
    · exact absurd ⟨ℓ, hℓ, Or.inr ⟨h1, h2⟩⟩ hcon
    · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩
  have hd : ∀ d x, x + d < n → (P x ↔ P (x + d)) := by
    intro d
    induction d with
    | zero => intro x _; exact Iff.rfl
    | succ d ih =>
      intro x hx
      exact (ih x (by omega)).trans (hstep (x + d) (by omega))
  rcases le_total i j with h | h
  · have := hd (j - i) i (by omega)
    rw [show i + (j - i) = j by omega] at this
    exact hPj (this.1 hPi)
  · have := hd (i - j) j (by omega)
    rw [show j + (i - j) = i by omega] at this
    exact hPj (this.2 hPi)

theorem junction (X Y : Finset (Fin n)) (ℓ : ℕ) (hℓ : ℓ + 1 < n)
    (hX : (⟨ℓ, by omega⟩ : Fin n) ∈ X) (hY : (⟨ℓ + 1, hℓ⟩ : Fin n) ∈ Y)
    (R : (ℕ → Fin k) → Prop) (U V : Set (IMMVar k n →₀ ℕ)) (u0 : IMMVar k n →₀ ℕ) (hu0 : u0 ∈ U)
    (v0 : IMMVar k n →₀ ℕ) (hv0 : v0 ∈ V)
    (h : ∀ u ∈ U, ∀ v ∈ V, ∃ a, R a ∧ u = pathOn a X ∧ v = pathOn a Y) :
    ∃ c : Fin k, ∀ u ∈ U, ∀ v ∈ V, ∃ a, R a ∧ u = pathOn a X ∧ v = pathOn a Y ∧ a (ℓ + 1) = c := by
  obtain ⟨a0, -, hu0', hv0'⟩ := h u0 hu0 v0 hv0
  refine ⟨a0 (ℓ + 1), fun u hu v hv => ?_⟩
  obtain ⟨a, hRa, hua, hva⟩ := h u hu v hv
  obtain ⟨a', -, hua', hva'⟩ := h u hu v0 hv0
  refine ⟨a, hRa, hua, hva, ?_⟩
  have e1 := (pathOn_inj (hv0'.symm.trans hva')).2 ⟨ℓ + 1, hℓ⟩ hY
  have e2 := (pathOn_inj (hua.symm.trans hua')).2 ⟨ℓ, by omega⟩ hX
  rw [pv_inj_iff] at e1 e2
  exact e2.2.trans e1.1.symm

theorem path_ext (hk : 0 < k) (hn : 0 < n) (a : ℕ → Fin k) (h0 : a 0 = z hk) (hn' : a n = z hk) :
    path (IMM.ext hk n (fun i : Fin (n - 1) => a (i.1 + 1))) n = path a n := by
  unfold path
  refine pathOn_congr fun j _ => ?_
  have key : ∀ i : ℕ, i ≤ n → IMM.ext hk n (fun i : Fin (n - 1) => a (i.1 + 1)) i = a i := by
    intro i hi
    by_cases h : 1 ≤ i ∧ i ≤ n - 1
    · simp [IMM.ext, h, show i - 1 + 1 = i by omega]
    · have : i = 0 ∨ i = n := by omega
      rcases this with rfl | rfl
      · simp only [IMM.ext, dif_neg h]; exact h0.symm
      · simp only [IMM.ext, dif_neg h]; exact hn'.symm
  have := j.2
  exact ⟨key j.1 (by omega), key (j.1 + 1) (by omega)⟩

theorem count_chain (hk : 0 < k) (hn : 0 < n) (ℓ : ℕ) (hℓ : ℓ + 1 < n) (c : Fin k)
    (T : Finset (IMMVar k n →₀ ℕ))
    (hT : ∀ m ∈ T, ∃ a : ℕ → Fin k, a 0 = z hk ∧ a n = z hk ∧ a (ℓ + 1) = c ∧ m = path a n) :
    T.card ≤ k ^ (n - 2) := by
  classical
  let F : Finset (Fin (n - 1) → Fin k) :=
    Fintype.piFinset (fun i : Fin (n - 1) => if i.1 = ℓ then ({c} : Finset (Fin k)) else Finset.univ)
  have hFcard : F.card = k ^ (n - 2) := by
    rw [Fintype.card_piFinset]
    have hi0 : ℓ < n - 1 := by omega
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (⟨ℓ, hi0⟩ : Fin (n - 1)))]
    rw [Finset.prod_congr rfl (g := fun _ => k)]
    · simp [Finset.card_erase_of_mem, show n - 1 - 1 = n - 2 by omega]
    · intro i hi
      have : i.1 ≠ ℓ := fun h => (Finset.mem_erase.1 hi).1 (Fin.ext h)
      simp [this]
  have hsub : T ⊆ F.image (fun c => path (IMM.ext hk n c) n) := by
    intro m hm
    obtain ⟨a, h0, hn', hc, rfl⟩ := hT m hm
    rw [Finset.mem_image]
    refine ⟨fun i => a (i.1 + 1), ?_, path_ext hk hn a h0 hn'⟩
    rw [Fintype.mem_piFinset]
    intro i
    by_cases hi : i.1 = ℓ
    · simp [hi, hc]
    · simp [hi]
  calc T.card ≤ (F.image (fun c => path (IMM.ext hk n c) n)).card := Finset.card_le_card hsub
    _ ≤ F.card := Finset.card_image_le
    _ = _ := hFcard

theorem vertex_count (hk : 0 < k) (hn : 0 < n) (f g : MvPolynomial (IMMVar k n) ℝ)
    (hf : MonotonePolynomial f) (hg : MonotonePolynomial g)
    (hfh : Homogeneous f) (hgh : Homogeneous g) (hfc : ¬ Cn f) (hgc : ¬ Cn g)
    (hfg : ∀ p ∈ f.support, ∀ q ∈ g.support, p + q ∈ (imm ℝ k n).support) :
    2 ≤ n ∧ (f * g).support.card ≤ k ^ (n - 2) := by
  classical
  obtain ⟨qf, hqf⟩ := hfh
  obtain ⟨qg, hqg⟩ := hgh
  simp only [Cn, not_forall] at hfc hgc
  obtain ⟨mf, hmf, hmf0⟩ := hfc
  obtain ⟨mg, hmg, hmg0⟩ := hgc
  obtain ⟨a0, ha00, ha0n, hpq0⟩ := (mem_support_imm hk hn _).1 (hfg mf hmf mg hmg)
  obtain ⟨S, hS1, hS2⟩ := split_path hpq0
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, pathOn_empty] at hS1
    exact hmf0 hS1
  have hScne : Sᶜ.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, pathOn_empty] at hS2
    exact hmg0 hS2
  obtain ⟨i0, hi0⟩ := hSne
  obtain ⟨j0, hj0⟩ := hScne
  have hij : i0 ≠ j0 := fun h => (Finset.mem_compl.1 hj0) (h ▸ hi0)
  have hn2 : 2 ≤ n := by
    have h1 := i0.2
    have h2 := j0.2
    have h3 : i0.1 ≠ j0.1 := fun h => hij (Fin.ext h)
    omega
  have hall : ∀ p ∈ f.support, ∀ q ∈ g.support, ∃ a : ℕ → Fin k, (a 0 = z hk ∧ a n = z hk) ∧
      p = pathOn a S ∧ q = pathOn a Sᶜ := by
    intro p hp q hq
    obtain ⟨a, h0, hn', hpq⟩ := (mem_support_imm hk hn _).1 (hfg p hp q hq)
    obtain ⟨S1, h1, h2⟩ := split_path hpq
    obtain ⟨a'', -, -, hpq''⟩ := (mem_support_imm hk hn _).1 (hfg mf hmf q hq)
    obtain ⟨S3, h3, h4⟩ := split_path hpq''
    have hS3 : S = S3 := (pathOn_inj (hS1.symm.trans h3)).1
    have hc : S1ᶜ = S3ᶜ := (pathOn_inj (h2.symm.trans h4)).1
    have hS1S : S1 = S := (compl_inj_iff.1 hc).trans hS3.symm
    subst hS1S
    exact ⟨a, ⟨h0, hn'⟩, h1, h2⟩
  -- adjacency
  let P : ℕ → Prop := fun ℓ => ∃ j ∈ S, j.1 = ℓ
  have hP : ∀ (ℓ : ℕ) (h : ℓ < n), P ℓ ↔ (⟨ℓ, h⟩ : Fin n) ∈ S := by
    intro ℓ h
    constructor
    · rintro ⟨j, hj, rfl⟩; exact hj
    · intro hm; exact ⟨_, hm, rfl⟩
  obtain ⟨ℓ, hℓ, hadj⟩ := adj n P i0.1 j0.1 i0.2 j0.2 ⟨i0, hi0, rfl⟩
    (fun h => (Finset.mem_compl.1 hj0) (by
      obtain ⟨j, hj, hjj⟩ := h
      have : j = j0 := Fin.ext hjj
      rwa [this] at hj))
  have hmain : ∃ c : Fin k, ∀ p ∈ f.support, ∀ q ∈ g.support, ∃ a : ℕ → Fin k,
      a 0 = z hk ∧ a n = z hk ∧ a (ℓ + 1) = c ∧ p + q = path a n := by
    rcases hadj with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have hA' := (hP ℓ (by omega)).1 hA
      have hB' : (⟨ℓ + 1, hℓ⟩ : Fin n) ∈ Sᶜ := Finset.mem_compl.2 (fun h => hB ((hP _ hℓ).2 h))
      obtain ⟨c, hc⟩ := junction S Sᶜ ℓ hℓ hA' hB' (fun a => a 0 = z hk ∧ a n = z hk)
        (f.support : Set _) (g.support : Set _) mf hmf mg hmg
        (fun p hp q hq => hall p hp q hq)
      refine ⟨c, fun p hp q hq => ?_⟩
      obtain ⟨a, ⟨h0, hn'⟩, hpa, hqa, hca⟩ := hc p hp q hq
      exact ⟨a, h0, hn', hca, by rw [hpa, hqa, pathOn_add_compl]⟩
    · have hA' : (⟨ℓ, by omega⟩ : Fin n) ∈ Sᶜ := Finset.mem_compl.2 (fun h => hA ((hP _ (by omega)).2 h))
      have hB' := (hP _ hℓ).1 hB
      obtain ⟨c, hc⟩ := junction Sᶜ S ℓ hℓ hA' hB' (fun a => a 0 = z hk ∧ a n = z hk)
        (g.support : Set _) (f.support : Set _) mg hmg mf hmf
        (fun q hq p hp => by
          obtain ⟨a, hR, hpa, hqa⟩ := hall p hp q hq
          exact ⟨a, hR, hqa, hpa⟩)
      refine ⟨c, fun p hp q hq => ?_⟩
      obtain ⟨a, ⟨h0, hn'⟩, hqa, hpa, hca⟩ := hc q hq p hp
      exact ⟨a, h0, hn', hca, by rw [hpa, hqa, pathOn_add_compl]⟩
  obtain ⟨c, hc⟩ := hmain
  refine ⟨hn2, count_chain hk hn ℓ hℓ c _ ?_⟩
  intro m hm
  obtain ⟨p, hp, q, hq, rfl⟩ := (mem_support_mul_of_mono hf hg m).1 hm
  obtain ⟨a, h0, hn', hca, he⟩ := hc p hp q hq
  exact ⟨a, h0, hn', hca, he⟩

theorem imm_deg (hk : 0 < k) (hn : 0 < n) {m : IMMVar k n →₀ ℕ} (hm : m ∈ (imm ℝ k n).support) :
    m.degree = n := by
  obtain ⟨a, -, -, rfl⟩ := (mem_support_imm hk hn m).1 hm
  exact deg_path a

theorem layer_const (hk : 0 < k) (hn : 0 < n) (w : ℕ) (A : MABP (IMMVar k n)) (hrel : A.Relevant)
    (hsub : A.output.support ⊆ (imm ℝ k n).support)
    (hdense : (w : ℝ) / (k : ℝ) * ((imm ℝ k n).support.card : ℝ) < (A.output.support.card : ℝ))
    (hwid : ∀ i, A.layerSize i ≤ w) (i : Fin (A.depth + 1)) :
    ∃ v, Cn (A.prefix i v) ∨ Cn (A.suffix i v) := by
  classical
  by_contra hcon
  rw [not_exists] at hcon
  have hcon' : ∀ v, ¬ Cn (A.prefix i v) ∧ ¬ Cn (A.suffix i v) := fun v => not_or.1 (hcon v)
  have hhom : Homogeneous A.output :=
    ⟨n, isHom_of_support _ n (fun m hm => imm_deg hk hn (hsub hm))⟩
  have hv := (MonoABPWidth.Hierarchy.lemma_A_3 A hrel hhom).1
  -- the layer is nonempty
  have hne : ∃ v : Fin (A.layerSize i), True := by
    by_contra h
    have hemp : IsEmpty (Fin (A.layerSize i)) := ⟨fun v => h ⟨v, trivial⟩⟩
    have : A.output = 0 := by
      rw [← sum_prefix_suffix A i]
      exact Finset.sum_eq_zero (fun v _ => (hemp.false v).elim)
    rw [this] at hdense
    simp at hdense
    have : (0 : ℝ) ≤ (w : ℝ) / (k : ℝ) * ((imm ℝ k n).support.card : ℝ) := by positivity
    linarith
  obtain ⟨v0, -⟩ := hne
  have hcnt : ∀ v : Fin (A.layerSize i), 2 ≤ n ∧
      (A.prefix i v * A.suffix i v).support.card ≤ k ^ (n - 2) := by
    intro v
    refine vertex_count hk hn _ _ (prefix_mono A i v) (suffix_mono A i v) (hv i v).1 (hv i v).2
      (hcon' v).1 (hcon' v).2 ?_
    intro p hp q hq
    apply hsub
    apply vertex_support_subset A i v
    exact (mem_support_mul_of_mono (prefix_mono A i v) (suffix_mono A i v) _).2 ⟨p, hp, q, hq, rfl⟩
  have hn2 : 2 ≤ n := (hcnt v0).1
  have hcard : A.output.support.card ≤ w * k ^ (n - 2) := by
    have hsubU : A.output.support ⊆
        Finset.univ.biUnion (fun v : Fin (A.layerSize i) => (A.prefix i v * A.suffix i v).support) := by
      intro m hm
      rw [← sum_prefix_suffix A i, mem_support_sum_of_mono _ _
        (fun u _ => mono_mul (prefix_mono A _ u) (suffix_mono A _ u))] at hm
      obtain ⟨v, -, hv'⟩ := hm
      exact Finset.mem_biUnion.2 ⟨v, Finset.mem_univ _, hv'⟩
    calc A.output.support.card
        ≤ (Finset.univ.biUnion (fun v : Fin (A.layerSize i) =>
            (A.prefix i v * A.suffix i v).support)).card := Finset.card_le_card hsubU
      _ ≤ ∑ v : Fin (A.layerSize i), (A.prefix i v * A.suffix i v).support.card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _v : Fin (A.layerSize i), k ^ (n - 2) :=
          Finset.sum_le_sum (fun v _ => (hcnt v).2)
      _ = A.layerSize i * k ^ (n - 2) := by simp
      _ ≤ w * k ^ (n - 2) := Nat.mul_le_mul_right _ (hwid i)
  rw [card_support_imm hk hn] at hdense
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h1 : (w : ℝ) / (k : ℝ) * ((k ^ (m + 2 - 1) : ℕ) : ℝ) = (w : ℝ) * ((k : ℝ) ^ m) := by
    rw [show m + 2 - 1 = m + 1 by omega]
    push_cast
    field_simp
    ring
  have h2 : (A.output.support.card : ℝ) ≤ (w : ℝ) * ((k : ℝ) ^ m) := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    simpa using this
  rw [h1] at hdense
  linarith

end MonoABPWidth.Dev.L45b
end

section
set_option autoImplicit false
open scoped BigOperators

namespace MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.L45b MonoABPWidth.Dev.L45c in
theorem chk_lemma_4_5 (k n w : ℕ) (hn : 0 < n) (hw : 3 ≤ w) (hwk : w < k)
    (A : MABP (SetMultCost.IMMVar k n)) (hwidth : A.width ≤ w)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support)
    (hdense : (w : ℝ) / (k : ℝ) * ((SetMultCost.imm ℝ k n).support.card : ℝ) <
      (A.output.support.card : ℝ)) :
    ∃ (r : ℕ) (B : Fin r → MABP (SetMultCost.IMMVar k n)) (c : Fin r → ℝ),
      r ≤ A.depth ^ 2 ∧ (2 ≤ A.depth → r < A.depth ^ 2) ∧
      (∀ j : Fin r, 0 < c j ∧ (B j).width ≤ w - 1 ∧ (B j).depth ≤ A.depth ∧
        (B j).output.support ⊆ A.output.support) ∧
      A.output = ∑ j : Fin r, MvPolynomial.C (c j) * (B j).output := by
  have hk : 0 < k := by omega
  have hzero : A.output ≠ 0 := by
    intro h
    rw [h] at hdense
    simp at hdense
    have : (0 : ℝ) ≤ (w : ℝ) / (k : ℝ) * ((SetMultCost.imm ℝ k n).support.card : ℝ) := by positivity
    linarith
  obtain ⟨A', hw', hd', ⟨hrel, hnp, -⟩, hout⟩ := lemma_4_1 k n hk hn A hzero hsub
  have hsub' : A'.output.support ⊆ (SetMultCost.imm ℝ k n).support := hout ▸ hsub
  have hdense' : (w : ℝ) / (k : ℝ) * ((SetMultCost.imm ℝ k n).support.card : ℝ) <
      (A'.output.support.card : ℝ) := hout ▸ hdense
  have hwid : ∀ i, A'.layerSize i ≤ w := fun i =>
    (Finset.le_sup (f := A'.layerSize) (Finset.mem_univ i)).trans (hw'.trans hwidth)
  have hlay := layer_const hk hn w A' hrel hsub' hdense' hwid
  have hdis : ∀ i v, ¬ (Cn (A'.prefix i v) ∧ Cn (A'.suffix i v)) := by
    rintro i v ⟨h1, h2⟩
    obtain ⟨m0, hm0⟩ := support_nonempty_of_ne_zero (hrel i v).1
    obtain ⟨m1, hm1⟩ := support_nonempty_of_ne_zero (hrel i v).2
    have e0 := h1 m0 hm0
    have e1 := h2 m1 hm1
    have hm : m0 + m1 ∈ (A'.prefix i v * A'.suffix i v).support :=
      (mem_support_mul_of_mono (prefix_mono A' i v) (suffix_mono A' i v) _).2 ⟨m0, hm0, m1, hm1, rfl⟩
    have := hsub' (vertex_support_subset A' i v _ hm)
    have hdeg := imm_deg hk hn this
    rw [e0, e1, add_zero] at hdeg
    simp at hdeg
    omega
  obtain ⟨r, B, hr, hB, hsum⟩ := decomp A' hrel hnp w (by omega) hwid hlay hdis
  have hmul : (A'.depth + 1) * A'.depth ≤ (A.depth + 1) * A.depth :=
    Nat.mul_le_mul (by omega) hd'
  refine ⟨r, B, fun _ => 1, ?_, ?_, ?_, ?_⟩
  · nlinarith [Nat.zero_le A.depth]
  · intro h2
    nlinarith
  · intro j
    refine ⟨one_pos, (hB j).1, ?_, ?_⟩
    · rw [(hB j).2]; exact hd'
    · intro m hm
      have : m ∈ A'.output.support := by
        rw [hsum, mem_support_sum_of_mono _ _ (fun j _ => output_mono (B j))]
        exact ⟨j, Finset.mem_univ _, hm⟩
      rwa [hout] at this
  · rw [← hout, hsum]
    simp

end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_4_5 := @MonoABPWidth.Hierarchy.chk_lemma_4_5
