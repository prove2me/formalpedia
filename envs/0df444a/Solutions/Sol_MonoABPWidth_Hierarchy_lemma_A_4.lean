-- Prove2me | solution 1 for MonoABPWidth.Hierarchy.lemma_A_4
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T04:20:38.576077+00:00
-- url     : https://prove2.me/submissions/fd29e39e-fb05-4a45-8fae-b06ea0c5505f

import Mathlib
import Definitions.Def_MonoABPWidth_Hierarchy_simplicity
import Definitions.Def_SetMultCost_imm

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

namespace MonoABPWidth.Dev.LA4
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.Basic2 MonoABPWidth.Dev.IMM SetMultCost

variable {k n : ℕ}

theorem degree_pathOn (a : ℕ → Fin k) (T : Finset (Fin n)) : (pathOn a T).degree = T.card := by
  unfold pathOn
  rw [map_sum]
  simp [Finsupp.degree_single]

theorem pathOn_empty (a : ℕ → Fin k) : pathOn a (∅ : Finset (Fin n)) = 0 := by
  simp [pathOn]

theorem pathOn_singleton (a : ℕ → Fin k) (j : Fin n) :
    pathOn a {j} = Finsupp.single (pv a j) 1 := by
  simp [pathOn]

/-- two path-monomial completions of the same monomial `x` by a monomial of degree at most one agree -/
theorem key (hk : 0 < k) (hn : 0 < n) (x m1 m2 : IMMVar k n →₀ ℕ)
    (h1 : x + m1 ∈ (imm ℝ k n).support) (h2 : x + m2 ∈ (imm ℝ k n).support)
    (d1 : m1.degree ≤ 1) :
    m1 = m2 ∧ (m1 = 0 ∨ ∃ y, m1 = Finsupp.single y 1) := by
  classical
  obtain ⟨c, hc0, hcn, hc⟩ := (mem_support_imm hk hn _).1 h1
  obtain ⟨c', hc0', hcn', hc'⟩ := (mem_support_imm hk hn _).1 h2
  obtain ⟨S, hS1, hS2⟩ := split_path hc
  obtain ⟨S', hS1', hS2'⟩ := split_path hc'
  obtain ⟨hSS, hpv⟩ := pathOn_inj (hS1.symm.trans hS1')
  subst hSS
  have hcard : Sᶜ.card ≤ 1 := by
    rw [← degree_pathOn c, ← hS2]; exact d1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hcard with h0 | h1'
  · have : Sᶜ = ∅ := Finset.card_eq_zero.1 h0
    rw [hS2, hS2', this, pathOn_empty]
    exact ⟨rfl, Or.inl rfl⟩
  · obtain ⟨j0, hj0⟩ := Finset.card_eq_one.1 h1'
    rw [hS2, hS2', hj0, pathOn_singleton, pathOn_singleton]
    have hmem : ∀ j : Fin n, j ≠ j0 → j ∈ S := by
      intro j hj
      by_contra hjS
      have : j ∈ Sᶜ := Finset.mem_compl.2 hjS
      rw [hj0] at this
      exact hj (Finset.mem_singleton.1 this)
    have e1 : c j0 = c' j0 := by
      by_cases hz : (j0 : ℕ) = 0
      · rw [hz, hc0, hc0']
      · have hlt : (j0 : ℕ) - 1 < n := by omega
        have := ((pv_inj_iff (⟨(j0 : ℕ) - 1, hlt⟩ : Fin n)).1
          (hpv _ (hmem _ (fun h => by
            have := congrArg Fin.val h
            simp at this; omega)))).2
        simp only [show (j0 : ℕ) - 1 + 1 = j0 by omega] at this
        exact this
    have e2 : c ((j0 : ℕ) + 1) = c' ((j0 : ℕ) + 1) := by
      by_cases hz : (j0 : ℕ) + 1 = n
      · rw [hz, hcn, hcn']
      · have hlt : (j0 : ℕ) + 1 < n := by omega
        exact ((pv_inj_iff (⟨(j0 : ℕ) + 1, hlt⟩ : Fin n)).1
          (hpv _ (hmem _ (fun h => by
            have := congrArg Fin.val h
            simp at this)))).1
    have : pv c j0 = pv c' j0 := (pv_inj_iff j0).2 ⟨e1, e2⟩
    rw [this]
    exact ⟨rfl, Or.inr ⟨_, rfl⟩⟩

end MonoABPWidth.Dev.LA4

namespace MonoABPWidth.Hierarchy
open MonoABPWidth.Dev.Basic MonoABPWidth.Dev.Basic2 MonoABPWidth.Dev.LA4 in
theorem chk_lemma_A_4 (k n : ℕ) (hk : 0 < k) (hn : 0 < n)
    (A : MABP (SetMultCost.IMMVar k n)) (hrel : A.Relevant)
    (hsub : A.output.support ⊆ (SetMultCost.imm ℝ k n).support) :
    A.SingleTermEdges := by
  intro e u v
  by_cases h0 : (A.label e u v).poly = 0
  · left
    exact ⟨0, by simp [h0]⟩
  · obtain ⟨m0, hm0⟩ := support_nonempty_of_ne_zero h0
    obtain ⟨a, ha⟩ := support_nonempty_of_ne_zero (hrel e.castSucc u).1
    obtain ⟨b, hb⟩ := support_nonempty_of_ne_zero (hrel e.succ v).2
    have hall : ∀ m ∈ (A.label e u v).poly.support, m = m0 := by
      intro m hm
      have h1 := hsub (triple_mem_output A e u v ha hm hb)
      have h2 := hsub (triple_mem_output A e u v ha hm0 hb)
      have e1 : a + m + b = (a + b) + m := by abel
      have e2 : a + m0 + b = (a + b) + m0 := by abel
      rw [e1] at h1
      rw [e2] at h2
      exact (key hk hn (a + b) m m0 h1 h2 (label_degree_le_one _ hm)).1
    have hshape := (key hk hn (a + b) m0 m0
      (by have := hsub (triple_mem_output A e u v ha hm0 hb)
          rwa [show a + m0 + b = (a + b) + m0 by abel] at this)
      (by have := hsub (triple_mem_output A e u v ha hm0 hb)
          rwa [show a + m0 + b = (a + b) + m0 by abel] at this)
      (label_degree_le_one _ hm0)).2
    have hpoly : (A.label e u v).poly = MvPolynomial.monomial m0 ((A.label e u v).poly.coeff m0) := by
      ext m
      rw [MvPolynomial.coeff_monomial]
      by_cases hm : m = m0
      · subst hm; simp
      · rw [if_neg (fun h => hm h.symm)]
        by_contra hne
        exact hm (hall m (MvPolynomial.mem_support_iff.2 hne))
    obtain ⟨r, hr, hnn⟩ : ∃ r : ℝ, (A.label e u v).poly = MvPolynomial.monomial m0 r ∧ 0 ≤ r :=
      ⟨_, hpoly, mono_label _ m0⟩
    rcases hshape with h | ⟨y, hy⟩
    · left
      refine ⟨⟨r, hnn⟩, ?_⟩
      rw [hr, h, ← MvPolynomial.C_apply]
      rfl
    · right
      refine ⟨⟨r, hnn⟩, y, ?_⟩
      rw [hr, hy, MvPolynomial.X, MvPolynomial.C_mul_monomial, mul_one]
      rfl
end MonoABPWidth.Hierarchy
end

theorem solution : type_of% @MonoABPWidth.Hierarchy.chk_lemma_A_4 := @MonoABPWidth.Hierarchy.chk_lemma_A_4
