-- Prove2me | solution 1 for KunenZF.gaifman_elem_of_godel_cofinal
-- status  : ACCEPTED   (prove)
-- author  : @teargosling
-- created : 2026-11-27T05:18:05.347584+00:00
-- url     : https://prove2.me/submissions/2b1e4a3d-074d-4fd4-a9c7-5231bbd99038

import Mathlib.ModelTheory.Semantics
import Definitions.Def_CH_SetTheoryLanguage
import Definitions.Def_CH_ZFC
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory
import Definitions.Def_KunenZF_godel

universe u

open FirstOrder FirstOrder.Language ContinuumHypothesis ContinuumHypothesis.SFormula
open KunenZF KunenZF.SFormulaJ

namespace KunenZFGaifman

/-! ### Part 1: Generic `freeVarFinset` and realization helpers -/

private lemma realize_congr_freeVar {L : FirstOrder.Language} {M : Type u} [L.Structure M]
    {α : Type*} [DecidableEq α] {φ : L.Formula α} {v₁ v₂ : α → M}
    (h : ∀ a ∈ φ.freeVarFinset, v₁ a = v₂ a) :
    Formula.Realize φ v₁ ↔ Formula.Realize φ v₂ := by
  have h1 := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
    (v := fun a : φ.freeVarFinset => v₁ a.1) (xs := default) v₁ (fun _ => rfl)
  have h2 := BoundedFormula.realize_restrictFreeVar (φ := φ) (f := id)
    (v := fun a : φ.freeVarFinset => v₁ a.1) (xs := default) v₂ (fun a => h a.1 a.2)
  exact h1.symm.trans h2

private lemma varFinsetLeft_relabel_sumMap_id {L : FirstOrder.Language} {α : Type*}
    [DecidableEq α] {m n : ℕ} (f : Fin m → Fin n) (t : L.Term (α ⊕ Fin m)) :
    (t.relabel (Sum.map id f)).varFinsetLeft = t.varFinsetLeft := by
  induction t with
  | var x => cases x <;> simp [Term.relabel, Term.varFinsetLeft]
  | func g ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft]
    exact Finset.biUnion_congr rfl fun i _ => ih i

private lemma freeVarFinset_castLE {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {m n : ℕ} (h : m ≤ n) (φ : L.BoundedFormula α m) :
    (φ.castLE h).freeVarFinset = φ.freeVarFinset := by
  induction φ generalizing n with
  | falsum => rfl
  | equal t₁ t₂ =>
    simp [BoundedFormula.castLE, BoundedFormula.freeVarFinset, varFinsetLeft_relabel_sumMap_id]
  | rel R ts =>
    simp only [BoundedFormula.castLE, BoundedFormula.freeVarFinset, Function.comp_apply]
    exact Finset.biUnion_congr rfl fun i _ => varFinsetLeft_relabel_sumMap_id _ (ts i)
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp [BoundedFormula.castLE, BoundedFormula.freeVarFinset, ih₁ h, ih₂ h]
  | all φ ih =>
    simp [BoundedFormula.castLE, BoundedFormula.freeVarFinset, ih (Nat.succ_le_succ h)]

private lemma mem_varFinsetLeft_relabelAux {L : FirstOrder.Language} {α β : Type*}
    [DecidableEq α] [DecidableEq β] {k l : ℕ} (g : α → β ⊕ Fin k) (t : L.Term (α ⊕ Fin l))
    {v : β} (hv : v ∈ (t.relabel (BoundedFormula.relabelAux g l)).varFinsetLeft) :
    ∃ a ∈ t.varFinsetLeft, g a = Sum.inl v := by
  induction t with
  | var x =>
    cases x with
    | inl a =>
      simp only [Term.relabel, BoundedFormula.relabelAux, Function.comp_apply, Sum.map_inl] at hv
      cases hga : g a with
      | inl b =>
        rw [hga] at hv
        simp only [Equiv.sumAssoc_apply_inl_inl, Sum.map_inl, id_eq, Term.varFinsetLeft,
          Finset.mem_singleton] at hv
        exact ⟨a, by simp [Term.varFinsetLeft], by rw [hga, hv]⟩
      | inr i =>
        rw [hga] at hv
        simp [Term.varFinsetLeft] at hv
    | inr j =>
      simp [Term.relabel, BoundedFormula.relabelAux, Term.varFinsetLeft] at hv
  | func f ts ih =>
    simp only [Term.relabel, Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨i, hi⟩ := hv
    obtain ⟨a, ha, hga⟩ := ih i hi
    exact ⟨a, ⟨i, ha⟩, hga⟩

private lemma mem_freeVarFinset_relabel {L : FirstOrder.Language} {α β : Type*}
    [DecidableEq α] [DecidableEq β] {k n : ℕ} (g : α → β ⊕ Fin k) (φ : L.BoundedFormula α n)
    {v : β} (hv : v ∈ (φ.relabel g).freeVarFinset) :
    ∃ a ∈ φ.freeVarFinset, g a = Sum.inl v := by
  induction φ with
  | falsum => simp [BoundedFormula.relabel, BoundedFormula.mapTermRel] at hv
  | equal t₁ t₂ =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset,
      Finset.mem_union] at hv ⊢
    rcases hv with h₁ | h₂
    · obtain ⟨a, ha, hga⟩ := mem_varFinsetLeft_relabelAux g t₁ h₁
      exact ⟨a, Or.inl ha, hga⟩
    · obtain ⟨a, ha, hga⟩ := mem_varFinsetLeft_relabelAux g t₂ h₂
      exact ⟨a, Or.inr ha, hga⟩
  | rel R ts =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and] at hv ⊢
    obtain ⟨i, hi⟩ := hv
    obtain ⟨a, ha, hga⟩ := mem_varFinsetLeft_relabelAux g (ts i) hi
    exact ⟨a, ⟨i, ha⟩, hga⟩
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset,
      Finset.mem_union] at hv ⊢
    rcases hv with h₁ | h₂
    · obtain ⟨a, ha, hga⟩ := ih₁ h₁
      exact ⟨a, Or.inl ha, hga⟩
    · obtain ⟨a, ha, hga⟩ := ih₂ h₂
      exact ⟨a, Or.inr ha, hga⟩
  | all φ ih =>
    simp only [BoundedFormula.relabel, BoundedFormula.mapTermRel, BoundedFormula.freeVarFinset,
      freeVarFinset_castLE] at hv ⊢
    exact ih hv

private lemma freeVarFinset_alls {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {n : ℕ} (φ : L.BoundedFormula α n) : φ.alls.freeVarFinset = φ.freeVarFinset := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih φ.all

private lemma freeVarFinset_exs {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {n : ℕ} (φ : L.BoundedFormula α n) : φ.exs.freeVarFinset = φ.freeVarFinset := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (BoundedFormula.exs (∼(∀' ∼φ))).freeVarFinset = φ.freeVarFinset
    rw [ih]
    simp

private lemma mem_freeVarFinset_iAlls {L : FirstOrder.Language} {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Finite β] (φ : L.Formula (α ⊕ β))
    {v : α} (hv : v ∈ (Formula.iAlls β φ).freeVarFinset) :
    Sum.inl v ∈ φ.freeVarFinset := by
  simp only [Formula.iAlls, freeVarFinset_alls] at hv
  obtain ⟨a, ha, hga⟩ := mem_freeVarFinset_relabel _ φ hv
  cases a with
  | inl x =>
    simp only [Sum.map_inl, id_eq, Sum.inl.injEq] at hga
    rwa [hga] at ha
  | inr y => simp at hga

private lemma mem_freeVarFinset_iExs {L : FirstOrder.Language} {α β : Type*}
    [DecidableEq α] [DecidableEq β] [Finite β] (φ : L.Formula (α ⊕ β))
    {v : α} (hv : v ∈ (Formula.iExs β φ).freeVarFinset) :
    Sum.inl v ∈ φ.freeVarFinset := by
  simp only [Formula.iExs, freeVarFinset_exs] at hv
  obtain ⟨a, ha, hga⟩ := mem_freeVarFinset_relabel _ φ hv
  cases a with
  | inl x =>
    simp only [Sum.map_inl, id_eq, Sum.inl.injEq] at hga
    rwa [hga] at ha
  | inr y => simp at hga

private lemma mem_freeVarFinset_formula_relabel {L : FirstOrder.Language} {α β : Type*}
    [DecidableEq α] [DecidableEq β] (g : α → β) (φ : L.Formula α)
    {v : β} (hv : v ∈ (Formula.relabel g φ).freeVarFinset) :
    ∃ a ∈ φ.freeVarFinset, g a = v := by
  obtain ⟨a, ha, hga⟩ := mem_freeVarFinset_relabel (Sum.inl ∘ g) φ hv
  exact ⟨a, ha, Sum.inl.inj hga⟩

private lemma mem_freeVarFinset_all {x : ℕ} {φ : SFormula} {v : ℕ}
    (hv : v ∈ (all x φ).freeVarFinset) : v ∈ φ.freeVarFinset ∧ v ≠ x := by
  have h1 := mem_freeVarFinset_iAlls _ hv
  obtain ⟨a, ha, hga⟩ := mem_freeVarFinset_formula_relabel _ φ h1
  by_cases hax : a = x
  · simp [hax] at hga
  · simp only [hax, ↓reduceIte, Sum.inl.injEq] at hga
    subst hga
    exact ⟨ha, hax⟩

private lemma mem_freeVarFinset_ex {x : ℕ} {φ : SFormula} {v : ℕ}
    (hv : v ∈ (ex x φ).freeVarFinset) : v ∈ φ.freeVarFinset ∧ v ≠ x := by
  have h1 := mem_freeVarFinset_iExs _ hv
  obtain ⟨a, ha, hga⟩ := mem_freeVarFinset_formula_relabel _ φ h1
  by_cases hax : a = x
  · simp [hax] at hga
  · simp only [hax, ↓reduceIte, Sum.inl.injEq] at hga
    subst hga
    exact ⟨ha, hax⟩

private lemma mem_varFinsetLeft_onTerm {L L' : FirstOrder.Language} (f : L →ᴸ L')
    {α : Type*} [DecidableEq α] {n : ℕ} (t : L.Term (α ⊕ Fin n))
    {v : α} (hv : v ∈ (f.onTerm t).varFinsetLeft) : v ∈ t.varFinsetLeft := by
  induction t with
  | var x =>
    cases x with
    | inl a => simpa [LHom.onTerm, Term.varFinsetLeft] using hv
    | inr i => simp [LHom.onTerm, Term.varFinsetLeft] at hv
  | func g ts ih =>
    simp only [LHom.onTerm, Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ,
      true_and] at hv ⊢
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, ih i hi⟩

private lemma mem_freeVarFinset_onBoundedFormula {L L' : FirstOrder.Language} (f : L →ᴸ L')
    {α : Type*} [DecidableEq α] {n : ℕ} (φ : L.BoundedFormula α n)
    {v : α} (hv : v ∈ (f.onBoundedFormula φ).freeVarFinset) : v ∈ φ.freeVarFinset := by
  induction φ with
  | falsum => simp [LHom.onBoundedFormula] at hv
  | equal t₁ t₂ =>
    simp only [LHom.onBoundedFormula, Term.bdEqual, BoundedFormula.freeVarFinset,
      Finset.mem_union] at hv ⊢
    rcases hv with h₁ | h₂
    · exact Or.inl (mem_varFinsetLeft_onTerm f t₁ h₁)
    · exact Or.inr (mem_varFinsetLeft_onTerm f t₂ h₂)
  | rel R ts =>
    simp only [LHom.onBoundedFormula, Relations.boundedFormula, BoundedFormula.freeVarFinset,
      Finset.mem_biUnion, Finset.mem_univ, true_and, Function.comp_apply] at hv ⊢
    obtain ⟨i, hi⟩ := hv
    exact ⟨i, mem_varFinsetLeft_onTerm f (ts i) hi⟩
  | imp φ₁ φ₂ ih₁ ih₂ =>
    simp only [LHom.onBoundedFormula, BoundedFormula.freeVarFinset, Finset.mem_union] at hv ⊢
    rcases hv with h₁ | h₂
    · exact Or.inl (ih₁ h₁)
    · exact Or.inr (ih₂ h₂)
  | all φ ih =>
    simp only [LHom.onBoundedFormula, BoundedFormula.freeVarFinset] at hv ⊢
    exact ih hv

private lemma mem_freeVarFinset_mem {x y v : ℕ} (hv : v ∈ (mem x y).freeVarFinset) :
    v = x ∨ v = y := by
  simp only [mem, Relations.formula₂, Relations.formula, Relations.boundedFormula,
    BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
  obtain ⟨⟨i, hi⟩, hmem⟩ := hv
  match i with
  | 0 => simp [Term.relabel, Term.varFinsetLeft] at hmem; exact Or.inl hmem
  | 1 => simp [Term.relabel, Term.varFinsetLeft] at hmem; exact Or.inr hmem
  | _ + 2 => omega

private lemma mem_freeVarFinset_eq {x y v : ℕ} (hv : v ∈ (eq x y).freeVarFinset) :
    v = x ∨ v = y := by
  simp only [eq, Term.equal, Term.bdEqual, Term.relabel, BoundedFormula.freeVarFinset,
    Finset.mem_union, Term.varFinsetLeft, Finset.mem_singleton] at hv
  exact hv

private lemma mem_freeVarFinset_not {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {n : ℕ} {φ : L.BoundedFormula α n} {v : α} (hv : v ∈ (∼φ).freeVarFinset) :
    v ∈ φ.freeVarFinset := by
  simpa [BoundedFormula.not] using hv

private lemma mem_freeVarFinset_inf {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {n : ℕ} {φ ψ : L.BoundedFormula α n} {v : α} (hv : v ∈ (φ ⊓ ψ).freeVarFinset) :
    v ∈ φ.freeVarFinset ∨ v ∈ ψ.freeVarFinset := by
  change v ∈ (φ.imp ψ.not).not.freeVarFinset at hv
  simpa [BoundedFormula.not] using hv

private lemma mem_freeVarFinset_sup {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {n : ℕ} {φ ψ : L.BoundedFormula α n} {v : α} (hv : v ∈ (φ ⊔ ψ).freeVarFinset) :
    v ∈ φ.freeVarFinset ∨ v ∈ ψ.freeVarFinset := by
  change v ∈ (φ.not.imp ψ).freeVarFinset at hv
  simpa [BoundedFormula.not] using hv

private lemma mem_freeVarFinset_imp {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {n : ℕ} {φ ψ : L.BoundedFormula α n} {v : α} (hv : v ∈ (φ ⟹ ψ).freeVarFinset) :
    v ∈ φ.freeVarFinset ∨ v ∈ ψ.freeVarFinset := by
  simpa [BoundedFormula.freeVarFinset] using hv

private lemma mem_freeVarFinset_iff {L : FirstOrder.Language} {α : Type*} [DecidableEq α]
    {n : ℕ} {φ ψ : L.BoundedFormula α n} {v : α} (hv : v ∈ (φ ⇔ ψ).freeVarFinset) :
    v ∈ φ.freeVarFinset ∨ v ∈ ψ.freeVarFinset := by
  rcases mem_freeVarFinset_inf hv with h | h
  · exact mem_freeVarFinset_imp h
  · exact (mem_freeVarFinset_imp h).symm

/-! ### Part 2: Pure formulas for `Ord`, `Union`, `Chain` and free-variable bounds -/

noncomputable section

def isTransF (t : ℕ) : SFormula := all 2000 (mem 2000 t ⟹ subset 2000 t)
def isOrdF (α : ℕ) : SFormula := isTransF α ⊓ all 2001 (mem 2001 α ⟹ isTransF 2001)
def isUnionF (u x : ℕ) : SFormula :=
  all 2002 (mem 2002 u ⇔ ex 2003 (mem 2003 x ⊓ mem 2002 2003))

def isChainF (f n x : ℕ) : SFormula :=
  ex 2010 (isSucc 2010 n ⊓
    all 2011 (mem 2011 f ⟹ ex 2012 (mem 2012 2010 ⊓ ex 2013 (isPair 2011 2012 2013))) ⊓
    all 2012 (mem 2012 2010 ⟹ ex 2013 (pairIn f 2012 2013)) ⊓
    all 2012 (all 2013 (all 2014 ((pairIn f 2012 2013 ⊓ pairIn f 2012 2014) ⟹ eq 2013 2014))) ⊓
    all 2015 (isEmpty 2015 ⟹ all 2013 (pairIn f 2015 2013 ⟹ isSingleton 2013 x)) ⊓
    all 2012 (all 2016 (all 2013 (all 2014
      ((mem 2012 n ⊓ isSucc 2016 2012 ⊓ pairIn f 2012 2013 ⊓ pairIn f 2016 2014) ⟹
        isUnionF 2014 2013)))))

end

private lemma fv_subset {x y v : ℕ} (hv : v ∈ (subset x y).freeVarFinset) : v = x ∨ v = y := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_imp h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inl rfl]
  · rcases mem_freeVarFinset_mem h2 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr rfl]

private lemma fv_isEmpty {x v : ℕ} (hv : v ∈ (isEmpty x).freeVarFinset) : v = x := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_mem (mem_freeVarFinset_not h) with rfl | rfl
  · exact absurd rfl hne
  · rfl

private lemma fv_isSucc {s z v : ℕ} (hv : v ∈ (isSucc s z).freeVarFinset) : v = s ∨ v = z := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_iff h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inl rfl]
  · rcases mem_freeVarFinset_sup h2 with h3 | h4
    · rcases mem_freeVarFinset_mem h3 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr rfl]
    · rcases mem_freeVarFinset_eq h4 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr rfl]

private lemma fv_isInductive {w v : ℕ} (hv : v ∈ (isInductive w).freeVarFinset) : v = w := by
  rcases mem_freeVarFinset_inf hv with h1 | h2
  · obtain ⟨h, hne⟩ := mem_freeVarFinset_ex h1
    rcases mem_freeVarFinset_inf h with ha | hb
    · exact absurd (fv_isEmpty ha) hne
    · rcases mem_freeVarFinset_mem hb with rfl | rfl <;> [exact absurd rfl hne; rfl]
  · obtain ⟨h, hne4⟩ := mem_freeVarFinset_all h2
    rcases mem_freeVarFinset_imp h with ha | hb
    · rcases mem_freeVarFinset_mem ha with rfl | rfl <;> [exact absurd rfl hne4; rfl]
    · obtain ⟨hb', hne5⟩ := mem_freeVarFinset_ex hb
      rcases mem_freeVarFinset_inf hb' with hc | hd
      · rcases fv_isSucc hc with rfl | rfl <;> [exact absurd rfl hne5; exact absurd rfl hne4]
      · rcases mem_freeVarFinset_mem hd with rfl | rfl <;> [exact absurd rfl hne5; rfl]

private lemma fv_isSingleton {t a v : ℕ} (hv : v ∈ (isSingleton t a).freeVarFinset) :
    v = t ∨ v = a := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_iff h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inl rfl]
  · rcases mem_freeVarFinset_eq h2 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr rfl]

private lemma fv_isDoubleton {t a b v : ℕ} (hv : v ∈ (isDoubleton t a b).freeVarFinset) :
    v = t ∨ v = a ∨ v = b := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_iff h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inl rfl]
  · rcases mem_freeVarFinset_sup h2 with h3 | h4
    · rcases mem_freeVarFinset_eq h3 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr (Or.inl rfl)]
    · rcases mem_freeVarFinset_eq h4 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr (Or.inr rfl)]

private lemma fv_isPair {z a b v : ℕ} (hv : v ∈ (isPair z a b).freeVarFinset) :
    v = z ∨ v = a ∨ v = b := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_iff h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inl rfl]
  · rcases mem_freeVarFinset_sup h2 with h3 | h4
    · rcases fv_isSingleton h3 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr (Or.inl rfl)]
    · rcases fv_isDoubleton h4 with rfl | rfl | rfl
      · exact absurd rfl hne
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

private lemma fv_pairIn {f a b v : ℕ} (hv : v ∈ (pairIn f a b).freeVarFinset) :
    v = f ∨ v = a ∨ v = b := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_ex hv
  rcases mem_freeVarFinset_inf h with h1 | h2
  · rcases fv_isPair h1 with rfl | rfl | rfl
    · exact absurd rfl hne
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rcases mem_freeVarFinset_mem h2 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inl rfl]

private lemma fv_isTransF {t v : ℕ} (hv : v ∈ (isTransF t).freeVarFinset) : v = t := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_imp h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne; rfl]
  · rcases fv_subset h2 with rfl | rfl <;> [exact absurd rfl hne; rfl]

private lemma fv_isOrdF {α v : ℕ} (hv : v ∈ (isOrdF α).freeVarFinset) : v = α := by
  rcases mem_freeVarFinset_inf hv with h1 | h2
  · exact fv_isTransF h1
  · obtain ⟨h, hne⟩ := mem_freeVarFinset_all h2
    rcases mem_freeVarFinset_imp h with ha | hb
    · rcases mem_freeVarFinset_mem ha with rfl | rfl <;> [exact absurd rfl hne; rfl]
    · exact absurd (fv_isTransF hb) hne

private lemma fv_isUnionF {u x v : ℕ} (hv : v ∈ (isUnionF u x).freeVarFinset) : v = u ∨ v = x := by
  obtain ⟨h, hne2⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_iff h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne2; exact Or.inl rfl]
  · obtain ⟨h2', hne3⟩ := mem_freeVarFinset_ex h2
    rcases mem_freeVarFinset_inf h2' with ha | hb
    · rcases mem_freeVarFinset_mem ha with rfl | rfl <;> [exact absurd rfl hne3; exact Or.inr rfl]
    · rcases mem_freeVarFinset_mem hb with rfl | rfl <;> [exact absurd rfl hne2; exact absurd rfl hne3]

private lemma fv_isChainF {f n x v : ℕ} (hv : v ∈ (isChainF f n x).freeVarFinset) :
    v = f ∨ v = n ∨ v = x := by
  obtain ⟨h, hne10⟩ := mem_freeVarFinset_ex hv
  rcases mem_freeVarFinset_inf h with h12345 | h6
  · rcases mem_freeVarFinset_inf h12345 with h1234 | h5
    · rcases mem_freeVarFinset_inf h1234 with h123 | h4
      · rcases mem_freeVarFinset_inf h123 with h12 | h3
        · rcases mem_freeVarFinset_inf h12 with h1 | h2
          · rcases fv_isSucc h1 with rfl | rfl <;> [exact absurd rfl hne10; exact Or.inr (Or.inl rfl)]
          · obtain ⟨h2, hne11⟩ := mem_freeVarFinset_all h2
            rcases mem_freeVarFinset_imp h2 with ha | hb
            · rcases mem_freeVarFinset_mem ha with rfl | rfl <;> [exact absurd rfl hne11; exact Or.inl rfl]
            · obtain ⟨hb, hne12⟩ := mem_freeVarFinset_ex hb
              rcases mem_freeVarFinset_inf hb with hc | hd
              · rcases mem_freeVarFinset_mem hc with rfl | rfl <;> [exact absurd rfl hne12; exact absurd rfl hne10]
              · obtain ⟨hd, hne13⟩ := mem_freeVarFinset_ex hd
                rcases fv_isPair hd with rfl | rfl | rfl <;>
                  [exact absurd rfl hne11; exact absurd rfl hne12; exact absurd rfl hne13]
        · obtain ⟨h3, hne12⟩ := mem_freeVarFinset_all h3
          rcases mem_freeVarFinset_imp h3 with ha | hb
          · rcases mem_freeVarFinset_mem ha with rfl | rfl <;> [exact absurd rfl hne12; exact absurd rfl hne10]
          · obtain ⟨hb, hne13⟩ := mem_freeVarFinset_ex hb
            rcases fv_pairIn hb with rfl | rfl | rfl <;>
              [exact Or.inl rfl; exact absurd rfl hne12; exact absurd rfl hne13]
      · obtain ⟨h4, hne12⟩ := mem_freeVarFinset_all h4
        obtain ⟨h4, hne13⟩ := mem_freeVarFinset_all h4
        obtain ⟨h4, hne14⟩ := mem_freeVarFinset_all h4
        rcases mem_freeVarFinset_imp h4 with ha | hb
        · rcases mem_freeVarFinset_inf ha with hc | hd
          · rcases fv_pairIn hc with rfl | rfl | rfl <;>
              [exact Or.inl rfl; exact absurd rfl hne12; exact absurd rfl hne13]
          · rcases fv_pairIn hd with rfl | rfl | rfl <;>
              [exact Or.inl rfl; exact absurd rfl hne12; exact absurd rfl hne14]
        · rcases mem_freeVarFinset_eq hb with rfl | rfl <;> [exact absurd rfl hne13; exact absurd rfl hne14]
    · obtain ⟨h5, hne15⟩ := mem_freeVarFinset_all h5
      rcases mem_freeVarFinset_imp h5 with ha | hb
      · exact absurd (fv_isEmpty ha) hne15
      · obtain ⟨hb, hne13⟩ := mem_freeVarFinset_all hb
        rcases mem_freeVarFinset_imp hb with hc | hd
        · rcases fv_pairIn hc with rfl | rfl | rfl <;>
            [exact Or.inl rfl; exact absurd rfl hne15; exact absurd rfl hne13]
        · rcases fv_isSingleton hd with rfl | rfl <;> [exact absurd rfl hne13; exact Or.inr (Or.inr rfl)]
  · obtain ⟨h6, hne12⟩ := mem_freeVarFinset_all h6
    obtain ⟨h6, hne16⟩ := mem_freeVarFinset_all h6
    obtain ⟨h6, hne13⟩ := mem_freeVarFinset_all h6
    obtain ⟨h6, hne14⟩ := mem_freeVarFinset_all h6
    rcases mem_freeVarFinset_imp h6 with ha | hb
    · rcases mem_freeVarFinset_inf ha with ha123 | ha4
      · rcases mem_freeVarFinset_inf ha123 with ha12 | ha3
        · rcases mem_freeVarFinset_inf ha12 with ha1 | ha2
          · rcases mem_freeVarFinset_mem ha1 with rfl | rfl <;> [exact absurd rfl hne12; exact Or.inr (Or.inl rfl)]
          · rcases fv_isSucc ha2 with rfl | rfl <;> [exact absurd rfl hne16; exact absurd rfl hne12]
        · rcases fv_pairIn ha3 with rfl | rfl | rfl <;>
            [exact Or.inl rfl; exact absurd rfl hne12; exact absurd rfl hne13]
      · rcases fv_pairIn ha4 with rfl | rfl | rfl <;>
          [exact Or.inl rfl; exact absurd rfl hne16; exact absurd rfl hne14]
    · rcases fv_isUnionF hb with rfl | rfl <;> [exact absurd rfl hne14; exact absurd rfl hne13]

/-! ### Part 3: Semantic bridge and `ZFj` axiom extractors -/

section Semantics

variable {M : Type u} [setLangJ.Structure M]

local instance setLangReduct : setLang.Structure M := incl.reduct M

def Sub (a b : M) : Prop := ∀ z : M, MemRelM z a → MemRelM z b
def IsEmp (e : M) : Prop := ∀ z : M, ¬ MemRelM z e
def IsSucc (s a : M) : Prop := ∀ z : M, MemRelM z s ↔ MemRelM z a ∨ z = a
def IsInd (w : M) : Prop :=
  (∃ e : M, IsEmp e ∧ MemRelM e w) ∧ ∀ a : M, MemRelM a w → ∃ s : M, IsSucc s a ∧ MemRelM s w
def IsPow (p x : M) : Prop := ∀ z : M, MemRelM z p ↔ Sub z x
def PairIn (f a b : M) : Prop := ∃ p : M, IsPairM p a b ∧ MemRelM p f
def Trans (t : M) : Prop := ∀ x : M, MemRelM x t → Sub x t
def Ord (α : M) : Prop := Trans α ∧ ∀ β : M, MemRelM β α → Trans β

def IsChain (f n x : M) : Prop :=
  ∃ s : M, IsSucc s n ∧
    (∀ p : M, MemRelM p f → ∃ k : M, MemRelM k s ∧ ∃ v : M, IsPairM p k v) ∧
    (∀ k : M, MemRelM k s → ∃ v : M, PairIn f k v) ∧
    (∀ k v₁ v₂ : M, PairIn f k v₁ → PairIn f k v₂ → v₁ = v₂) ∧
    (∀ e : M, IsEmp e → ∀ v : M, PairIn f e v → IsSingM v x) ∧
    (∀ k k' v v' : M, MemRelM k n → IsSucc k' k → PairIn f k v → PairIn f k' v' → IsUnionM v' v)

private lemma realize_mem (v : ℕ → M) (x y : ℕ) :
    Formula.Realize (mem x y) v ↔ MemRelM (v x) (v y) := by
  rw [mem, Formula.realize_rel₂]; rfl

private lemma realize_eq (v : ℕ → M) (x y : ℕ) :
    Formula.Realize (eq x y) v ↔ v x = v y := by
  rw [eq, Formula.realize_equal]; rfl

private lemma realize_all (v : ℕ → M) (x : ℕ) (φ : SFormula) :
    Formula.Realize (all x φ) v ↔ ∀ a : M, Formula.Realize φ (Function.update v x a) := by
  simp only [all, Formula.realize_iAlls, Formula.realize_relabel]
  constructor
  · intro h a
    convert h (fun _ => a) using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]
  · intro h i
    convert h (i ()) using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]

private lemma realize_ex (v : ℕ → M) (x : ℕ) (φ : SFormula) :
    Formula.Realize (ex x φ) v ↔ ∃ a : M, Formula.Realize φ (Function.update v x a) := by
  simp only [ex, Formula.realize_iExs, Formula.realize_relabel]
  constructor
  · rintro ⟨i, h⟩
    refine ⟨i (), ?_⟩
    convert h using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]
  · rintro ⟨a, h⟩
    refine ⟨fun _ => a, ?_⟩
    convert h using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]

private lemma realize_memJ (v : ℕ → M) (x y : ℕ) :
    Formula.Realize (memJ x y) v ↔ MemRelM (v x) (v y) := by
  rw [memJ, Formula.realize_rel₂]; rfl

private lemma realize_allJ (v : ℕ → M) (x : ℕ) (φ : SFormulaJ) :
    Formula.Realize (allJ x φ) v ↔ ∀ a : M, Formula.Realize φ (Function.update v x a) := by
  simp only [allJ, Formula.realize_iAlls, Formula.realize_relabel]
  constructor
  · intro h a
    convert h (fun _ => a) using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]
  · intro h i
    convert h (i ()) using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]

private lemma realize_exJ (v : ℕ → M) (x : ℕ) (φ : SFormulaJ) :
    Formula.Realize (exJ x φ) v ↔ ∃ a : M, Formula.Realize φ (Function.update v x a) := by
  simp only [exJ, Formula.realize_iExs, Formula.realize_relabel]
  constructor
  · rintro ⟨i, h⟩
    refine ⟨i (), ?_⟩
    convert h using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]
  · rintro ⟨a, h⟩
    refine ⟨fun _ => a, ?_⟩
    convert h using 2
    ext n; by_cases hn : n = x <;> simp [hn, Function.update]

private lemma realize_of_close {φ : SFormula} (h : M ⊨ close φ) (v : ℕ → M) :
    Formula.Realize φ v := by
  simp only [Sentence.Realize, close, Formula.realize_iAlls, Formula.realize_relabel] at h
  have h1 := h (fun i => v i.1)
  refine (realize_congr_freeVar ?_).mp h1
  intro a ha
  have hlt : a < varBound φ + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  simp [Function.comp, Nat.mod_eq_of_lt hlt]

private lemma realize_of_closeJ {φ : SFormulaJ} (h : M ⊨ closeJ φ) (v : ℕ → M) :
    Formula.Realize φ v := by
  simp only [Sentence.Realize, closeJ, Formula.realize_iAlls, Formula.realize_relabel] at h
  have h1 := h (fun i => v i.1)
  refine (realize_congr_freeVar ?_).mp h1
  intro a ha
  have hlt : a < varBoundJ φ + 1 := Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  simp [Function.comp, Nat.mod_eq_of_lt hlt]

private lemma realize_onBoundedFormula_formula (φ : SFormula) (v : ℕ → M) :
    Formula.Realize (incl.onBoundedFormula φ) v ↔ Formula.Realize φ v :=
  LHom.realize_onFormula incl φ

private lemma r_subset (v : ℕ → M) {x y : ℕ} (hx : x ≠ 1000) (hy : y ≠ 1000) :
    Formula.Realize (subset x y) v ↔ Sub (v x) (v y) := by
  simp [subset, Sub, realize_all, realize_mem, Function.update_of_ne hx, Function.update_of_ne hy]

private lemma r_isEmpty (v : ℕ → M) {x : ℕ} (hx : x ≠ 1001) :
    Formula.Realize (isEmpty x) v ↔ IsEmp (v x) := by
  simp [isEmpty, IsEmp, realize_all, realize_mem, Function.update_of_ne hx]

private lemma r_isSucc (v : ℕ → M) {s z : ℕ} (hs : s ≠ 1002) (hz : z ≠ 1002) :
    Formula.Realize (isSucc s z) v ↔ IsSucc (v s) (v z) := by
  simp [isSucc, IsSucc, realize_all, realize_mem, realize_eq,
    Function.update_of_ne hs, Function.update_of_ne hz]

private lemma r_isInductive (v : ℕ → M) {w : ℕ} (hw : w < 1000) :
    Formula.Realize (isInductive w) v ↔ IsInd (v w) := by
  simp only [isInductive, IsInd, Formula.realize_inf, realize_ex, realize_all,
    Formula.realize_imp, realize_mem,
    r_isEmpty _ (by omega : (1003 : ℕ) ≠ 1001),
    r_isSucc _ (by omega : (1005 : ℕ) ≠ 1002) (by omega : (1004 : ℕ) ≠ 1002)]
  simp [Function.update_of_ne (by omega : w ≠ 1003),
    Function.update_of_ne (by omega : w ≠ 1004),
    Function.update_of_ne (by omega : w ≠ 1005)]

private lemma r_isPowerset (v : ℕ → M) {p x : ℕ} (hp : p ≠ 1007) (hx : x ≠ 1007) (hx0 : x ≠ 1000) :
    Formula.Realize (isPowerset p x) v ↔ IsPow (v p) (v x) := by
  simp [isPowerset, IsPow, realize_all, realize_mem, r_subset _ (by omega : (1007 : ℕ) ≠ 1000) hx0,
    Function.update_of_ne hp, Function.update_of_ne hx]

private lemma r_isSingleton (v : ℕ → M) {t a : ℕ} (ht : t ≠ 1008) (ha : a ≠ 1008) :
    Formula.Realize (isSingleton t a) v ↔ IsSingM (v t) (v a) := by
  simp [isSingleton, IsSingM, realize_all, realize_mem, realize_eq,
    Function.update_of_ne ht, Function.update_of_ne ha]

private lemma r_isDoubleton (v : ℕ → M) {t a b : ℕ} (ht : t ≠ 1009) (ha : a ≠ 1009) (hb : b ≠ 1009) :
    Formula.Realize (isDoubleton t a b) v ↔ IsDblM (v t) (v a) (v b) := by
  simp [isDoubleton, IsDblM, realize_all, realize_mem, realize_eq,
    Function.update_of_ne ht, Function.update_of_ne ha, Function.update_of_ne hb]

private lemma r_isPair (v : ℕ → M) {z a b : ℕ}
    (hz : z ≠ 1010) (ha : a ≠ 1008 ∧ a ≠ 1009 ∧ a ≠ 1010) (hb : b ≠ 1009 ∧ b ≠ 1010) :
    Formula.Realize (isPair z a b) v ↔ IsPairM (v z) (v a) (v b) := by
  simp only [isPair, IsPairM, realize_all, Formula.realize_iff, realize_mem,
    Formula.realize_sup,
    r_isSingleton _ (by omega : (1010 : ℕ) ≠ 1008) ha.1,
    r_isDoubleton _ (by omega : (1010 : ℕ) ≠ 1009) ha.2.1 hb.1]
  simp [Function.update_of_ne hz, Function.update_of_ne ha.2.2, Function.update_of_ne hb.2]

private lemma r_pairIn (v : ℕ → M) {f a b : ℕ}
    (hf : f ≠ 1011)
    (ha : a ≠ 1008 ∧ a ≠ 1009 ∧ a ≠ 1010 ∧ a ≠ 1011)
    (hb : b ≠ 1009 ∧ b ≠ 1010 ∧ b ≠ 1011) :
    Formula.Realize (pairIn f a b) v ↔ PairIn (v f) (v a) (v b) := by
  simp only [pairIn, PairIn, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair _ (by omega : (1011 : ℕ) ≠ 1010) ⟨ha.1, ha.2.1, ha.2.2.1⟩ ⟨hb.1, hb.2.1⟩]
  simp [Function.update_of_ne hf, Function.update_of_ne ha.2.2.2, Function.update_of_ne hb.2.2]

private lemma r_isTransF (v : ℕ → M) {t : ℕ} (ht : t ≠ 1000 ∧ t ≠ 2000) :
    Formula.Realize (isTransF t) v ↔ Trans (v t) := by
  simp [isTransF, Trans, realize_all, realize_mem, r_subset _ (by omega : (2000 : ℕ) ≠ 1000) ht.1,
    Function.update_of_ne ht.2]

private lemma r_isOrdF (v : ℕ → M) {α : ℕ} (hα : α ≠ 1000 ∧ α ≠ 2000 ∧ α ≠ 2001) :
    Formula.Realize (isOrdF α) v ↔ Ord (v α) := by
  simp [isOrdF, Ord, realize_all, realize_mem,
    r_isTransF (t := α) _ ⟨hα.1, hα.2.1⟩,
    r_isTransF (t := 2001) _ ⟨by omega, by omega⟩,
    Function.update_of_ne hα.2.2]

private lemma r_isUnionF (v : ℕ → M) {u x : ℕ}
    (hu : u ≠ 2002 ∧ u ≠ 2003) (hx : x ≠ 2002 ∧ x ≠ 2003) :
    Formula.Realize (isUnionF u x) v ↔ IsUnionM (v u) (v x) := by
  simp only [isUnionF, IsUnionM, realize_all, realize_ex, Formula.realize_iff,
    Formula.realize_inf, realize_mem]
  simp [Function.update_of_ne hu.1, Function.update_of_ne hx.1, Function.update_of_ne hx.2]

private lemma r_isChainF (v : ℕ → M) {f n x : ℕ} (hf : f < 1000) (hn : n < 1000) (hx : x < 1000) :
    Formula.Realize (isChainF f n x) v ↔ IsChain (v f) (v n) (v x) := by
  simp only [isChainF, IsChain, realize_ex, realize_all, Formula.realize_inf,
    Formula.realize_imp, realize_mem, realize_eq,
    r_isSucc (s := 2010) (z := n) _ (by omega) (by omega),
    r_isPair (z := 2011) (a := 2012) (b := 2013) _ (by omega)
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_pairIn (f := f) (a := 2012) (b := 2013) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩,
    r_pairIn (f := f) (a := 2012) (b := 2014) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩,
    r_pairIn (f := f) (a := 2015) (b := 2013) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩,
    r_pairIn (f := f) (a := 2016) (b := 2014) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩,
    r_isEmpty (x := 2015) _ (by omega),
    r_isSingleton (t := 2013) (a := x) _ (by omega) (by omega),
    r_isSucc (s := 2016) (z := 2012) _ (by omega) (by omega),
    r_isUnionF (u := 2014) (x := 2013) _ ⟨by omega, by omega⟩ ⟨by omega, by omega⟩]
  simp only [Function.update_self,
    Function.update_of_ne (by omega : f ≠ 2010),
    Function.update_of_ne (by omega : f ≠ 2011),
    Function.update_of_ne (by omega : f ≠ 2012),
    Function.update_of_ne (by omega : f ≠ 2013),
    Function.update_of_ne (by omega : f ≠ 2014),
    Function.update_of_ne (by omega : f ≠ 2015),
    Function.update_of_ne (by omega : f ≠ 2016),
    Function.update_of_ne (by omega : n ≠ 2010),
    Function.update_of_ne (by omega : n ≠ 2012),
    Function.update_of_ne (by omega : n ≠ 2013),
    Function.update_of_ne (by omega : n ≠ 2014),
    Function.update_of_ne (by omega : n ≠ 2016),
    Function.update_of_ne (by omega : x ≠ 2010),
    Function.update_of_ne (by omega : x ≠ 2013),
    Function.update_of_ne (by omega : x ≠ 2015),
    Function.update_of_ne (by omega : (2010 : ℕ) ≠ 2011),
    Function.update_of_ne (by omega : (2010 : ℕ) ≠ 2012),
    Function.update_of_ne (by omega : (2011 : ℕ) ≠ 2012),
    Function.update_of_ne (by omega : (2011 : ℕ) ≠ 2013),
    Function.update_of_ne (by omega : (2012 : ℕ) ≠ 2013),
    Function.update_of_ne (by omega : (2012 : ℕ) ≠ 2014),
    Function.update_of_ne (by omega : (2012 : ℕ) ≠ 2016),
    Function.update_of_ne (by omega : (2013 : ℕ) ≠ 2014),
    Function.update_of_ne (by omega : (2015 : ℕ) ≠ 2013),
    Function.update_of_ne (by omega : (2016 : ℕ) ≠ 2013),
    Function.update_of_ne (by omega : (2016 : ℕ) ≠ 2014)]
  constructor
  · rintro ⟨s, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩⟩
    exact ⟨s, h1, h2, h3, fun k v₁ v₂ a b => h4 k v₁ v₂ ⟨a, b⟩, h5,
      fun k k' v₁ v₂ a b c d => h6 k k' v₁ v₂ ⟨⟨⟨a, b⟩, c⟩, d⟩⟩
  · rintro ⟨s, h1, h2, h3, h4, h5, h6⟩
    exact ⟨s, ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, fun k v₁ v₂ ⟨a, b⟩ => h4 k v₁ v₂ a b⟩, h5⟩,
      fun k k' v₁ v₂ ⟨⟨⟨a, b⟩, c⟩, d⟩ => h6 k k' v₁ v₂ a b c d⟩⟩

private lemma ord_emp {e : M} (he : IsEmp e) : Ord e :=
  ⟨fun x hx => absurd hx (he x), fun β hβ => absurd hβ (he β)⟩

private lemma ord_mem {α β : M} (hα : Ord α) (hβα : MemRelM β α) : Ord β :=
  ⟨hα.2 β hβα, fun γ hγβ => hα.2 γ (hα.1 β hβα γ hγβ)⟩

private lemma ord_succ {α s : M} (hα : Ord α) (hs : IsSucc s α) : Ord s := by
  refine ⟨fun x hx z hzx => ?_, fun β hβ => ?_⟩
  · rcases (hs x).mp hx with hxα | rfl
    · exact (hs z).mpr (Or.inl (hα.1 x hxα z hzx))
    · exact (hs z).mpr (Or.inl hzx)
  · rcases (hs β).mp hβ with hβα | rfl
    · exact hα.2 β hβα
    · exact hα.1

variable (hM : M ⊨ ZFj)
include hM

private lemma model_zf_axiom {φ : SFormula} (hφ : φ ∈ ZFAxioms) :
    ∀ v : ℕ → M, Formula.Realize φ v := by
  intro v
  have hmem : incl.onSentence (close φ) ∈ ZFj :=
    Or.inl (Or.inl ⟨close φ, ⟨φ, hφ, rfl⟩, rfl⟩)
  have hreal : M ⊨ incl.onSentence (close φ) := hM.realize_of_mem _ hmem
  rw [LHom.realize_onSentence] at hreal
  exact realize_of_close hreal v

private lemma ax_ext (x y : M) (h : ∀ z : M, MemRelM z x ↔ MemRelM z y) : x = y := by
  have h0 := model_zf_axiom (φ := extensionality) hM (Or.inl (Or.inl (by simp))) (fun _ => x)
  simp only [extensionality, realize_all, Formula.realize_imp, Formula.realize_iff,
    realize_mem, realize_eq] at h0
  exact h0 x y (by simpa using h)

private lemma ax_found (x : M) (hne : ∃ y : M, MemRelM y x) :
    ∃ y : M, MemRelM y x ∧ ∀ z : M, ¬ (MemRelM z y ∧ MemRelM z x) := by
  have h0 := model_zf_axiom (φ := foundation) hM (Or.inl (Or.inl (by simp))) (fun _ => x)
  simp only [foundation, realize_all, realize_ex, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, realize_mem] at h0
  simpa using h0 x hne

private lemma ax_pair (a b : M) : ∃ p : M, IsDblM p a b := by
  have h0 := model_zf_axiom (φ := pairing) hM (Or.inl (Or.inl (by simp))) (fun _ => a)
  simp only [pairing, realize_all, realize_ex,
    r_isDoubleton _ (by omega : (2 : ℕ) ≠ 1009) (by omega : (0 : ℕ) ≠ 1009)
      (by omega : (1 : ℕ) ≠ 1009)] at h0
  simpa using h0 a b

private lemma ax_union (x : M) : ∃ u : M, IsUnionM u x := by
  have h0 := model_zf_axiom (φ := union) hM (Or.inl (Or.inl (by simp))) (fun _ => x)
  simp only [union, realize_all, realize_ex, Formula.realize_iff,
    Formula.realize_inf, realize_mem] at h0
  simpa [IsUnionM] using h0 x

private lemma ax_powerset (x : M) : ∃ p : M, IsPow p x := by
  have h0 := model_zf_axiom (φ := powerset) hM (Or.inl (Or.inl (by simp))) (fun _ => x)
  simp only [powerset, realize_all, realize_ex,
    r_isPowerset _ (by omega : (1 : ℕ) ≠ 1007) (by omega : (0 : ℕ) ≠ 1007)
      (by omega : (0 : ℕ) ≠ 1000)] at h0
  simpa using h0 x

private lemma ax_infinity [Nonempty M] : ∃ w : M, IsInd w := by
  have h0 := model_zf_axiom (φ := infinity) hM (Or.inl (Or.inl (by simp))) (fun _ => Classical.arbitrary M)
  simp only [infinity, realize_ex, r_isInductive _ (by omega : (0 : ℕ) < 1000)] at h0
  simpa using h0

private lemma ax_sepJ (φ : SFormulaJ) (x a b : ℕ) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (hb : b ∉ φ.freeVarFinset) (v : ℕ → M) :
    ∃ B : M, ∀ z : M, MemRelM z B ↔ MemRelM z (v a) ∧ Formula.Realize φ (Function.update v x z) := by
  let σ : SFormulaJ := allJ a (exJ b (allJ x (memJ x b ⇔ (memJ x a ⊓ φ))))
  have hσ : IsSeparationJ σ := ⟨φ, x, a, b, hxa, hxb, hab, hb, rfl⟩
  have hmem : closeJ σ ∈ ZFj := Or.inl (Or.inr ⟨σ, hσ, rfl⟩)
  have hreal := realize_of_closeJ (hM.realize_of_mem _ hmem) v
  simp only [σ, realize_allJ, realize_exJ, Formula.realize_iff,
    Formula.realize_inf, realize_memJ] at hreal
  obtain ⟨B, hB⟩ := hreal (v a)
  refine ⟨B, fun z => ?_⟩
  have hz := hB z
  simp only [Function.update_self, Function.update_of_ne hxb.symm, Function.update_of_ne hxa.symm,
    Function.update_of_ne hab] at hz
  rw [hz]
  refine and_congr_right fun _ => realize_congr_freeVar fun n hn => ?_
  have hnb : n ≠ b := fun h => hb (h ▸ hn)
  by_cases hnx : n = x
  · subst hnx; simp
  · by_cases hna : n = a
    · subst hna; simp [hxa.symm, hnb]
    · simp [hnx, hnb]

private lemma ax_sep (φ : SFormula) (x a b : ℕ) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (hb : b ∉ φ.freeVarFinset) (v : ℕ → M) :
    ∃ B : M, ∀ z : M, MemRelM z B ↔ MemRelM z (v a) ∧ Formula.Realize φ (Function.update v x z) := by
  have hbJ : b ∉ (incl.onBoundedFormula φ).freeVarFinset := fun h =>
    hb (mem_freeVarFinset_onBoundedFormula incl φ h)
  obtain ⟨B, hB⟩ := ax_sepJ hM (incl.onBoundedFormula φ) x a b hxa hxb hab hbJ v
  refine ⟨B, fun z => ?_⟩
  simpa [realize_onBoundedFormula_formula] using hB z

private lemma ax_collJ (φ : SFormulaJ) (x y a b : ℕ) (hnodup : [x, y, a, b].Nodup)
    (hb : b ∉ φ.freeVarFinset) (v : ℕ → M)
    (htot : ∀ u : M, MemRelM u (v a) →
      ∃ w : M, Formula.Realize φ (Function.update (Function.update v x u) y w)) :
    ∃ B : M, ∀ u : M, MemRelM u (v a) →
      ∃ w : M, MemRelM w B ∧ Formula.Realize φ (Function.update (Function.update v x u) y w) := by
  let σ : SFormulaJ := allJ a ((allJ x (memJ x a ⟹ exJ y φ)) ⟹
    exJ b (allJ x (memJ x a ⟹ exJ y (memJ y b ⊓ φ))))
  have hσ : IsCollectionJ σ := ⟨φ, x, y, a, b, hnodup, hb, rfl⟩
  have hmem : closeJ σ ∈ ZFj := Or.inr ⟨σ, hσ, rfl⟩
  have hreal := realize_of_closeJ (hM.realize_of_mem _ hmem) v
  simp only [σ, realize_allJ, realize_exJ, Formula.realize_imp,
    Formula.realize_inf, realize_memJ] at hreal
  have hnodup' := hnodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup'
  rcases hnodup' with ⟨⟨hxy, hxa, hxb⟩, ⟨hya, hyb⟩, hab, _⟩
  have hpre : ∀ u : M, MemRelM (Function.update (Function.update v a (v a)) x u x)
        (Function.update (Function.update v a (v a)) x u a) →
      ∃ w : M, Formula.Realize φ (Function.update (Function.update (Function.update v a (v a)) x u) y w) := by
    intro u hu
    have hu0 : MemRelM u (v a) := by
      simpa [Function.update_self, Function.update_of_ne (Ne.symm hxa)] using hu
    obtain ⟨w, hw⟩ := htot u hu0
    refine ⟨w, (realize_congr_freeVar ?_).mp hw⟩
    intro n _
    by_cases hny : n = y
    · subst hny; simp
    · by_cases hnx : n = x
      · subst hnx; simp [hxy]
      · by_cases hna : n = a
        · subst hna; simp [hnx, hny]
        · simp [hnx, hny]
  obtain ⟨B, hB⟩ := hreal (v a) hpre
  refine ⟨B, fun u hu => ?_⟩
  have hu' : MemRelM (Function.update (Function.update (Function.update v a (v a)) b B) x u x)
      (Function.update (Function.update (Function.update v a (v a)) b B) x u a) := by
    simpa [Function.update_self, Function.update_of_ne (Ne.symm hxa),
      Function.update_of_ne hab] using hu
  obtain ⟨w, hwB, hwφ⟩ := hB u hu'
  refine ⟨w, ?_, ?_⟩
  · simpa [Function.update_self, Function.update_of_ne (Ne.symm hyb),
      Function.update_of_ne (Ne.symm hxb)] using hwB
  · refine (realize_congr_freeVar ?_).mp hwφ
    intro n hn
    have hnb : n ≠ b := fun h => hb (h ▸ hn)
    by_cases hny : n = y
    · subst hny; simp
    · by_cases hnx : n = x
      · subst hnx; simp [hxy]
      · by_cases hna : n = a
        · subst hna; simp [hny, hnx, hnb]
        · simp [hny, hnx, hnb]

private lemma ax_coll (φ : SFormula) (x y a b : ℕ) (hnodup : [x, y, a, b].Nodup)
    (hb : b ∉ φ.freeVarFinset) (v : ℕ → M)
    (htot : ∀ u : M, MemRelM u (v a) →
      ∃ w : M, Formula.Realize φ (Function.update (Function.update v x u) y w)) :
    ∃ B : M, ∀ u : M, MemRelM u (v a) →
      ∃ w : M, MemRelM w B ∧ Formula.Realize φ (Function.update (Function.update v x u) y w) := by
  have hbJ : b ∉ (incl.onBoundedFormula φ).freeVarFinset := fun h =>
    hb (mem_freeVarFinset_onBoundedFormula incl φ h)
  have htot' : ∀ u : M, MemRelM u (v a) →
      ∃ w : M, Formula.Realize (incl.onBoundedFormula φ) (Function.update (Function.update v x u) y w) := by
    intro u hu
    obtain ⟨w, hw⟩ := htot u hu
    exact ⟨w, (realize_onBoundedFormula_formula φ _).mpr hw⟩
  obtain ⟨B, hB⟩ := ax_collJ hM (incl.onBoundedFormula φ) x y a b hnodup hbJ v htot'
  refine ⟨B, fun u hu => ?_⟩
  obtain ⟨w, hwB, hwφ⟩ := hB u hu
  exact ⟨w, hwB, (realize_onBoundedFormula_formula φ _).mp hwφ⟩

/-! ### Part 4: Basic set constructors, `ω`, and transitive supersets -/

private lemma emp_ex [Nonempty M] : ∃ e : M, IsEmp e := by
  obtain ⟨w, ⟨e, he, _⟩, _⟩ := ax_infinity hM
  exact ⟨e, he⟩

private lemma emp_uniq {e₁ e₂ : M} (h₁ : IsEmp e₁) (h₂ : IsEmp e₂) : e₁ = e₂ :=
  ax_ext hM e₁ e₂ fun z => ⟨fun hz => absurd hz (h₁ z), fun hz => absurd hz (h₂ z)⟩

private lemma sing_ex (a : M) : ∃ s : M, IsSingM s a := by
  obtain ⟨s, hs⟩ := ax_pair hM a a
  exact ⟨s, fun z => by simpa [IsDblM] using hs z⟩

private lemma sing_uniq {s₁ s₂ a : M} (h₁ : IsSingM s₁ a) (h₂ : IsSingM s₂ a) : s₁ = s₂ :=
  ax_ext hM s₁ s₂ fun z => (h₁ z).trans (h₂ z).symm

private lemma binUnion_ex (a b : M) : ∃ u : M, ∀ z : M, MemRelM z u ↔ MemRelM z a ∨ MemRelM z b := by
  obtain ⟨p, hp⟩ := ax_pair hM a b
  obtain ⟨u, hu⟩ := ax_union hM p
  refine ⟨u, fun z => ?_⟩
  rw [hu]
  constructor
  · rintro ⟨y, hyp, hzy⟩
    rcases (hp y).mp hyp with rfl | rfl
    · exact Or.inl hzy
    · exact Or.inr hzy
  · rintro (hza | hzb)
    · exact ⟨a, (hp a).mpr (Or.inl rfl), hza⟩
    · exact ⟨b, (hp b).mpr (Or.inr rfl), hzb⟩

private lemma succ_ex (a : M) : ∃ s : M, IsSucc s a := by
  obtain ⟨t, ht⟩ := sing_ex hM a
  obtain ⟨u, hu⟩ := binUnion_ex hM a t
  exact ⟨u, fun z => by rw [hu, ht]⟩

private lemma succ_uniq {s₁ s₂ a : M} (h₁ : IsSucc s₁ a) (h₂ : IsSucc s₂ a) : s₁ = s₂ :=
  ax_ext hM s₁ s₂ fun z => (h₁ z).trans (h₂ z).symm

private lemma pair_ex (a b : M) : ∃ p : M, IsPairM p a b := by
  obtain ⟨s, hs⟩ := sing_ex hM a
  obtain ⟨d, hd⟩ := ax_pair hM a b
  obtain ⟨p, hp⟩ := ax_pair hM s d
  refine ⟨p, fun w => ?_⟩
  rw [hp]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl hs
    · exact Or.inr hd
  · rintro (hw | hw)
    · exact Or.inl (sing_uniq hM hw hs)
    · exact Or.inr (ax_ext hM w d fun z => (hw z).trans (hd z).symm)

private lemma pair_uniq {p₁ p₂ a b : M} (h₁ : IsPairM p₁ a b) (h₂ : IsPairM p₂ a b) : p₁ = p₂ :=
  ax_ext hM p₁ p₂ fun w => (h₁ w).trans (h₂ w).symm

private lemma pair_inj {p₁ p₂ a₁ b₁ a₂ b₂ : M}
    (h₁ : IsPairM p₁ a₁ b₁) (h₂ : IsPairM p₂ a₂ b₂) (heq : p₁ = p₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  subst heq
  obtain ⟨s₁, hs₁⟩ := sing_ex hM a₁
  obtain ⟨d₁, hd₁⟩ := ax_pair hM a₁ b₁
  obtain ⟨s₂, hs₂⟩ := sing_ex hM a₂
  obtain ⟨d₂, hd₂⟩ := ax_pair hM a₂ b₂
  have hs₁_mem : MemRelM s₁ p₁ := (h₁ s₁).mpr (Or.inl hs₁)
  have hd₁_mem : MemRelM d₁ p₁ := (h₁ d₁).mpr (Or.inr hd₁)
  have hd₂_mem : MemRelM d₂ p₁ := (h₂ d₂).mpr (Or.inr hd₂)
  have ha : a₁ = a₂ := by
    rcases (h₂ s₁).mp hs₁_mem with hs | hd
    · exact (hs a₁).mp ((hs₁ a₁).mpr rfl)
    · exact ((hs₁ a₂).mp ((hd a₂).mpr (Or.inl rfl))).symm
  subst ha
  refine ⟨rfl, ?_⟩
  rcases (h₂ d₁).mp hd₁_mem with hs | hd
  · have hb1 : b₁ = a₁ := (hs b₁).mp ((hd₁ b₁).mpr (Or.inr rfl))
    rcases (h₁ d₂).mp hd₂_mem with hs' | hd'
    · exact hb1.trans ((hs' b₂).mp ((hd₂ b₂).mpr (Or.inr rfl))).symm
    · have hb2 : b₂ = a₁ := by
        rcases (hd' b₂).mp ((hd₂ b₂).mpr (Or.inr rfl)) with rfl | h
        · rfl
        · exact h.trans hb1
      exact hb1.trans hb2.symm
  · rcases (hd b₁).mp ((hd₁ b₁).mpr (Or.inr rfl)) with hb1 | h
    · rcases (h₁ d₂).mp hd₂_mem with hs' | hd'
      · exact hb1.trans ((hs' b₂).mp ((hd₂ b₂).mpr (Or.inr rfl))).symm
      · rcases (hd' b₂).mp ((hd₂ b₂).mpr (Or.inr rfl)) with hb2 | hb2
        · exact hb1.trans hb2.symm
        · exact hb2.symm
    · exact h

private lemma mem_irrefl (x : M) : ¬ MemRelM x x := by
  intro hxx
  obtain ⟨s, hs⟩ := sing_ex hM x
  obtain ⟨y, hys, hmin⟩ := ax_found hM s ⟨x, (hs x).mpr rfl⟩
  have hyx : y = x := (hs y).mp hys
  subst hyx
  exact hmin y ⟨hxx, hys⟩

private lemma mem_asym {x y : M} (hxy : MemRelM x y) : ¬ MemRelM y x := by
  intro hyx
  obtain ⟨d, hd⟩ := ax_pair hM x y
  obtain ⟨w, hwd, hmin⟩ := ax_found hM d ⟨x, (hd x).mpr (Or.inl rfl)⟩
  rcases (hd w).mp hwd with rfl | rfl
  · exact hmin y ⟨hyx, (hd y).mpr (Or.inr rfl)⟩
  · exact hmin x ⟨hxy, (hd x).mpr (Or.inl rfl)⟩

private lemma succ_inj_ord {a b s : M} (hsa : IsSucc s a) (hsb : IsSucc s b) : a = b := by
  have ha_s : MemRelM a s := (hsa a).mpr (Or.inr rfl)
  have hb_s : MemRelM b s := (hsb b).mpr (Or.inr rfl)
  rcases (hsb a).mp ha_s with hab | rfl
  · rcases (hsa b).mp hb_s with hba | rfl
    · exact absurd hba (mem_asym hM hab)
    · rfl
  · rfl

private lemma omega_ex [Nonempty M] :
    ∃ ω : M, IsInd ω ∧ ∀ u : M, IsInd u → Sub ω u := by
  obtain ⟨w₀, hw₀⟩ := ax_infinity hM
  let φ : SFormula := all 1 (isInductive 1 ⟹ mem 0 1)
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := by
    intro h
    obtain ⟨h1, hne1⟩ := mem_freeVarFinset_all h
    rcases mem_freeVarFinset_imp h1 with ha | hb
    · exact hne1 (fv_isInductive ha)
    · rcases mem_freeVarFinset_mem hb with h0 | h1' <;> omega
  obtain ⟨ω, hω⟩ := ax_sep hM φ 0 3 2 (by omega) (by omega) (by omega) hhb (fun _ => w₀)
  have hω_mem : ∀ z : M, MemRelM z ω ↔ MemRelM z w₀ ∧ ∀ u : M, IsInd u → MemRelM z u := by
    intro z
    rw [hω z]
    refine and_congr_right fun _ => ?_
    simp [φ, realize_all, Formula.realize_imp, realize_mem,
      r_isInductive _ (by omega : (1 : ℕ) < 1000)]
  refine ⟨ω, ⟨?_, ?_⟩, fun u hu z hz => ((hω_mem z).mp hz).2 u hu⟩
  · obtain ⟨e, he, hew⟩ := hw₀.1
    refine ⟨e, he, (hω_mem e).mpr ⟨hew, fun u hu => ?_⟩⟩
    obtain ⟨e', he', he'u⟩ := hu.1
    rwa [emp_uniq hM he he']
  · intro a ha
    have haw : MemRelM a w₀ := ((hω_mem a).mp ha).1
    obtain ⟨s, hsa, hsw⟩ := hw₀.2 a haw
    refine ⟨s, hsa, (hω_mem s).mpr ⟨hsw, fun u hu => ?_⟩⟩
    have hau : MemRelM a u := ((hω_mem a).mp ha).2 u hu
    obtain ⟨s', hs'a, hs'u⟩ := hu.2 a hau
    rwa [succ_uniq hM hsa hs'a]

private lemma chain_ex_and_uniq (ω : M) (hω_ind : IsInd ω) (hω_min : ∀ u : M, IsInd u → Sub ω u)
    (x : M) :
    (∀ n : M, MemRelM n ω → Ord n) ∧
    (∀ n : M, MemRelM n ω → ∃ f : M, IsChain f n x) ∧
    (∀ n₁ n₂ f₁ f₂ k v₁ v₂ : M, MemRelM n₁ ω → MemRelM n₂ ω →
      IsChain f₁ n₁ x → IsChain f₂ n₂ x → MemRelM k ω →
      PairIn f₁ k v₁ → PairIn f₂ k v₂ → v₁ = v₂) := by
  have hω_ord : ∀ n : M, MemRelM n ω → Ord n := by
    have hhb : (2 : ℕ) ∉ (isOrdF 0).freeVarFinset := fun h => by
      have := fv_isOrdF h; omega
    obtain ⟨U, hU⟩ := ax_sep hM (isOrdF 0) 0 1 2 (by omega) (by omega) (by omega) hhb (fun _ => ω)
    have hU_mem : ∀ z : M, MemRelM z U ↔ MemRelM z ω ∧ Ord z := fun z => by
      simpa [r_isOrdF (α := 0) _ ⟨by omega, by omega, by omega⟩] using hU z
    have hU_ind : IsInd U := by
      refine ⟨?_, ?_⟩
      · obtain ⟨e, he, heω⟩ := hω_ind.1
        exact ⟨e, he, (hU_mem e).mpr ⟨heω, ord_emp he⟩⟩
      · intro a ha
        obtain ⟨haω, haOrd⟩ := (hU_mem a).mp ha
        obtain ⟨s, hsa, hsω⟩ := hω_ind.2 a haω
        exact ⟨s, hsa, (hU_mem s).mpr ⟨hsω, ord_succ haOrd hsa⟩⟩
    exact fun n hn => ((hU_mem n).mp (hω_min U hU_ind n hn)).2
  have hchain_ex : ∀ n : M, MemRelM n ω → ∃ f : M, IsChain f n x := by
    let φ : SFormula := ex 3 (isChainF 3 0 4)
    have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
      obtain ⟨h1, hne3⟩ := mem_freeVarFinset_ex h
      rcases fv_isChainF h1 with h3 | h0 | h4 <;> omega
    let env : ℕ → M := Function.update (fun _ => ω) 4 x
    obtain ⟨U, hU⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
    have hU_mem : ∀ n : M, MemRelM n U ↔ MemRelM n ω ∧ ∃ f : M, IsChain f n x := fun n => by
      rw [hU n]
      have h1 : env 1 = ω := by simp [env]
      rw [h1]
      refine and_congr_right fun _ => ?_
      simp [φ, realize_ex, r_isChainF _ (by omega : (3 : ℕ) < 1000) (by omega : (0 : ℕ) < 1000)
        (by omega : (4 : ℕ) < 1000), env]
    have hU_ind : IsInd U := by
      refine ⟨?_, ?_⟩
      · obtain ⟨e, he, heω⟩ := hω_ind.1
        refine ⟨e, he, (hU_mem e).mpr ⟨heω, ?_⟩⟩
        obtain ⟨se, hse⟩ := succ_ex hM e
        obtain ⟨sx, hsx⟩ := sing_ex hM x
        obtain ⟨p, hp⟩ := pair_ex hM e sx
        obtain ⟨f, hf⟩ := sing_ex hM p
        refine ⟨f, se, hse, ?_, ?_, ?_, ?_, ?_⟩
        · intro q hqf
          have hqp : q = p := (hf q).mp hqf
          subst hqp
          exact ⟨e, (hse e).mpr (Or.inr rfl), sx, hp⟩
        · intro k hk
          rcases (hse k).mp hk with hke | rfl
          · exact absurd hke (he k)
          · exact ⟨sx, p, hp, (hf p).mpr rfl⟩
        · intro k v₁ v₂ ⟨p₁, hp₁, h1f⟩ ⟨p₂, hp₂, h2f⟩
          have heq : p₁ = p₂ := ((hf p₁).mp h1f).trans ((hf p₂).mp h2f).symm
          exact (pair_inj hM hp₁ hp₂ heq).2
        · intro e' he' v ⟨q, hq, hqf⟩
          have hqp : q = p := (hf q).mp hqf
          have hv : v = sx := (pair_inj hM hq hp hqp).2
          subst hv
          exact hsx
        · intro k _ _ _ hke
          exact absurd hke (he k)
      · intro n hnU
        obtain ⟨hnω, f, s, hsn, hf_pairs, hf_dom, hf_fun, hf_zero, hf_step⟩ := (hU_mem n).mp hnU
        obtain ⟨n', hn'n, hn'ω⟩ := hω_ind.2 n hnω
        have hsn' : s = n' := succ_uniq hM hsn hn'n
        subst s
        obtain ⟨s', hs'n'⟩ := succ_ex hM n'
        obtain ⟨vn, hvn⟩ := hf_dom n ((hn'n n).mpr (Or.inr rfl))
        obtain ⟨vn', hvn'⟩ := ax_union hM vn
        obtain ⟨p_new, hp_new⟩ := pair_ex hM n' vn'
        obtain ⟨sp_new, hsp_new⟩ := sing_ex hM p_new
        obtain ⟨f', hf'⟩ := binUnion_ex hM f sp_new
        have hf'_mem : ∀ q : M, MemRelM q f' ↔ MemRelM q f ∨ q = p_new := fun q => by
          rw [hf', hsp_new]
        have hf'_pairIn : ∀ k v : M, PairIn f' k v ↔ PairIn f k v ∨ (k = n' ∧ v = vn') := by
          intro k v
          constructor
          · rintro ⟨q, hq, hqf'⟩
            rcases (hf'_mem q).mp hqf' with hqf | rfl
            · exact Or.inl ⟨q, hq, hqf⟩
            · exact Or.inr (pair_inj hM hq hp_new rfl)
          · rintro (⟨q, hq, hqf⟩ | ⟨rfl, rfl⟩)
            · exact ⟨q, hq, (hf'_mem q).mpr (Or.inl hqf)⟩
            · exact ⟨p_new, hp_new, (hf'_mem p_new).mpr (Or.inr rfl)⟩
        have hn'_not_in_n' : ¬ MemRelM n' n' := mem_irrefl hM n'
        have hn'_no_f : ∀ v : M, ¬ PairIn f n' v := by
          rintro v ⟨q, hq, hqf⟩
          obtain ⟨k, hkn', w, hkw⟩ := hf_pairs q hqf
          have hkn'eq : n' = k := (pair_inj hM hq hkw rfl).1
          subst hkn'eq
          exact hn'_not_in_n' hkn'
        refine ⟨n', hn'n, (hU_mem n').mpr ⟨hn'ω, f', s', hs'n', ?_, ?_, ?_, ?_, ?_⟩⟩
        · intro q hqf'
          rcases (hf'_mem q).mp hqf' with hqf | rfl
          · obtain ⟨k, hkn', v, hkv⟩ := hf_pairs q hqf
            exact ⟨k, (hs'n' k).mpr (Or.inl hkn'), v, hkv⟩
          · exact ⟨n', (hs'n' n').mpr (Or.inr rfl), vn', hp_new⟩
        · intro k hks'
          rcases (hs'n' k).mp hks' with hkn' | hkeq
          · obtain ⟨v, hv⟩ := hf_dom k hkn'
            exact ⟨v, (hf'_pairIn k v).mpr (Or.inl hv)⟩
          · subst k
            exact ⟨vn', (hf'_pairIn n' vn').mpr (Or.inr ⟨rfl, rfl⟩)⟩
        · intro k v₁ v₂ h1 h2
          rcases (hf'_pairIn k v₁).mp h1 with h1f | ⟨hkeq, rfl⟩
          · rcases (hf'_pairIn k v₂).mp h2 with h2f | ⟨hkeq, rfl⟩
            · exact hf_fun k v₁ v₂ h1f h2f
            · subst k; exact absurd h1f (hn'_no_f v₁)
          · subst k
            rcases (hf'_pairIn n' v₂).mp h2 with h2f | ⟨_, rfl⟩
            · exact absurd h2f (hn'_no_f v₂)
            · rfl
        · intro e he v hfv
          rcases (hf'_pairIn e v).mp hfv with hvf | ⟨rfl, rfl⟩
          · exact hf_zero e he v hvf
          · exact absurd ((hn'n n).mpr (Or.inr rfl)) (he n)
        · intro k k' v v' hkn' hk'k hkv hk'v'
          rcases (hn'n k).mp hkn' with hkn | hkeq
          · have hk'_ne_n' : k' ≠ n' := by
              intro hEq
              subst hEq
              have hk_eq_n : k = n := succ_inj_ord hM hk'k hn'n
              subst hk_eq_n
              exact mem_irrefl hM k hkn
            have hk_ne_n' : k ≠ n' := fun h => mem_irrefl hM n' (h ▸ (hn'n k).mpr (Or.inl hkn))
            have hkv_f : PairIn f k v := by
              rcases (hf'_pairIn k v).mp hkv with h | ⟨h, _⟩
              · exact h
              · exact absurd h hk_ne_n'
            have hk'v'_f : PairIn f k' v' := by
              rcases (hf'_pairIn k' v').mp hk'v' with h | ⟨h, _⟩
              · exact h
              · exact absurd h hk'_ne_n'
            exact hf_step k k' v v' hkn hk'k hkv_f hk'v'_f
          · subst k
            have hk'_eq : k' = n' := succ_uniq hM hk'k hn'n
            subst k'
            have hn_ne_n' : n ≠ n' := fun h => mem_irrefl hM n (h ▸ (hn'n n).mpr (Or.inr rfl))
            have hkv_f : PairIn f n v := by
              rcases (hf'_pairIn n v).mp hkv with h | ⟨h, _⟩
              · exact h
              · exact absurd h hn_ne_n'
            have hv_eq : v = vn := hf_fun n v vn hkv_f hvn
            subst hv_eq
            rcases (hf'_pairIn n' v').mp hk'v' with h | ⟨_, rfl⟩
            · exact absurd h (hn'_no_f v')
            · exact hvn'
    exact fun n hn => ((hU_mem n).mp (hω_min U hU_ind n hn)).2
  have hchain_uniq : ∀ n₁ n₂ f₁ f₂ k v₁ v₂ : M, MemRelM n₁ ω → MemRelM n₂ ω →
      IsChain f₁ n₁ x → IsChain f₂ n₂ x → MemRelM k ω →
      PairIn f₁ k v₁ → PairIn f₂ k v₂ → v₁ = v₂ := by
    intro n₁ n₂ f₁ f₂ k v₁ v₂ hn₁ hn₂ hf₁ hf₂ hk hv₁ hv₂
    let φ : SFormula := all 5 (all 6 ((pairIn 7 0 5 ⊓ pairIn 8 0 6) ⟹ eq 5 6))
    have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
      obtain ⟨h, hne5⟩ := mem_freeVarFinset_all h
      obtain ⟨h, hne6⟩ := mem_freeVarFinset_all h
      rcases mem_freeVarFinset_imp h with ha | hb
      · rcases mem_freeVarFinset_inf ha with hc | hd
        · rcases fv_pairIn hc with h7 | h0 | h5 <;> omega
        · rcases fv_pairIn hd with h8 | h0 | h6 <;> omega
      · rcases mem_freeVarFinset_eq hb with h5 | h6 <;> omega
    let env : ℕ → M := Function.update (Function.update (fun _ => ω) 7 f₁) 8 f₂
    obtain ⟨U, hU⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
    have hU_mem : ∀ m : M, MemRelM m U ↔ MemRelM m ω ∧ ∀ w₁ w₂ : M, PairIn f₁ m w₁ → PairIn f₂ m w₂ → w₁ = w₂ := by
      intro m
      rw [hU m]
      have h1 : env 1 = ω := by simp [env]
      rw [h1]
      refine and_congr_right fun _ => ?_
      simp [φ, realize_all, Formula.realize_imp, Formula.realize_inf, realize_eq,
        r_pairIn (f := 7) (a := 0) (b := 5) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩,
        r_pairIn (f := 8) (a := 0) (b := 6) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩, env]
    obtain ⟨s₁, hs₁, hf₁_p, hf₁_d, _, hf₁_z, hf₁_s⟩ := hf₁
    obtain ⟨s₂, hs₂, hf₂_p, hf₂_d, _, hf₂_z, hf₂_s⟩ := hf₂
    have hU_ind : IsInd U := by
      refine ⟨?_, ?_⟩
      · obtain ⟨e, he, heω⟩ := hω_ind.1
        refine ⟨e, he, (hU_mem e).mpr ⟨heω, fun w₁ w₂ h1 h2 => ?_⟩⟩
        exact sing_uniq hM (hf₁_z e he w₁ h1) (hf₂_z e he w₂ h2)
      · intro m hmU
        obtain ⟨hmω, hmEq⟩ := (hU_mem m).mp hmU
        obtain ⟨m', hm'm, hm'ω⟩ := hω_ind.2 m hmω
        refine ⟨m', hm'm, (hU_mem m').mpr ⟨hm'ω, fun w₁' w₂' h1' h2' => ?_⟩⟩
        have hm'_s1 : MemRelM m' s₁ := by
          obtain ⟨q, hq, hqf⟩ := h1'
          obtain ⟨k', hk', _, hkw⟩ := hf₁_p q hqf
          rwa [(pair_inj hM hq hkw rfl).1]
        have hm'_s2 : MemRelM m' s₂ := by
          obtain ⟨q, hq, hqf⟩ := h2'
          obtain ⟨k', hk', _, hkw⟩ := hf₂_p q hqf
          rwa [(pair_inj hM hq hkw rfl).1]
        have hm_n1 : MemRelM m n₁ := by
          rcases (hs₁ m').mp hm'_s1 with hm'n1 | rfl
          · exact (hω_ord n₁ hn₁).1 m' hm'n1 m ((hm'm m).mpr (Or.inr rfl))
          · exact (hm'm m).mpr (Or.inr rfl)
        have hm_n2 : MemRelM m n₂ := by
          rcases (hs₂ m').mp hm'_s2 with hm'n2 | rfl
          · exact (hω_ord n₂ hn₂).1 m' hm'n2 m ((hm'm m).mpr (Or.inr rfl))
          · exact (hm'm m).mpr (Or.inr rfl)
        obtain ⟨w₁, hw₁⟩ := hf₁_d m ((hs₁ m).mpr (Or.inl hm_n1))
        obtain ⟨w₂, hw₂⟩ := hf₂_d m ((hs₂ m).mpr (Or.inl hm_n2))
        have hwEq : w₁ = w₂ := hmEq w₁ w₂ hw₁ hw₂
        subst hwEq
        have hu1 := hf₁_s m m' w₁ w₁' hm_n1 hm'm hw₁ h1'
        have hu2 := hf₂_s m m' w₁ w₂' hm_n2 hm'm hw₂ h2'
        exact ax_ext hM w₁' w₂' fun z => (hu1 z).trans (hu2 z).symm
    exact ((hU_mem k).mp (hω_min U hU_ind k hk)).2 v₁ v₂ hv₁ hv₂
  exact ⟨hω_ord, hchain_ex, hchain_uniq⟩

private lemma exists_transitive_superset [Nonempty M] (x : M) : ∃ T : M, MemRelM x T ∧ Trans T := by
  obtain ⟨ω, hω_ind, hω_min⟩ := omega_ex hM
  obtain ⟨_, hchain_ex, hchain_uniq⟩ := chain_ex_and_uniq hM ω hω_ind hω_min x
  let φ : SFormula := ex 5 (isChainF 5 0 6 ⊓ pairIn 5 0 1)
  have hhb : (3 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne5⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with ha | hb
    · rcases fv_isChainF ha with h5 | h0 | h6 <;> omega
    · rcases fv_pairIn hb with h5 | h0 | h1 <;> omega
  let env : ℕ → M := Function.update (fun _ => ω) 6 x
  have htot : ∀ n : M, MemRelM n (env 2) →
      ∃ y : M, Formula.Realize φ (Function.update (Function.update env 0 n) 1 y) := by
    intro n hn
    have hnω : MemRelM n ω := by simpa [env] using hn
    obtain ⟨f, hf⟩ := hchain_ex n hnω
    have ⟨s, hs, _, hf_dom, _, _, _⟩ := hf
    obtain ⟨y, hy⟩ := hf_dom n ((hs n).mpr (Or.inr rfl))
    refine ⟨y, ?_⟩
    simp only [φ, realize_ex, Formula.realize_inf,
      r_isChainF (f := 5) (n := 0) (x := 6) _ (by omega) (by omega) (by omega),
      r_pairIn (f := 5) (a := 0) (b := 1) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩]
    exact ⟨f, by simpa [env] using hf, by simpa [env] using hy⟩
  obtain ⟨B, hB⟩ := ax_coll hM φ 0 1 2 3 (by decide) hhb env htot
  let ψ : SFormula := ex 0 (mem 0 7 ⊓ ex 5 (isChainF 5 0 6 ⊓ pairIn 5 0 1))
  have hhb' : (4 : ℕ) ∉ ψ.freeVarFinset := fun h => by
    obtain ⟨h, hne0⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with ha | hb
    · rcases mem_freeVarFinset_mem ha with h0 | h7 <;> omega
    · obtain ⟨hb, hne5⟩ := mem_freeVarFinset_ex hb
      rcases mem_freeVarFinset_inf hb with hc | hd
      · rcases fv_isChainF hc with h5 | h0 | h6 <;> omega
      · rcases fv_pairIn hd with h5 | h0 | h1 <;> omega
  let env' : ℕ → M := Function.update (Function.update (fun _ => B) 7 ω) 6 x
  obtain ⟨C, hC⟩ := ax_sep hM ψ 1 2 4 (by omega) (by omega) (by omega) hhb' env'
  have hC_mem : ∀ y : M, MemRelM y C ↔ MemRelM y B ∧ ∃ n : M, MemRelM n ω ∧ ∃ f : M, IsChain f n x ∧ PairIn f n y := by
    intro y
    rw [hC y]
    have h2 : env' 2 = B := by simp [env']
    rw [h2]
    refine and_congr_right fun _ => ?_
    simp [ψ, realize_ex, Formula.realize_inf, realize_mem,
      r_isChainF (f := 5) (n := 0) (x := 6) _ (by omega) (by omega) (by omega),
      r_pairIn (f := 5) (a := 0) (b := 1) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩, env']
  obtain ⟨T, hT⟩ := ax_union hM C
  refine ⟨T, ?_, ?_⟩
  · obtain ⟨e, he, heω⟩ := hω_ind.1
    obtain ⟨y, hyB, hyφ⟩ := hB e (by simpa [env] using heω)
    simp only [φ, realize_ex, Formula.realize_inf,
      r_isChainF (f := 5) (n := 0) (x := 6) _ (by omega) (by omega) (by omega),
      r_pairIn (f := 5) (a := 0) (b := 1) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩, env, Function.update_self,
      Function.update_of_ne (by omega : (0 : ℕ) ≠ 5),
      Function.update_of_ne (by omega : (0 : ℕ) ≠ 1),
      Function.update_of_ne (by omega : (1 : ℕ) ≠ 5),
      Function.update_of_ne (by omega : (6 : ℕ) ≠ 5),
      Function.update_of_ne (by omega : (6 : ℕ) ≠ 1),
      Function.update_of_ne (by omega : (6 : ℕ) ≠ 0)] at hyφ
    obtain ⟨f, hf, hfy⟩ := hyφ
    have hyC : MemRelM y C := (hC_mem y).mpr ⟨hyB, e, heω, f, hf, hfy⟩
    obtain ⟨_, _, _, _, _, hf_z, _⟩ := hf
    have hxy : MemRelM x y := (hf_z e he y hfy x).mpr rfl
    exact (hT x).mpr ⟨y, hyC, hxy⟩
  · intro a haT b hba
    obtain ⟨y, hyC, hay⟩ := (hT a).mp haT
    obtain ⟨_, n, hnω, f, hf, hfy⟩ := (hC_mem y).mp hyC
    obtain ⟨n', hn'n, hn'ω⟩ := hω_ind.2 n hnω
    obtain ⟨y', hy'B, hy'φ⟩ := hB n' (by simpa [env] using hn'ω)
    simp only [φ, realize_ex, Formula.realize_inf,
      r_isChainF (f := 5) (n := 0) (x := 6) _ (by omega) (by omega) (by omega),
      r_pairIn (f := 5) (a := 0) (b := 1) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩, env, Function.update_self,
      Function.update_of_ne (by omega : (0 : ℕ) ≠ 5),
      Function.update_of_ne (by omega : (0 : ℕ) ≠ 1),
      Function.update_of_ne (by omega : (1 : ℕ) ≠ 5),
      Function.update_of_ne (by omega : (6 : ℕ) ≠ 5),
      Function.update_of_ne (by omega : (6 : ℕ) ≠ 1),
      Function.update_of_ne (by omega : (6 : ℕ) ≠ 0)] at hy'φ
    obtain ⟨f', hf', hf'y'⟩ := hy'φ
    have hy'C : MemRelM y' C := (hC_mem y').mpr ⟨hy'B, n', hn'ω, f', hf', hf'y'⟩
    have ⟨s', hs', _, hf'_d, _, _, hf'_s⟩ := hf'
    have hn_s' : MemRelM n s' := (hs' n).mpr (Or.inl ((hn'n n).mpr (Or.inr rfl)))
    obtain ⟨yn, hyn⟩ := hf'_d n hn_s'
    have hyEq : yn = y := hchain_uniq n' n f' f n yn y hn'ω hnω hf' hf hnω hyn hfy
    subst hyEq
    have hunion : IsUnionM y' yn :=
      hf'_s n n' yn y' ((hn'n n).mpr (Or.inr rfl)) hn'n hyn hf'y'
    have hby' : MemRelM b y' := (hunion b).mpr ⟨a, hay, hba⟩
    exact (hT b).mpr ⟨y', hy'C, hby'⟩

private lemma exists_transitive_superset_fin [Nonempty M] :
    ∀ {m : ℕ} (f : Fin m → M), ∃ T : M, Trans T ∧ ∀ i : Fin m, MemRelM (f i) T
  | 0, _ => by
    obtain ⟨e, he⟩ := emp_ex hM
    exact ⟨e, fun x hx => absurd hx (he x), fun i => Fin.elim0 i⟩
  | _ + 1, f => by
    obtain ⟨T₁, hT₁mem, hT₁tr⟩ := exists_transitive_superset hM (f 0)
    obtain ⟨T₂, hT₂tr, hT₂mem⟩ := exists_transitive_superset_fin (f ∘ Fin.succ)
    obtain ⟨T, hT⟩ := binUnion_ex hM T₁ T₂
    refine ⟨T, fun x hx z hzx => ?_, fun i => ?_⟩
    · rcases (hT x).mp hx with hx1 | hx2
      · exact (hT z).mpr (Or.inl (hT₁tr x hx1 z hzx))
      · exact (hT z).mpr (Or.inr (hT₂tr x hx2 z hzx))
    · refine Fin.cases ?_ ?_ i
      · exact (hT (f 0)).mpr (Or.inl hT₁mem)
      · intro j; exact (hT (f j.succ)).mpr (Or.inr (hT₂mem j))

/-! ### Part 5: Existence, uniqueness, and `k`-commutation of the 12 Gödel operations -/

private lemma diff_ex (x y : M) : ∃ d : M, IsDiffM d x y := by
  let φ : SFormula := ∼(mem 0 3)
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    rcases mem_freeVarFinset_mem (mem_freeVarFinset_not h) with h0 | h3 <;> omega
  let env : ℕ → M := Function.update (fun _ => x) 3 y
  obtain ⟨d, hd⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨d, fun z => ?_⟩
  simpa [φ, realize_mem, env] using hd z

private lemma prod_ex (x y : M) : ∃ r : M, IsProdM r x y := by
  obtain ⟨u, hu⟩ := binUnion_ex hM x y
  obtain ⟨p1, hp1⟩ := ax_powerset hM u
  obtain ⟨p2, hp2⟩ := ax_powerset hM p1
  let φ : SFormula := ex 3 (ex 4 (mem 3 5 ⊓ mem 4 6 ⊓ isPair 0 3 4))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, hne4⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h12 | h3
    · rcases mem_freeVarFinset_inf h12 with h1 | h2
      · rcases mem_freeVarFinset_mem h1 with h3' | h5 <;> omega
      · rcases mem_freeVarFinset_mem h2 with h4' | h6 <;> omega
    · rcases fv_isPair h3 with h0 | h3' | h4' <;> omega
  let env : ℕ → M := Function.update (Function.update (fun _ => p2) 5 x) 6 y
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = p2 := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 0) (a := 3) (b := 4) _ (by omega) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega⟩, env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 0),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, a, b, ⟨hax, hby⟩, hp⟩
    exact ⟨a, b, hax, hby, hp⟩
  · rintro ⟨a, b, hax, hby, hp⟩
    refine ⟨(hp2 p).mpr fun w hwp => (hp1 w).mpr fun z hzw => ?_, a, b, ⟨hax, hby⟩, hp⟩
    rcases (hp w).mp hwp with hws | hwd
    · have hza : z = a := (hws z).mp hzw
      subst hza; exact (hu z).mpr (Or.inl hax)
    · rcases (hwd z).mp hzw with rfl | rfl
      · exact (hu z).mpr (Or.inl hax)
      · exact (hu z).mpr (Or.inr hby)

private lemma dom_ex (x : M) : ∃ d : M, IsDomM d x := by
  obtain ⟨u1, hu1⟩ := ax_union hM x
  obtain ⟨u2, hu2⟩ := ax_union hM u1
  let φ : SFormula := ex 3 (pairIn 4 0 3)
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex h
    rcases fv_pairIn h with h4 | h0 | h3 <;> omega
  let env : ℕ → M := Function.update (fun _ => u2) 4 x
  obtain ⟨d, hd⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨d, fun a => ?_⟩
  have hda := hd a
  have h1 : env 1 = u2 := by simp [env]
  rw [h1] at hda
  rw [hda]
  simp only [φ, realize_ex,
    r_pairIn (f := 4) (a := 0) (b := 3) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
      ⟨by omega, by omega, by omega⟩, env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, b, p, hp, hpx⟩
    exact ⟨b, p, hp, hpx⟩
  · rintro ⟨b, p, hp, hpx⟩
    refine ⟨?_, b, p, hp, hpx⟩
    obtain ⟨s, hs⟩ := sing_ex hM a
    have hsp : MemRelM s p := (hp s).mpr (Or.inl hs)
    have hsu1 : MemRelM s u1 := (hu1 s).mpr ⟨p, hpx, hsp⟩
    exact (hu2 a).mpr ⟨s, hsu1, (hs a).mpr rfl⟩

private lemma memGraph_ex (x : M) : ∃ r : M, IsMemGraphM r x := by
  obtain ⟨xx, hxx⟩ := prod_ex hM x x
  let φ : SFormula := ex 3 (ex 4 (mem 3 5 ⊓ mem 4 5 ⊓ mem 3 4 ⊓ isPair 0 3 4))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, hne4⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h123 | h4
    · rcases mem_freeVarFinset_inf h123 with h12 | h3
      · rcases mem_freeVarFinset_inf h12 with h1 | h2
        · rcases mem_freeVarFinset_mem h1 with h3' | h5 <;> omega
        · rcases mem_freeVarFinset_mem h2 with h4' | h5 <;> omega
      · rcases mem_freeVarFinset_mem h3 with h3' | h4' <;> omega
    · rcases fv_isPair h4 with h0 | h3' | h4' <;> omega
  let env : ℕ → M := Function.update (fun _ => xx) 5 x
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = xx := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 0) (a := 3) (b := 4) _ (by omega) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega⟩, env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, a, b, ⟨⟨hax, hbx⟩, hab⟩, hp⟩
    exact ⟨a, b, hax, hbx, hab, hp⟩
  · rintro ⟨a, b, hax, hbx, hab, hp⟩
    exact ⟨(hxx p).mpr ⟨a, b, hax, hbx, hp⟩, a, b, ⟨⟨hax, hbx⟩, hab⟩, hp⟩

private lemma eqGraph_ex (x : M) : ∃ r : M, IsEqGraphM r x := by
  obtain ⟨xx, hxx⟩ := prod_ex hM x x
  let φ : SFormula := ex 3 (mem 3 5 ⊓ isPair 0 3 3)
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · rcases mem_freeVarFinset_mem h1 with h3 | h5 <;> omega
    · rcases fv_isPair h2 with h0 | h3 | h3' <;> omega
  let env : ℕ → M := Function.update (fun _ => xx) 5 x
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = xx := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 0) (a := 3) (b := 3) _ (by omega) ⟨by omega, by omega, by omega⟩
      ⟨by omega, by omega⟩, env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, a, hax, hp⟩
    exact ⟨a, hax, hp⟩
  · rintro ⟨a, hax, hp⟩
    exact ⟨(hxx p).mpr ⟨a, a, hax, hax, hp⟩, a, hax, hp⟩

private lemma mem_trans_of_pair {U p a b : M} (hU : Trans U) (hpU : MemRelM p U) (hp : IsPairM p a b) :
    MemRelM a U ∧ MemRelM b U := by
  obtain ⟨d, hd⟩ := ax_pair hM a b
  have hdp : MemRelM d p := (hp d).mpr (Or.inr hd)
  have hdU : MemRelM d U := hU p hpU d hdp
  exact ⟨hU d hdU a ((hd a).mpr (Or.inl rfl)), hU d hdU b ((hd b).mpr (Or.inr rfl))⟩

private lemma swap_ex [Nonempty M] (x : M) : ∃ r : M, IsSwapM r x := by
  obtain ⟨U, hxU, hU⟩ := exists_transitive_superset hM x
  obtain ⟨UU, hUU⟩ := prod_ex hM U U
  let φ : SFormula := ex 3 (ex 4 (ex 5 (isPair 0 4 3 ⊓ isPair 5 3 4 ⊓ mem 5 6)))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, hne4⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, hne5⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h12 | h3
    · rcases mem_freeVarFinset_inf h12 with h1 | h2
      · rcases fv_isPair h1 with h0 | h4 | h3' <;> omega
      · rcases fv_isPair h2 with h5 | h3' | h4 <;> omega
    · rcases mem_freeVarFinset_mem h3 with h5 | h6 <;> omega
  let env : ℕ → M := Function.update (fun _ => UU) 6 x
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = UU := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 0) (a := 4) (b := 3) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 5) (a := 3) (b := 4) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, a, b, q, ⟨hp, hq⟩, hqx⟩
    exact ⟨a, b, q, hp, hq, hqx⟩
  · rintro ⟨a, b, q, hp, hq, hqx⟩
    have ⟨haU, hbU⟩ := mem_trans_of_pair hM hU (hU x hxU q hqx) hq
    exact ⟨(hUU p).mpr ⟨b, a, hbU, haU, hp⟩, a, b, q, ⟨hp, hq⟩, hqx⟩

private lemma pull_ex [Nonempty M] (x : M) : ∃ r : M, IsPullM r x := by
  obtain ⟨U, hxU, hU⟩ := exists_transitive_superset hM x
  obtain ⟨UU, hUU⟩ := prod_ex hM U U
  obtain ⟨UUU, hUUU⟩ := prod_ex hM UU U
  let φ : SFormula := ex 3 (ex 4 (ex 5 (ex 6 (ex 7 (ex 8
    (isPair 6 3 4 ⊓ isPair 0 6 5 ⊓ isPair 7 4 5 ⊓ isPair 8 3 7 ⊓ mem 8 9))))))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1234 | h5
    · rcases mem_freeVarFinset_inf h1234 with h123 | h4
      · rcases mem_freeVarFinset_inf h123 with h12 | h3
        · rcases mem_freeVarFinset_inf h12 with h1 | h2
          · rcases fv_isPair h1 with h' | h' | h' <;> omega
          · rcases fv_isPair h2 with h' | h' | h' <;> omega
        · rcases fv_isPair h3 with h' | h' | h' <;> omega
      · rcases fv_isPair h4 with h' | h' | h' <;> omega
    · rcases mem_freeVarFinset_mem h5 with h' | h' <;> omega
  let env : ℕ → M := Function.update (fun _ => UUU) 9 x
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = UUU := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 6) (a := 3) (b := 4) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 0) (a := 6) (b := 5) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 7) (a := 4) (b := 5) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 8) (a := 3) (b := 7) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (7 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, a, b, c, ab, bc, q, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
    exact ⟨a, b, c, ab, bc, q, h1, h2, h3, h4, h5⟩
  · rintro ⟨a, b, c, ab, bc, q, hab, hp, hbc, hq, hqx⟩
    have ⟨haU, hbcU⟩ := mem_trans_of_pair hM hU (hU x hxU q hqx) hq
    have ⟨hbU, hcU⟩ := mem_trans_of_pair hM hU hbcU hbc
    have habUU : MemRelM ab UU := (hUU ab).mpr ⟨a, b, haU, hbU, hab⟩
    exact ⟨(hUUU p).mpr ⟨ab, c, habUU, hcU, hp⟩, a, b, c, ab, bc, q, ⟨⟨⟨⟨hab, hp⟩, hbc⟩, hq⟩, hqx⟩⟩

private lemma push_ex [Nonempty M] (x : M) : ∃ r : M, IsPushM r x := by
  obtain ⟨U, hxU, hU⟩ := exists_transitive_superset hM x
  obtain ⟨UU, hUU⟩ := prod_ex hM U U
  obtain ⟨UUU, hUUU⟩ := prod_ex hM U UU
  let φ : SFormula := ex 3 (ex 4 (ex 5 (ex 6 (ex 7 (ex 8
    (isPair 7 4 5 ⊓ isPair 0 3 7 ⊓ isPair 6 3 4 ⊓ isPair 8 6 5 ⊓ mem 8 9))))))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1234 | h5
    · rcases mem_freeVarFinset_inf h1234 with h123 | h4
      · rcases mem_freeVarFinset_inf h123 with h12 | h3
        · rcases mem_freeVarFinset_inf h12 with h1 | h2
          · rcases fv_isPair h1 with h' | h' | h' <;> omega
          · rcases fv_isPair h2 with h' | h' | h' <;> omega
        · rcases fv_isPair h3 with h' | h' | h' <;> omega
      · rcases fv_isPair h4 with h' | h' | h' <;> omega
    · rcases mem_freeVarFinset_mem h5 with h' | h' <;> omega
  let env : ℕ → M := Function.update (fun _ => UUU) 9 x
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = UUU := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 7) (a := 4) (b := 5) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 0) (a := 3) (b := 7) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 6) (a := 3) (b := 4) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 8) (a := 6) (b := 5) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (7 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, a, b, c, ab, bc, q, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
    exact ⟨a, b, c, ab, bc, q, h1, h2, h3, h4, h5⟩
  · rintro ⟨a, b, c, ab, bc, q, hbc, hp, hab, hq, hqx⟩
    have ⟨habU, hcU⟩ := mem_trans_of_pair hM hU (hU x hxU q hqx) hq
    have ⟨haU, hbU⟩ := mem_trans_of_pair hM hU habU hab
    have hbcUU : MemRelM bc UU := (hUU bc).mpr ⟨b, c, hbU, hcU, hbc⟩
    exact ⟨(hUUU p).mpr ⟨a, bc, haU, hbcUU, hp⟩, a, b, c, ab, bc, q, ⟨⟨⟨⟨hbc, hp⟩, hab⟩, hq⟩, hqx⟩⟩

private lemma shift_ex [Nonempty M] (x : M) : ∃ r : M, IsShiftM r x := by
  obtain ⟨U, hxU, hU⟩ := exists_transitive_superset hM x
  obtain ⟨UU, hUU⟩ := prod_ex hM U U
  obtain ⟨UUU, hUUU⟩ := prod_ex hM U UU
  let φ : SFormula := ex 3 (ex 4 (ex 5 (ex 6 (ex 7 (ex 8
    (isPair 6 3 5 ⊓ isPair 0 4 6 ⊓ isPair 7 4 5 ⊓ isPair 8 3 7 ⊓ mem 8 9))))))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1234 | h5
    · rcases mem_freeVarFinset_inf h1234 with h123 | h4
      · rcases mem_freeVarFinset_inf h123 with h12 | h3
        · rcases mem_freeVarFinset_inf h12 with h1 | h2
          · rcases fv_isPair h1 with h' | h' | h' <;> omega
          · rcases fv_isPair h2 with h' | h' | h' <;> omega
        · rcases fv_isPair h3 with h' | h' | h' <;> omega
      · rcases fv_isPair h4 with h' | h' | h' <;> omega
    · rcases mem_freeVarFinset_mem h5 with h' | h' <;> omega
  let env : ℕ → M := Function.update (fun _ => UUU) 9 x
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = UUU := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 6) (a := 3) (b := 5) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 0) (a := 4) (b := 6) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 7) (a := 4) (b := 5) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 8) (a := 3) (b := 7) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (7 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 3),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, a, b, c, ac, bc, q, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
    exact ⟨a, b, c, ac, bc, q, h1, h2, h3, h4, h5⟩
  · rintro ⟨a, b, c, ac, bc, q, hac, hp, hbc, hq, hqx⟩
    have ⟨haU, hbcU⟩ := mem_trans_of_pair hM hU (hU x hxU q hqx) hq
    have ⟨hbU, hcU⟩ := mem_trans_of_pair hM hU hbcU hbc
    have hacUU : MemRelM ac UU := (hUU ac).mpr ⟨a, c, haU, hcU, hac⟩
    exact ⟨(hUUU p).mpr ⟨b, ac, hbU, hacUU, hp⟩, a, b, c, ac, bc, q, ⟨⟨⟨⟨hac, hp⟩, hbc⟩, hq⟩, hqx⟩⟩

private lemma innerShift_ex [Nonempty M] (x : M) : ∃ r : M, IsInnerShiftM r x := by
  obtain ⟨U, hxU, hU⟩ := exists_transitive_superset hM x
  obtain ⟨U2, hU2⟩ := prod_ex hM U U
  obtain ⟨U3, hU3⟩ := prod_ex hM U U2
  obtain ⟨U4, hU4⟩ := prod_ex hM U U3
  let φ : SFormula := ex 3 (ex 4 (ex 5 (ex 6 (ex 7 (ex 8 (ex 9 (ex 10 (ex 11
    (isPair 7 4 6 ⊓ isPair 8 5 7 ⊓ isPair 0 3 8 ⊓
     isPair 9 5 6 ⊓ isPair 10 4 9 ⊓ isPair 11 3 10 ⊓ mem 11 12)))))))))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, _⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h16 | h7
    · rcases mem_freeVarFinset_inf h16 with h15 | h6
      · rcases mem_freeVarFinset_inf h15 with h14 | h5
        · rcases mem_freeVarFinset_inf h14 with h13 | h4
          · rcases mem_freeVarFinset_inf h13 with h12 | h3
            · rcases mem_freeVarFinset_inf h12 with h1 | h2
              · rcases fv_isPair h1 with h' | h' | h' <;> omega
              · rcases fv_isPair h2 with h' | h' | h' <;> omega
            · rcases fv_isPair h3 with h' | h' | h' <;> omega
          · rcases fv_isPair h4 with h' | h' | h' <;> omega
        · rcases fv_isPair h5 with h' | h' | h' <;> omega
      · rcases fv_isPair h6 with h' | h' | h' <;> omega
    · rcases mem_freeVarFinset_mem h7 with h' | h' <;> omega
  let env : ℕ → M := Function.update (fun _ => U4) 12 x
  obtain ⟨r, hr⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  refine ⟨r, fun p => ?_⟩
  have hrp := hr p
  have h1 : env 1 = U4 := by simp [env]
  rw [h1] at hrp
  rw [hrp]
  simp only [φ, realize_ex, Formula.realize_inf, realize_mem,
    r_isPair (z := 7) (a := 4) (b := 6) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 8) (a := 5) (b := 7) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 0) (a := 3) (b := 8) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 9) (a := 5) (b := 6) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 10) (a := 4) (b := 9) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_isPair (z := 11) (a := 3) (b := 10) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    env, Function.update_self,
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 3), Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 5), Function.update_of_ne (by omega : (0 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 7), Function.update_of_ne (by omega : (0 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 9), Function.update_of_ne (by omega : (0 : ℕ) ≠ 10),
    Function.update_of_ne (by omega : (0 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 4), Function.update_of_ne (by omega : (3 : ℕ) ≠ 5),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 6), Function.update_of_ne (by omega : (3 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 8), Function.update_of_ne (by omega : (3 : ℕ) ≠ 9),
    Function.update_of_ne (by omega : (3 : ℕ) ≠ 10), Function.update_of_ne (by omega : (3 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 5), Function.update_of_ne (by omega : (4 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 7), Function.update_of_ne (by omega : (4 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 9), Function.update_of_ne (by omega : (4 : ℕ) ≠ 10),
    Function.update_of_ne (by omega : (4 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 6), Function.update_of_ne (by omega : (5 : ℕ) ≠ 7),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 8), Function.update_of_ne (by omega : (5 : ℕ) ≠ 9),
    Function.update_of_ne (by omega : (5 : ℕ) ≠ 10), Function.update_of_ne (by omega : (5 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 7), Function.update_of_ne (by omega : (6 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 9), Function.update_of_ne (by omega : (6 : ℕ) ≠ 10),
    Function.update_of_ne (by omega : (6 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (7 : ℕ) ≠ 8), Function.update_of_ne (by omega : (7 : ℕ) ≠ 9),
    Function.update_of_ne (by omega : (7 : ℕ) ≠ 10), Function.update_of_ne (by omega : (7 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (8 : ℕ) ≠ 9), Function.update_of_ne (by omega : (8 : ℕ) ≠ 10),
    Function.update_of_ne (by omega : (8 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (9 : ℕ) ≠ 10), Function.update_of_ne (by omega : (9 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (10 : ℕ) ≠ 11),
    Function.update_of_ne (by omega : (12 : ℕ) ≠ 11), Function.update_of_ne (by omega : (12 : ℕ) ≠ 10),
    Function.update_of_ne (by omega : (12 : ℕ) ≠ 9), Function.update_of_ne (by omega : (12 : ℕ) ≠ 8),
    Function.update_of_ne (by omega : (12 : ℕ) ≠ 7), Function.update_of_ne (by omega : (12 : ℕ) ≠ 6),
    Function.update_of_ne (by omega : (12 : ℕ) ≠ 5), Function.update_of_ne (by omega : (12 : ℕ) ≠ 4),
    Function.update_of_ne (by omega : (12 : ℕ) ≠ 3), Function.update_of_ne (by omega : (12 : ℕ) ≠ 0)]
  constructor
  · rintro ⟨_, d, a, b, c, ac, bac, bc, abc, q, ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩⟩
    exact ⟨d, a, b, c, ac, bac, bc, abc, q, h1, h2, h3, h4, h5, h6, h7⟩
  · rintro ⟨d, a, b, c, ac, bac, bc, abc, q, hac, hbac, hp, hbc, habc, hq, hqx⟩
    have ⟨hdU, habcU⟩ := mem_trans_of_pair hM hU (hU x hxU q hqx) hq
    have ⟨haU, hbcU⟩ := mem_trans_of_pair hM hU habcU habc
    have ⟨hbU, hcU⟩ := mem_trans_of_pair hM hU hbcU hbc
    have hacU2 : MemRelM ac U2 := (hU2 ac).mpr ⟨a, c, haU, hcU, hac⟩
    have hbacU3 : MemRelM bac U3 := (hU3 bac).mpr ⟨b, ac, hbU, hacU2, hbac⟩
    exact ⟨(hU4 p).mpr ⟨d, bac, hdU, hbacU3, hp⟩,
      d, a, b, c, ac, bac, bc, abc, q, ⟨⟨⟨⟨⟨⟨hac, hbac⟩, hp⟩, hbc⟩, habc⟩, hq⟩, hqx⟩⟩

/-! Functional wrappers via `Classical.choose` -/

noncomputable section Ops

private def emp [Nonempty M] : M := (emp_ex hM).choose
private lemma emp_spec [Nonempty M] : IsEmp (emp hM) := (emp_ex hM).choose_spec

private def sing (a : M) : M := (sing_ex hM a).choose
private lemma sing_spec (a : M) : IsSingM (sing hM a) a := (sing_ex hM a).choose_spec

private def dbl (a b : M) : M := (ax_pair hM a b).choose
private lemma dbl_spec (a b : M) : IsDblM (dbl hM a b) a b := (ax_pair hM a b).choose_spec

private def pair (a b : M) : M := (pair_ex hM a b).choose
private lemma pair_spec (a b : M) : IsPairM (pair hM a b) a b := (pair_ex hM a b).choose_spec

private lemma pair_eq_iff {a₁ b₁ a₂ b₂ : M} :
    pair hM a₁ b₁ = pair hM a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ :=
  ⟨fun h => pair_inj hM (pair_spec hM a₁ b₁) (pair_spec hM a₂ b₂) h,
   fun ⟨h1, h2⟩ => by subst h1 h2; rfl⟩

private def bigUnion (x : M) : M := (ax_union hM x).choose
private lemma bigUnion_spec (x : M) : IsUnionM (bigUnion hM x) x := (ax_union hM x).choose_spec

private def diff (x y : M) : M := (diff_ex hM x y).choose
private lemma diff_spec (x y : M) : IsDiffM (diff hM x y) x y := (diff_ex hM x y).choose_spec

private def prod (x y : M) : M := (prod_ex hM x y).choose
private lemma prod_spec (x y : M) : IsProdM (prod hM x y) x y := (prod_ex hM x y).choose_spec

private lemma mem_prod_iff {x y z : M} :
    MemRelM z (prod hM x y) ↔ ∃ a b : M, MemRelM a x ∧ MemRelM b y ∧ z = pair hM a b := by
  rw [prod_spec]
  constructor
  · rintro ⟨a, b, ha, hb, hp⟩; exact ⟨a, b, ha, hb, pair_uniq hM hp (pair_spec hM a b)⟩
  · rintro ⟨a, b, ha, hb, rfl⟩; exact ⟨a, b, ha, hb, pair_spec hM a b⟩

private def dom (x : M) : M := (dom_ex hM x).choose
private lemma dom_spec (x : M) : IsDomM (dom hM x) x := (dom_ex hM x).choose_spec

private lemma mem_dom_iff {x a : M} :
    MemRelM a (dom hM x) ↔ ∃ b : M, MemRelM (pair hM a b) x := by
  rw [dom_spec]
  constructor
  · rintro ⟨b, p, hp, hpx⟩; exact ⟨b, (pair_uniq hM (pair_spec hM a b) hp).symm ▸ hpx⟩
  · rintro ⟨b, hbx⟩; exact ⟨b, pair hM a b, pair_spec hM a b, hbx⟩

private def memGraph (x : M) : M := (memGraph_ex hM x).choose
private lemma memGraph_spec (x : M) : IsMemGraphM (memGraph hM x) x := (memGraph_ex hM x).choose_spec

private lemma mem_memGraph_iff {x z : M} :
    MemRelM z (memGraph hM x) ↔
      ∃ a b : M, MemRelM a x ∧ MemRelM b x ∧ MemRelM a b ∧ z = pair hM a b := by
  rw [memGraph_spec]
  constructor
  · rintro ⟨a, b, ha, hb, hab, hp⟩; exact ⟨a, b, ha, hb, hab, pair_uniq hM hp (pair_spec hM a b)⟩
  · rintro ⟨a, b, ha, hb, hab, rfl⟩; exact ⟨a, b, ha, hb, hab, pair_spec hM a b⟩

private def eqGraph (x : M) : M := (eqGraph_ex hM x).choose
private lemma eqGraph_spec (x : M) : IsEqGraphM (eqGraph hM x) x := (eqGraph_ex hM x).choose_spec

private lemma mem_eqGraph_iff {x z : M} :
    MemRelM z (eqGraph hM x) ↔ ∃ a : M, MemRelM a x ∧ z = pair hM a a := by
  rw [eqGraph_spec]
  constructor
  · rintro ⟨a, ha, hp⟩; exact ⟨a, ha, pair_uniq hM hp (pair_spec hM a a)⟩
  · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, pair_spec hM a a⟩

section OpsNonempty

variable [Nonempty M]

private def swap (x : M) : M := (swap_ex hM x).choose
private lemma swap_spec (x : M) : IsSwapM (swap hM x) x := (swap_ex hM x).choose_spec

private lemma mem_swap_iff {x z : M} :
    MemRelM z (swap hM x) ↔ ∃ a b : M, z = pair hM b a ∧ MemRelM (pair hM a b) x := by
  rw [swap_spec]
  constructor
  · rintro ⟨a, b, q, hp, hq, hqx⟩
    refine ⟨a, b, pair_uniq hM hp (pair_spec hM b a), ?_⟩
    rwa [pair_uniq hM (pair_spec hM a b) hq]
  · rintro ⟨a, b, rfl, hqx⟩
    exact ⟨a, b, pair hM a b, pair_spec hM b a, pair_spec hM a b, hqx⟩

private def pull (x : M) : M := (pull_ex hM x).choose
private lemma pull_spec (x : M) : IsPullM (pull hM x) x := (pull_ex hM x).choose_spec

private lemma mem_pull_iff {x z : M} :
    MemRelM z (pull hM x) ↔
      ∃ a b c : M, z = pair hM (pair hM a b) c ∧ MemRelM (pair hM a (pair hM b c)) x := by
  rw [pull_spec]
  constructor
  · rintro ⟨a, b, c, ab, bc, q, hab, hp, hbc, hq, hqx⟩
    have hab' := pair_uniq hM hab (pair_spec hM a b)
    have hbc' := pair_uniq hM hbc (pair_spec hM b c)
    subst hab' hbc'
    refine ⟨a, b, c, pair_uniq hM hp (pair_spec hM (pair hM a b) c), ?_⟩
    rwa [pair_uniq hM (pair_spec hM a (pair hM b c)) hq]
  · rintro ⟨a, b, c, rfl, hqx⟩
    exact ⟨a, b, c, pair hM a b, pair hM b c, pair hM a (pair hM b c),
      pair_spec hM a b, pair_spec hM (pair hM a b) c, pair_spec hM b c,
      pair_spec hM a (pair hM b c), hqx⟩

private def push (x : M) : M := (push_ex hM x).choose
private lemma push_spec (x : M) : IsPushM (push hM x) x := (push_ex hM x).choose_spec

private lemma mem_push_iff {x z : M} :
    MemRelM z (push hM x) ↔
      ∃ a b c : M, z = pair hM a (pair hM b c) ∧ MemRelM (pair hM (pair hM a b) c) x := by
  rw [push_spec]
  constructor
  · rintro ⟨a, b, c, ab, bc, q, hbc, hp, hab, hq, hqx⟩
    have hab' := pair_uniq hM hab (pair_spec hM a b)
    have hbc' := pair_uniq hM hbc (pair_spec hM b c)
    subst hab' hbc'
    refine ⟨a, b, c, pair_uniq hM hp (pair_spec hM a (pair hM b c)), ?_⟩
    rwa [pair_uniq hM (pair_spec hM (pair hM a b) c) hq]
  · rintro ⟨a, b, c, rfl, hqx⟩
    exact ⟨a, b, c, pair hM a b, pair hM b c, pair hM (pair hM a b) c,
      pair_spec hM b c, pair_spec hM a (pair hM b c), pair_spec hM a b,
      pair_spec hM (pair hM a b) c, hqx⟩

private def shift (x : M) : M := (shift_ex hM x).choose
private lemma shift_spec (x : M) : IsShiftM (shift hM x) x := (shift_ex hM x).choose_spec

private lemma mem_shift_iff {x z : M} :
    MemRelM z (shift hM x) ↔
      ∃ a b c : M, z = pair hM b (pair hM a c) ∧ MemRelM (pair hM a (pair hM b c)) x := by
  rw [shift_spec]
  constructor
  · rintro ⟨a, b, c, ac, bc, q, hac, hp, hbc, hq, hqx⟩
    have hac' := pair_uniq hM hac (pair_spec hM a c)
    have hbc' := pair_uniq hM hbc (pair_spec hM b c)
    subst hac' hbc'
    refine ⟨a, b, c, pair_uniq hM hp (pair_spec hM b (pair hM a c)), ?_⟩
    rwa [pair_uniq hM (pair_spec hM a (pair hM b c)) hq]
  · rintro ⟨a, b, c, rfl, hqx⟩
    exact ⟨a, b, c, pair hM a c, pair hM b c, pair hM a (pair hM b c),
      pair_spec hM a c, pair_spec hM b (pair hM a c), pair_spec hM b c,
      pair_spec hM a (pair hM b c), hqx⟩

private def innerShift (x : M) : M := (innerShift_ex hM x).choose
private lemma innerShift_spec (x : M) : IsInnerShiftM (innerShift hM x) x :=
  (innerShift_ex hM x).choose_spec

private lemma mem_innerShift_iff {x z : M} :
    MemRelM z (innerShift hM x) ↔
      ∃ d a b c : M,
        z = pair hM d (pair hM b (pair hM a c)) ∧
        MemRelM (pair hM d (pair hM a (pair hM b c))) x := by
  rw [innerShift_spec]
  constructor
  · rintro ⟨d, a, b, c, ac, bac, bc, abc, q, hac, hbac, hp, hbc, habc, hq, hqx⟩
    have hac' := pair_uniq hM hac (pair_spec hM a c)
    subst hac'
    have hbac' := pair_uniq hM hbac (pair_spec hM b (pair hM a c))
    subst hbac'
    have hbc' := pair_uniq hM hbc (pair_spec hM b c)
    subst hbc'
    have habc' := pair_uniq hM habc (pair_spec hM a (pair hM b c))
    subst habc'
    refine ⟨d, a, b, c, pair_uniq hM hp (pair_spec hM d (pair hM b (pair hM a c))), ?_⟩
    rwa [pair_uniq hM (pair_spec hM d (pair hM a (pair hM b c))) hq]
  · rintro ⟨d, a, b, c, rfl, hqx⟩
    exact ⟨d, a, b, c, pair hM a c, pair hM b (pair hM a c), pair hM b c,
      pair hM a (pair hM b c), pair hM d (pair hM a (pair hM b c)),
      pair_spec hM a c, pair_spec hM b (pair hM a c),
      pair_spec hM d (pair hM b (pair hM a c)),
      pair_spec hM b c, pair_spec hM a (pair hM b c),
      pair_spec hM d (pair hM a (pair hM b c)), hqx⟩

end OpsNonempty

/-! `k`-commutation for every Gödel operation -/

section KComm

variable (k : M → M) (hk : IsGodelCofinalEmb k)
include hk

private lemma k_inj : Function.Injective k := by
  intro x y hxy
  apply ax_ext hM x y
  intro z
  rw [hk.pres_mem z x, hk.pres_mem z y, hxy]

private lemma k_emp [Nonempty M] : k (emp hM) = emp hM := by
  let a : M := Classical.arbitrary M
  have hdiff : IsDiffM (emp hM) a a := fun z =>
    ⟨fun hz => absurd hz (emp_spec hM z), fun ⟨h1, h2⟩ => absurd h1 h2⟩
  have hkdiff := hk.pres_diff (emp hM) a a hdiff
  exact emp_uniq hM (fun z hz => by have := (hkdiff z).mp hz; exact this.2 this.1) (emp_spec hM)

private lemma k_dbl (a b : M) : k (dbl hM a b) = dbl hM (k a) (k b) :=
  ax_ext hM _ _ fun z => (hk.pres_dbl _ _ _ (dbl_spec hM a b) z).trans (dbl_spec hM (k a) (k b) z).symm

private lemma k_sing (a : M) : k (sing hM a) = sing hM (k a) := by
  have h : IsDblM (sing hM a) a a := fun z => by simpa using sing_spec hM a z
  have hk' := hk.pres_dbl _ _ _ h
  exact ax_ext hM _ _ fun z => by simpa [sing_spec hM (k a) z] using hk' z

private lemma k_pair (a b : M) : k (pair hM a b) = pair hM (k a) (k b) := by
  have hd : IsDblM (pair hM a b) (sing hM a) (dbl hM a b) := fun w => by
    rw [pair_spec hM a b w]
    constructor
    · rintro (hs | hd')
      · exact Or.inl (sing_uniq hM hs (sing_spec hM a))
      · exact Or.inr (ax_ext hM w (dbl hM a b) fun z => (hd' z).trans (dbl_spec hM a b z).symm)
    · rintro (rfl | rfl)
      · exact Or.inl (sing_spec hM a)
      · exact Or.inr (dbl_spec hM a b)
  have hkd := hk.pres_dbl _ _ _ hd
  rw [k_sing hM k hk a, k_dbl hM k hk a b] at hkd
  apply ax_ext hM _ _
  intro w
  rw [hkd w, pair_spec hM (k a) (k b) w]
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl (sing_spec hM (k a))
    · exact Or.inr (dbl_spec hM (k a) (k b))
  · rintro (hs | hd')
    · exact Or.inl (sing_uniq hM hs (sing_spec hM (k a)))
    · exact Or.inr (ax_ext hM w (dbl hM (k a) (k b)) fun z => (hd' z).trans (dbl_spec hM (k a) (k b) z).symm)

private lemma k_bigUnion (x : M) : k (bigUnion hM x) = bigUnion hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_union _ _ (bigUnion_spec hM x) z).trans (bigUnion_spec hM (k x) z).symm

private lemma k_diff (x y : M) : k (diff hM x y) = diff hM (k x) (k y) :=
  ax_ext hM _ _ fun z => (hk.pres_diff _ _ _ (diff_spec hM x y) z).trans (diff_spec hM (k x) (k y) z).symm

private lemma k_prod (x y : M) : k (prod hM x y) = prod hM (k x) (k y) :=
  ax_ext hM _ _ fun z => (hk.pres_prod _ _ _ (prod_spec hM x y) z).trans (prod_spec hM (k x) (k y) z).symm

private lemma k_dom (x : M) : k (dom hM x) = dom hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_dom _ _ (dom_spec hM x) z).trans (dom_spec hM (k x) z).symm

private lemma k_memGraph (x : M) : k (memGraph hM x) = memGraph hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_memGraph _ _ (memGraph_spec hM x) z).trans (memGraph_spec hM (k x) z).symm

private lemma k_eqGraph (x : M) : k (eqGraph hM x) = eqGraph hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_eqGraph _ _ (eqGraph_spec hM x) z).trans (eqGraph_spec hM (k x) z).symm

private lemma k_swap [Nonempty M] (x : M) : k (swap hM x) = swap hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_swap _ _ (swap_spec hM x) z).trans (swap_spec hM (k x) z).symm

private lemma k_pull [Nonempty M] (x : M) : k (pull hM x) = pull hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_pull _ _ (pull_spec hM x) z).trans (pull_spec hM (k x) z).symm

private lemma k_push [Nonempty M] (x : M) : k (push hM x) = push hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_push _ _ (push_spec hM x) z).trans (push_spec hM (k x) z).symm

private lemma k_shift [Nonempty M] (x : M) : k (shift hM x) = shift hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_shift _ _ (shift_spec hM x) z).trans (shift_spec hM (k x) z).symm

private lemma k_innerShift [Nonempty M] (x : M) : k (innerShift hM x) = innerShift hM (k x) :=
  ax_ext hM _ _ fun z => (hk.pres_innerShift _ _ (innerShift_spec hM x) z).trans (innerShift_spec hM (k x) z).symm

private lemma k_trans [Nonempty M] {T : M} (hT : Trans T) : Trans (k T) := by
  have hd_emp : diff hM (bigUnion hM T) T = emp hM := by
    apply ax_ext hM _ _
    intro z
    rw [diff_spec hM]
    refine ⟨fun ⟨hzu, hzT⟩ => ?_, fun hze => absurd hze (emp_spec hM z)⟩
    obtain ⟨y, hyT, hzy⟩ := (bigUnion_spec hM T z).mp hzu
    exact absurd (hT y hyT z hzy) hzT
  have hkd : diff hM (bigUnion hM (k T)) (k T) = emp hM := by
    rw [← k_bigUnion hM k hk T, ← k_diff hM k hk, hd_emp, k_emp hM k hk]
  intro y hyT z hzy
  have hzu : MemRelM z (bigUnion hM (k T)) := (bigUnion_spec hM (k T) z).mpr ⟨y, hyT, hzy⟩
  by_contra hzT
  have hzd : MemRelM z (diff hM (bigUnion hM (k T)) (k T)) := (diff_spec hM _ _ z).mpr ⟨hzu, hzT⟩
  rw [hkd] at hzd
  exact emp_spec hM z hzd

end KComm

end Ops

end Semantics

/-! ### Part 6: Pure syntax for bounded (`Δ₀`) formulas `BForm`, adjacent swap combinatorics, and `Levy` -/

private inductive BForm : ℕ → Type where
  | falsum {m} : BForm m
  | eq {m} (i j : Fin m) : BForm m
  | mem {m} (i j : Fin m) : BForm m
  | imp {m} (φ ψ : BForm m) : BForm m
  | bEx {m} (i : Fin m) (φ : BForm (m + 1)) : BForm m

private def BForm.not {m} (φ : BForm m) : BForm m := BForm.imp φ BForm.falsum
private def BForm.or {m} (φ ψ : BForm m) : BForm m := BForm.imp φ.not ψ
private def BForm.and {m} (φ ψ : BForm m) : BForm m := (BForm.imp φ ψ.not).not
private def BForm.bAll {m} (i : Fin m) (φ : BForm (m + 1)) : BForm m := (BForm.bEx i φ.not).not

private def BForm.lift : ∀ {m m'}, BForm m → (Fin m → Fin m') → BForm m'
  | _, _, .falsum, _ => .falsum
  | _, _, .eq i j, r => .eq (r i) (r j)
  | _, _, .mem i j, r => .mem (r i) (r j)
  | _, _, .imp φ ψ, r => .imp (φ.lift r) (ψ.lift r)
  | _, _, .bEx i φ, r => .bEx (r i) (φ.lift (Fin.cons 0 (Fin.succ ∘ r)))

private noncomputable def BForm.toFormula : ∀ {m}, BForm m → (Fin m → ℕ) → ℕ → SFormula
  | _, .falsum, _, _ => BoundedFormula.falsum
  | _, .eq i j, vars, _ => SFormula.eq (vars i) (vars j)
  | _, .mem i j, vars, _ => SFormula.mem (vars i) (vars j)
  | _, .imp φ ψ, vars, nxt => φ.toFormula vars nxt ⟹ ψ.toFormula vars nxt
  | _, .bEx i φ, vars, nxt =>
    ex nxt (SFormula.mem nxt (vars i) ⊓ φ.toFormula (Fin.cons nxt vars) (nxt + 1))

private lemma BForm.fv_toFormula : ∀ {m} (φ : BForm m) (vars : Fin m → ℕ) (nxt : ℕ)
    {v : ℕ}, v ∈ (φ.toFormula vars nxt).freeVarFinset → ∃ j : Fin m, v = vars j
  | _, .falsum, _, _, _, hv => by simp [BForm.toFormula] at hv
  | _, .eq i j, vars, _, _, hv => by
    rcases mem_freeVarFinset_eq hv with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
  | _, .mem i j, vars, _, _, hv => by
    rcases mem_freeVarFinset_mem hv with rfl | rfl
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
  | _, .imp φ ψ, vars, nxt, _, hv => by
    rcases mem_freeVarFinset_imp hv with h1 | h2
    · exact BForm.fv_toFormula φ vars nxt h1
    · exact BForm.fv_toFormula ψ vars nxt h2
  | _, .bEx i φ, vars, nxt, _, hv => by
    obtain ⟨h1, hne⟩ := mem_freeVarFinset_ex hv
    rcases mem_freeVarFinset_inf h1 with ha | hb
    · rcases mem_freeVarFinset_mem ha with rfl | rfl
      · exact absurd rfl hne
      · exact ⟨i, rfl⟩
    · obtain ⟨j, hj⟩ := BForm.fv_toFormula φ (Fin.cons nxt vars) (nxt + 1) hb
      refine Fin.cases ?_ ?_ j hj
      · intro h0; exact absurd h0 hne
      · intro k hk; exact ⟨k, hk⟩

private def isSingBForm {m} (s a : Fin m) : BForm m :=
  .and (.mem a s) (.bAll s (.eq 0 a.succ))

private def isDblBForm {m} (d a b : Fin m) : BForm m :=
  .and (.and (.mem a d) (.mem b d)) (.bAll d (.or (.eq 0 a.succ) (.eq 0 b.succ)))

private def isPairBForm : BForm 3 :=
  .and (.and (.bEx 0 (isSingBForm 0 2)) (.bEx 0 (isDblBForm 0 2 3)))
    (.bAll 0 (.or (isSingBForm 0 2) (isDblBForm 0 2 3)))

private def swapLast (i : ℕ) (x : Fin (i + 2)) : Fin (i + 2) :=
  if x.1 = i then ⟨i + 1, by omega⟩
  else if x.1 = i + 1 then ⟨i, by omega⟩
  else x

private lemma swapLast_invol (i : ℕ) (x : Fin (i + 2)) :
    swapLast i (swapLast i x) = x := by
  ext
  by_cases h1 : x.1 = i
  · simp [swapLast, h1]
  · by_cases h2 : x.1 = i + 1
    · simp [swapLast, h2]
    · simp [swapLast, h1, h2]

private def swapAt {m : ℕ} (idx : ℕ) (hidx : idx + 1 < m) (x : Fin m) : Fin m :=
  if x.1 = idx then ⟨idx + 1, hidx⟩
  else if x.1 = idx + 1 then ⟨idx, by omega⟩
  else x

private lemma swapAt_invol {m : ℕ} (idx : ℕ) (hidx : idx + 1 < m) (x : Fin m) :
    swapAt idx hidx (swapAt idx hidx x) = x := by
  ext
  by_cases h1 : x.1 = idx
  · simp [swapAt, h1]
  · by_cases h2 : x.1 = idx + 1
    · simp [swapAt, h2]
    · simp [swapAt, h1, h2]

private def permOfSwaps {m : ℕ} : List { idx : ℕ // idx + 1 < m } → Fin m → Fin m
  | [] => id
  | a :: l => swapAt a.1 a.2 ∘ permOfSwaps l

private lemma permOfSwaps_append {m : ℕ} (l₁ l₂ : List { idx : ℕ // idx + 1 < m }) (x : Fin m) :
    permOfSwaps (l₁ ++ l₂) x = permOfSwaps l₁ (permOfSwaps l₂ x) := by
  induction l₁ with
  | nil => rfl
  | cons a l₁ ih => simp [permOfSwaps, ih]

private def moveDown {m : ℕ} (a : ℕ) : ∀ (b : ℕ), b < m → List { idx : ℕ // idx + 1 < m }
  | 0, _ => []
  | b + 1, hb =>
    if a ≤ b then ⟨b, hb⟩ :: moveDown a b (by omega)
    else []

private lemma permOfSwaps_moveDown {m : ℕ} (a b : ℕ) (hab : a ≤ b) (hb : b < m) (x : Fin m) :
    (permOfSwaps (moveDown a b hb) x).1 =
      if x.1 < a then x.1
      else if x.1 = a then b
      else if x.1 ≤ b then x.1 - 1
      else x.1 := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    simp only [moveDown, permOfSwaps, id_eq]
    split_ifs <;> omega
  | succ b ih =>
    by_cases hlt : a ≤ b
    · simp only [moveDown, hlt, ↓reduceIte, permOfSwaps, Function.comp_apply]
      have hih := ih hlt (by omega)
      dsimp only [swapAt]
      split_ifs at hih ⊢ <;> (try dsimp only at hih ⊢) <;> omega
    · have ha : a = b + 1 := by omega
      subst ha
      simp only [moveDown, hlt, ↓reduceIte, permOfSwaps, id_eq]
      split_ifs <;> omega

private def swapsFor {m : ℕ} (i j : Fin m) (_hne : i ≠ j) : List { idx : ℕ // idx + 1 < m } :=
  let j' : ℕ := if j.1 < i.1 then j.1 + 1 else j.1
  have hj' : j' < m := by
    dsimp [j']; split_ifs with h
    · omega
    · exact j.2
  moveDown 0 i.1 i.2 ++ moveDown 1 j' hj'

private lemma permOfSwaps_swapsFor {m : ℕ} (i j : Fin m) (hne : i ≠ j) :
    permOfSwaps (swapsFor i j hne) ⟨0, by omega⟩ = i ∧
    permOfSwaps (swapsFor i j hne) ⟨1, by
      have : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
      omega⟩ = j := by
  have hne' : i.1 ≠ j.1 := fun h => hne (Fin.ext h)
  let j' : ℕ := if j.1 < i.1 then j.1 + 1 else j.1
  have hj'1 : 1 ≤ j' := by dsimp [j']; split_ifs <;> omega
  have hj'm : j' < m := by dsimp [j']; split_ifs <;> omega
  constructor
  · apply Fin.ext
    change (permOfSwaps (moveDown 0 i.1 i.2 ++ moveDown 1 j' hj'm) ⟨0, by omega⟩).1 = i.1
    rw [permOfSwaps_append, permOfSwaps_moveDown 0 i.1 (Nat.zero_le _) i.2]
    have h2 : (permOfSwaps (moveDown 1 j' hj'm) ⟨0, by omega⟩).1 = 0 := by
      rw [permOfSwaps_moveDown 1 j' hj'1 hj'm]; simp
    rw [h2]; simp
  · apply Fin.ext
    change (permOfSwaps (moveDown 0 i.1 i.2 ++ moveDown 1 j' hj'm) ⟨1, by omega⟩).1 = j.1
    rw [permOfSwaps_append, permOfSwaps_moveDown 0 i.1 (Nat.zero_le _) i.2]
    have h2 : (permOfSwaps (moveDown 1 j' hj'm) ⟨1, by omega⟩).1 = j' := by
      rw [permOfSwaps_moveDown 1 j' hj'1 hj'm]; simp
    have h0 : ¬ (j' < 0) := Nat.not_lt_zero _
    have h1 : j' ≠ 0 := by omega
    rw [h2]
    simp only [h0, h1, ↓reduceIte]
    by_cases hji : j.1 < i.1
    · have hj'eq : j' = j.1 + 1 := by simp [j', hji]
      have hle : j' ≤ i.1 := by omega
      simp only [hle, ↓reduceIte]; omega
    · have hj'eq : j' = j.1 := by simp [j', hji]
      have hgt : ¬ (j' ≤ i.1) := by omega
      simp only [hgt, ↓reduceIte]; omega

private def Levy : ℕ → ℕ → Type
  | 0, m => BForm m
  | n + 1, m => Levy n (m + 1)

private def Levy.step {n m : ℕ} (ψ : Levy n (m + 1)) : Levy (n + 1) m := ψ
private def Levy.unstep {n m : ℕ} (φ : Levy (n + 1) m) : Levy n (m + 1) := φ
private lemma Levy.unstep_step {n m : ℕ} (ψ : Levy n (m + 1)) : Levy.unstep (Levy.step ψ) = ψ := rfl

private def Levy.lift : ∀ {n m m' : ℕ}, Levy n m → (Fin m → Fin m') → Levy n m'
  | 0, _, _, b, r => BForm.lift b r
  | n + 1, m, m', ψ, r =>
    Levy.step (Levy.lift (n := n) (m := m + 1) (m' := m' + 1) (Levy.unstep ψ) (Fin.cons 0 (Fin.succ ∘ r)))

private noncomputable def Levy.toFormula : ∀ {n m : ℕ}, Levy n m → (Fin m → ℕ) → ℕ → SFormula
  | 0, _, b, vars, nxt => BForm.toFormula b vars nxt
  | n + 1, m, ψ, vars, nxt =>
    ex nxt (∼(Levy.toFormula (n := n) (m := m + 1) (Levy.unstep ψ) (Fin.cons nxt vars) (nxt + 1)))

private lemma Levy.fv_toFormula : ∀ {n m : ℕ} (φ : Levy n m) (vars : Fin m → ℕ) (nxt : ℕ)
    {v : ℕ}, v ∈ (Levy.toFormula (n := n) φ vars nxt).freeVarFinset → ∃ j : Fin m, v = vars j
  | 0, _, b, vars, nxt, _, hv => BForm.fv_toFormula b vars nxt hv
  | n + 1, m, ψ, vars, nxt, _, hv => by
    obtain ⟨h1, hne⟩ := mem_freeVarFinset_ex hv
    obtain ⟨j, hj⟩ := Levy.fv_toFormula (n := n) (m := m + 1) (Levy.unstep ψ) (Fin.cons nxt vars) (nxt + 1)
      (mem_freeVarFinset_not h1)
    refine Fin.cases ?_ ?_ j hj
    · intro h0; exact absurd h0 hne
    · intro k hk; exact ⟨k, hk⟩

private def Levy.neg {n m : ℕ} (φ : Levy n m) : Levy (n + 1) m :=
  Levy.step (Levy.lift (n := n) (m := m) (m' := m + 1) φ Fin.succ)

private def Levy.ofBForm : ∀ (n : ℕ) {m : ℕ}, BForm m → Levy n m
  | 0, _, b => b
  | n + 1, _, b => Levy.neg (Levy.ofBForm n b.not)

private def Levy.raise1 : ∀ {n m : ℕ}, Levy n m → Levy (n + 1) m
  | 0, _, b => Levy.ofBForm 1 b
  | n + 1, m, ψ => Levy.step (Levy.raise1 (n := n) (m := m + 1) (Levy.unstep ψ))

private def Levy.raiseAdd : ∀ {n m : ℕ} (d : ℕ), Levy n m → Levy (n + d) m
  | _, _, 0, φ => φ
  | _, _, d + 1, φ => Levy.raise1 (Levy.raiseAdd d φ)

private def Levy.castN {n₁ n₂ m : ℕ} (h : n₁ = n₂) (φ : Levy n₁ m) : Levy n₂ m := h ▸ φ

private def Levy.raiseLe {n₁ n₂ m : ℕ} (h : n₁ ≤ n₂) (φ : Levy n₁ m) : Levy n₂ m :=
  Levy.castN (Nat.add_sub_of_le h) (Levy.raiseAdd (n₂ - n₁) φ)

private def swap01 {m : ℕ} : Fin (m + 2) → Fin (m + 2) :=
  Fin.cons 1 (Fin.cons 0 (Fin.succ ∘ Fin.succ))

private def consToSnoc (k : ℕ) (i : Fin (k + 1)) : Fin (k + 1) :=
  if h : i.1 < k then ⟨i.1 + 1, by omega⟩ else 0

private def termIdx {m l : ℕ} :
    (t : setLang.Term (ℕ ⊕ Fin l)) → (∀ a ∈ t.varFinsetLeft, a < m) → Fin (m + l)
  | .var (.inl a), ht => ⟨a, by
      have ha : a < m := ht a (by simp [Term.varFinsetLeft])
      omega⟩
  | .var (.inr j), _ => ⟨m + j.1, by omega⟩
  | .func f _, _ => Empty.elim f

/-! ### Part 7: Semantics of `BForm` and `Levy`, Gödel truth sets `evalSet`, and Gaifman's Lemma -/

private lemma cons_comp_swap01 {M : Type u} {m : ℕ} (a b : M) (f : Fin m → M) :
    Fin.cons a (Fin.cons b f) ∘ swap01 = Fin.cons b (Fin.cons a f) := by
  ext j
  refine Fin.cases rfl (fun j' => Fin.cases rfl (fun _ => rfl) j') j

private lemma cons_comp_consToSnoc {M : Type u} {k : ℕ} (a : M) (g : Fin k → M) :
    Fin.cons a g ∘ consToSnoc k = Fin.snoc g a := by
  ext ⟨i, hi⟩
  simp only [Function.comp_apply, consToSnoc, Fin.snoc]
  split_ifs with h1
  · simp [Fin.cons]
  · have hi_eq : i = k := by omega
    subst hi_eq
    simp [Fin.cons]

private lemma append_snoc {M : Type u} {m l : ℕ} (u : Fin m → M) (xs : Fin l → M) (a : M) :
    Fin.append u (Fin.snoc xs a) = Fin.snoc (Fin.append u xs) a := by
  ext ⟨i, hi⟩
  simp only [Fin.append, Fin.snoc, Fin.addCases]
  by_cases h1 : i < m
  · have h2 : i < m + l := by omega
    simp [h1, h2]
  · by_cases h2 : i < m + l
    · have h3 : i - m < l := by omega
      simp [h1, h2, h3]
    · have h3 : ¬ (i - m < l) := by omega
      simp [h1, h2, h3]

section Semantics2

variable {M : Type u} [setLangJ.Structure M]
local instance : setLang.Structure M := incl.reduct M

private def BForm.eval : ∀ {m}, BForm m → (Fin m → M) → Prop
  | _, .falsum, _ => False
  | _, .eq i j, f => f i = f j
  | _, .mem i j, f => MemRelM (f i) (f j)
  | _, .imp φ ψ, f => φ.eval f → ψ.eval f
  | _, .bEx i φ, f => ∃ w : M, MemRelM w (f i) ∧ φ.eval (Fin.cons w f)

private lemma BForm.eval_not {m} (φ : BForm m) (f : Fin m → M) :
    φ.not.eval f ↔ ¬ φ.eval f := Iff.rfl

private lemma BForm.eval_or {m} (φ ψ : BForm m) (f : Fin m → M) :
    (φ.or ψ).eval f ↔ φ.eval f ∨ ψ.eval f := by
  simp only [BForm.or, BForm.not, BForm.eval]; tauto

private lemma BForm.eval_and {m} (φ ψ : BForm m) (f : Fin m → M) :
    (φ.and ψ).eval f ↔ φ.eval f ∧ ψ.eval f := by
  simp only [BForm.and, BForm.not, BForm.eval]; tauto

private lemma BForm.eval_bAll {m} (i : Fin m) (φ : BForm (m + 1)) (f : Fin m → M) :
    (φ.bAll i).eval f ↔ ∀ w : M, MemRelM w (f i) → φ.eval (Fin.cons w f) := by
  simp only [BForm.bAll, BForm.not, BForm.eval]
  constructor
  · intro h w hw
    by_contra hφ
    exact h ⟨w, hw, hφ⟩
  · rintro h ⟨w, hw, hφ⟩
    exact hφ (h w hw)

private lemma BForm.eval_lift : ∀ {m m'} (φ : BForm m) (r : Fin m → Fin m') (f : Fin m' → M),
    (φ.lift r).eval f ↔ φ.eval (f ∘ r)
  | _, _, .falsum, _, _ => Iff.rfl
  | _, _, .eq _ _, _, _ => Iff.rfl
  | _, _, .mem _ _, _, _ => Iff.rfl
  | _, _, .imp φ ψ, r, f => by
    simp only [BForm.lift, BForm.eval, BForm.eval_lift φ r f, BForm.eval_lift ψ r f]
  | _, _, .bEx i φ, r, f => by
    simp only [BForm.lift, BForm.eval, Function.comp_apply]
    refine exists_congr fun w => and_congr_right fun _ => ?_
    have hcomp : Fin.cons w f ∘ Fin.cons 0 (Fin.succ ∘ r) = Fin.cons w (f ∘ r) := by
      ext j
      refine Fin.cases ?_ ?_ j
      · rfl
      · intro k; rfl
    rw [BForm.eval_lift φ, hcomp]

private lemma BForm.realize_toFormula : ∀ {m} (φ : BForm m) (vars : Fin m → ℕ) (nxt : ℕ)
    (_hvars : ∀ i : Fin m, vars i < nxt) (env : ℕ → M),
    Formula.Realize (φ.toFormula vars nxt) env ↔ φ.eval (env ∘ vars)
  | _, .falsum, _, _, _, _ => by
    simp [BForm.toFormula, BForm.eval, Formula.Realize, BoundedFormula.Realize]
  | _, .eq i j, vars, _, _, env => by
    simp [BForm.toFormula, BForm.eval, realize_eq]
  | _, .mem i j, vars, _, _, env => by
    simp [BForm.toFormula, BForm.eval, realize_mem]
  | _, .imp φ ψ, vars, nxt, hvars, env => by
    simp only [BForm.toFormula, BForm.eval, Formula.realize_imp,
      BForm.realize_toFormula φ vars nxt hvars env,
      BForm.realize_toFormula ψ vars nxt hvars env]
  | _, .bEx i φ, vars, nxt, hvars, env => by
    simp only [BForm.toFormula, BForm.eval, realize_ex, Formula.realize_inf, realize_mem,
      Function.comp_apply]
    refine exists_congr fun w => ?_
    have hne : vars i ≠ nxt := Nat.ne_of_lt (hvars i)
    simp only [Function.update_self, Function.update_of_ne hne]
    refine and_congr_right fun _ => ?_
    have hvars' : ∀ j : Fin (_ + 1), (Fin.cons (α := fun _ => ℕ) nxt vars) j < nxt + 1 := by
      intro j; refine Fin.cases ?_ ?_ j
      · simp
      · intro k; exact Nat.lt_succ_of_lt (hvars k)
    rw [BForm.realize_toFormula φ (Fin.cons nxt vars) (nxt + 1) hvars']
    have hcomp : Function.update env nxt w ∘ Fin.cons nxt vars = Fin.cons w (env ∘ vars) := by
      ext j; refine Fin.cases ?_ ?_ j
      · simp
      · intro k
        have hnk : vars k ≠ nxt := Nat.ne_of_lt (hvars k)
        simp [Function.update_of_ne hnk]
    rw [hcomp]

private lemma eval_isSingBForm {m} (s a : Fin m) (f : Fin m → M) :
    (isSingBForm s a).eval f ↔ IsSingM (f s) (f a) := by
  simp only [isSingBForm, BForm.eval_and, BForm.eval_bAll, BForm.eval, Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨has, h⟩ z
    exact ⟨fun hz => h z hz, fun hz => hz ▸ has⟩
  · intro h
    exact ⟨(h (f a)).mpr rfl, fun z hz => (h z).mp hz⟩

private lemma eval_isDblBForm {m} (d a b : Fin m) (f : Fin m → M) :
    (isDblBForm d a b).eval f ↔ IsDblM (f d) (f a) (f b) := by
  simp only [isDblBForm, BForm.eval_and, BForm.eval_bAll, BForm.eval_or, BForm.eval,
    Fin.cons_zero, Fin.cons_succ]
  constructor
  · rintro ⟨⟨had, hbd⟩, h⟩ z
    exact ⟨fun hz => h z hz, fun hz => by rcases hz with rfl | rfl <;> assumption⟩
  · intro h
    exact ⟨⟨(h (f a)).mpr (Or.inl rfl), (h (f b)).mpr (Or.inr rfl)⟩, fun z hz => (h z).mp hz⟩

private def Levy.eval : ∀ {n m : ℕ}, Levy n m → (Fin m → M) → Prop
  | 0, _, b, f => BForm.eval b f
  | n + 1, m, ψ, f => ∃ u : M, ¬ Levy.eval (n := n) (m := m + 1) (Levy.unstep ψ) (Fin.cons u f)

private lemma Levy.eval_step {n m : ℕ} (ψ : Levy n (m + 1)) (f : Fin m → M) :
    Levy.eval (n := n + 1) (Levy.step ψ) f ↔ ∃ u : M, ¬ Levy.eval (n := n) ψ (Fin.cons u f) :=
  Iff.rfl

private lemma Levy.eval_unstep {n m : ℕ} (φ : Levy (n + 1) m) (f : Fin m → M) :
    Levy.eval (n := n + 1) φ f ↔ ∃ u : M, ¬ Levy.eval (n := n) (Levy.unstep φ) (Fin.cons u f) :=
  Iff.rfl

private lemma Levy.eval_lift : ∀ {n m m' : ℕ} (φ : Levy n m) (r : Fin m → Fin m') (f : Fin m' → M),
    Levy.eval (n := n) (Levy.lift (n := n) φ r) f ↔ Levy.eval (n := n) φ (f ∘ r)
  | 0, _, _, b, r, f => BForm.eval_lift b r f
  | n + 1, m, m', ψ, r, f => by
    simp only [Levy.lift, Levy.eval_unstep, Levy.unstep_step]
    refine exists_congr fun u => not_congr ?_
    have hcomp : Fin.cons u f ∘ Fin.cons 0 (Fin.succ ∘ r) = Fin.cons u (f ∘ r) := by
      ext j; refine Fin.cases rfl (fun _ => rfl) j
    rw [Levy.eval_lift (n := n) (m := m + 1) (m' := m' + 1) (Levy.unstep ψ), hcomp]

private lemma Levy.realize_toFormula : ∀ {n m : ℕ} (φ : Levy n m) (vars : Fin m → ℕ) (nxt : ℕ)
    (_hvars : ∀ i : Fin m, vars i < nxt) (env : ℕ → M),
    Formula.Realize (Levy.toFormula (n := n) φ vars nxt) env ↔ Levy.eval (n := n) φ (env ∘ vars)
  | 0, _, b, vars, nxt, hvars, env => BForm.realize_toFormula b vars nxt hvars env
  | n + 1, m, ψ, vars, nxt, hvars, env => by
    simp only [Levy.toFormula, Levy.eval_unstep, realize_ex, Formula.realize_not]
    refine exists_congr fun u => not_congr ?_
    have hvars' : ∀ j : Fin (m + 1), (Fin.cons (α := fun _ => ℕ) nxt vars) j < nxt + 1 := by
      intro j; refine Fin.cases (by simp) (fun k => Nat.lt_succ_of_lt (hvars k)) j
    rw [Levy.realize_toFormula (n := n) (m := m + 1) (Levy.unstep ψ) (Fin.cons nxt vars) (nxt + 1) hvars']
    have hcomp : Function.update env nxt u ∘ Fin.cons nxt vars = Fin.cons u (env ∘ vars) := by
      ext j; refine Fin.cases (by simp) (fun k => by
        have hnk : vars k ≠ nxt := Nat.ne_of_lt (hvars k)
        simp [Function.update_of_ne hnk]) j
    rw [hcomp]

private lemma Levy.eval_neg [Nonempty M] {n m : ℕ} (φ : Levy n m) (f : Fin m → M) :
    Levy.eval (n := n + 1) (Levy.neg φ) f ↔ ¬ Levy.eval (n := n) φ f := by
  simp only [Levy.neg, Levy.eval_step, Levy.eval_lift]
  have hcomp : ∀ u : M, Fin.cons u f ∘ Fin.succ = f := fun _ => rfl
  simp only [hcomp]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨Classical.arbitrary M, h⟩⟩

private lemma Levy.eval_ofBForm [Nonempty M] : ∀ (n : ℕ) {m : ℕ} (b : BForm m) (f : Fin m → M),
    Levy.eval (n := n) (Levy.ofBForm n b) f ↔ b.eval f
  | 0, _, _, _ => Iff.rfl
  | n + 1, _, b, f => by
    simp only [Levy.ofBForm, Levy.eval_neg, Levy.eval_ofBForm n b.not f, BForm.eval_not, not_not]

private lemma Levy.eval_raise1 [Nonempty M] : ∀ {n m : ℕ} (φ : Levy n m) (f : Fin m → M),
    Levy.eval (n := n + 1) (Levy.raise1 (n := n) φ) f ↔ Levy.eval (n := n) φ f
  | 0, _, b, f => Levy.eval_ofBForm 1 b f
  | n + 1, m, ψ, f => by
    simp only [Levy.raise1, Levy.eval_unstep, Levy.unstep_step]
    refine exists_congr fun u => not_congr (Levy.eval_raise1 (n := n) (m := m + 1) (Levy.unstep ψ) (Fin.cons u f))

private lemma Levy.eval_raiseAdd [Nonempty M] : ∀ {n m : ℕ} (d : ℕ) (φ : Levy n m) (f : Fin m → M),
    Levy.eval (n := n + d) (Levy.raiseAdd d φ) f ↔ Levy.eval (n := n) φ f
  | _, _, 0, _, _ => Iff.rfl
  | _, _, d + 1, φ, f => (Levy.eval_raise1 _ f).trans (Levy.eval_raiseAdd d φ f)

private lemma Levy.eval_castN {n₁ n₂ m : ℕ} (h : n₁ = n₂) (φ : Levy n₁ m) (f : Fin m → M) :
    Levy.eval (n := n₂) (Levy.castN h φ) f ↔ Levy.eval (n := n₁) φ f := by
  subst h; rfl

private lemma Levy.eval_raiseLe [Nonempty M] {n₁ n₂ m : ℕ} (h : n₁ ≤ n₂) (φ : Levy n₁ m) (f : Fin m → M) :
    Levy.eval (n := n₂) (Levy.raiseLe h φ) f ↔ Levy.eval (n := n₁) φ f :=
  (Levy.eval_castN _ _ f).trans (Levy.eval_raiseAdd _ φ f)

private lemma realize_termIdx {m l : ℕ} (t : setLang.Term (ℕ ⊕ Fin l))
    (ht : ∀ a ∈ t.varFinsetLeft, a < m) (v : ℕ → M) (xs : Fin l → M) :
    Fin.append (fun i : Fin m => v i.1) xs (termIdx t ht) = t.realize (Sum.elim v xs) := by
  cases t with
  | var x =>
    cases x with
    | inl a =>
      have ha : a < m := ht a (by simp [Term.varFinsetLeft])
      have h : termIdx (.var (.inl a)) ht = Fin.castAdd l ⟨a, ha⟩ := rfl
      rw [h, Fin.append_left]; rfl
    | inr j =>
      have h : termIdx (.var (.inr j)) ht = Fin.natAdd m j := rfl
      rw [h, Fin.append_right]; rfl
  | func f _ => exact Empty.elim f

private structure LevyOps (n : ℕ) where
  or : ∀ {m}, Levy n m → Levy n m → Levy n m
  and : ∀ {m}, Levy n m → Levy n m → Levy n m
  bEx : ∀ {m}, Fin m → Levy n (m + 1) → Levy n m
  bAll : ∀ {m}, Fin m → Levy n (m + 1) → Levy n m
  eval_or : ∀ {m} (φ ψ : Levy n m) (f : Fin m → M),
    Levy.eval (n := n) (or φ ψ) f ↔ Levy.eval (n := n) φ f ∨ Levy.eval (n := n) ψ f
  eval_and : ∀ {m} (φ ψ : Levy n m) (f : Fin m → M),
    Levy.eval (n := n) (and φ ψ) f ↔ Levy.eval (n := n) φ f ∧ Levy.eval (n := n) ψ f
  eval_bEx : ∀ {m} (i : Fin m) (φ : Levy n (m + 1)) (f : Fin m → M),
    Levy.eval (n := n) (bEx i φ) f ↔ ∃ w : M, MemRelM w (f i) ∧ Levy.eval (n := n) φ (Fin.cons w f)
  eval_bAll : ∀ {m} (i : Fin m) (φ : Levy n (m + 1)) (f : Fin m → M),
    Levy.eval (n := n) (bAll i φ) f ↔ ∀ w : M, MemRelM w (f i) → Levy.eval (n := n) φ (Fin.cons w f)

noncomputable section ZFjPart

variable (hM : M ⊨ ZFj)
include hM

private lemma eval_isPairBForm (f : Fin 3 → M) :
    isPairBForm.eval f ↔ IsPairM (f 0) (f 1) (f 2) := by
  simp only [isPairBForm, BForm.eval_and, BForm.eval_bAll, BForm.eval_or, BForm.eval,
    eval_isSingBForm, eval_isDblBForm, Fin.cons_zero]
  constructor
  · rintro ⟨⟨⟨s, hsp, hs⟩, ⟨d, hdp, hd⟩⟩, hall⟩ w
    refine ⟨hall w, ?_⟩
    rintro (hws | hwd)
    · rwa [sing_uniq hM hws hs]
    · rwa [ax_ext hM w d fun z => (hwd z).trans (hd z).symm]
  · intro hp
    obtain ⟨s, hs⟩ := sing_ex hM (f 1)
    obtain ⟨d, hd⟩ := ax_pair hM (f 1) (f 2)
    exact ⟨⟨⟨s, (hp s).mpr (Or.inl hs), hs⟩, ⟨d, (hp d).mpr (Or.inr hd), hd⟩⟩,
      fun w hw => (hp w).mp hw⟩

/-! Tuples, Cartesian powers, adjacent swaps, and Gödel truth sets `evalSet` -/

private def nTuple : ∀ {k : ℕ}, (Fin k → M) → M → M
  | 0, _, r => r
  | _ + 1, f, r => pair hM (f 0) (nTuple (f ∘ Fin.succ) r)

private lemma nTuple_inj : ∀ {k : ℕ} {f₁ f₂ : Fin k → M} {r₁ r₂ : M},
    nTuple hM f₁ r₁ = nTuple hM f₂ r₂ → f₁ = f₂ ∧ r₁ = r₂
  | 0, f₁, f₂, r₁, r₂, h => ⟨funext fun i => Fin.elim0 i, h⟩
  | _ + 1, f₁, f₂, r₁, r₂, h => by
    obtain ⟨h0, htail⟩ := (pair_eq_iff hM).mp h
    obtain ⟨hft, hr⟩ := nTuple_inj htail
    refine ⟨funext fun i => Fin.cases h0 (fun j => congrFun hft j) i, hr⟩

private lemma k_nTuple (k : M → M) (hk : IsGodelCofinalEmb k) :
    ∀ {n : ℕ} (f : Fin n → M) (r : M), k (nTuple hM f r) = nTuple hM (k ∘ f) (k r)
  | 0, _, _ => rfl
  | _ + 1, f, r => by
    simp only [nTuple, k_pair hM k hk, Function.comp_apply]
    rw [k_nTuple k hk (f ∘ Fin.succ) r]
    rfl

section ZFjNonempty

variable [Nonempty M]

private def tuple {m : ℕ} (f : Fin m → M) : M := nTuple hM f (emp hM)

private def powT (T : M) : ℕ → M
  | 0 => sing hM (emp hM)
  | m + 1 => prod hM T (powT T m)

private lemma tuple_inj {m : ℕ} {f₁ f₂ : Fin m → M} (h : tuple hM f₁ = tuple hM f₂) : f₁ = f₂ :=
  (nTuple_inj hM h).1

private lemma mem_powT_iff (T : M) :
    ∀ {m : ℕ} {z : M}, MemRelM z (powT hM T m) ↔
      ∃ f : Fin m → M, (∀ i : Fin m, MemRelM (f i) T) ∧ z = tuple hM f
  | 0, z => by
    rw [powT, sing_spec hM]
    simp only [tuple, nTuple]
    constructor
    · rintro rfl; exact ⟨Fin.elim0, fun i => Fin.elim0 i, rfl⟩
    · rintro ⟨_, _, rfl⟩; rfl
  | m + 1, z => by
    rw [powT, mem_prod_iff hM]
    constructor
    · rintro ⟨a, b, ha, hb, rfl⟩
      obtain ⟨g, hg, rfl⟩ := (mem_powT_iff T).mp hb
      refine ⟨Fin.cons a g, fun i => Fin.cases ha hg i, ?_⟩
      simp [tuple, nTuple]
    · rintro ⟨f, hf, rfl⟩
      refine ⟨f 0, tuple hM (f ∘ Fin.succ), hf 0,
        (mem_powT_iff T).mpr ⟨f ∘ Fin.succ, fun j => hf j.succ, rfl⟩, rfl⟩

private lemma k_tuple (k : M → M) (hk : IsGodelCofinalEmb k) {m : ℕ} (f : Fin m → M) :
    k (tuple hM f) = tuple hM (k ∘ f) := by
  simp only [tuple, k_nTuple hM k hk, k_emp hM k hk]

private lemma k_powT (k : M → M) (hk : IsGodelCofinalEmb k) (T : M) :
    ∀ m : ℕ, k (powT hM T m) = powT hM (k T) m
  | 0 => by simp [powT, k_sing hM k hk, k_emp hM k hk]
  | m + 1 => by simp [powT, k_prod hM k hk, k_powT k hk T m]

private def swapAdj : ℕ → M → M
  | 0, S => shift hM S
  | 1, S => innerShift hM S
  | j + 2, S => push hM (swapAdj (j + 1) (pull hM S))

private lemma k_swapAdj (k : M → M) (hk : IsGodelCofinalEmb k) :
    ∀ (i : ℕ) (S : M), k (swapAdj hM i S) = swapAdj hM i (k S)
  | 0, S => k_shift hM k hk S
  | 1, S => k_innerShift hM k hk S
  | j + 2, S => by
    simp only [swapAdj, k_push hM k hk, k_swapAdj k hk (j + 1), k_pull hM k hk]

private lemma swapAdj_spec :
    ∀ (i : ℕ) (S : M),
      (∀ z : M, MemRelM z S → ∃ (f : Fin (i + 2) → M) (r : M), z = nTuple hM f r) →
      (∀ z : M, MemRelM z (swapAdj hM i S) → ∃ (f : Fin (i + 2) → M) (r : M), z = nTuple hM f r) ∧
      (∀ (f : Fin (i + 2) → M) (r : M),
        MemRelM (nTuple hM f r) (swapAdj hM i S) ↔
          MemRelM (nTuple hM (f ∘ swapLast i) r) S)
  | 0, S, _ => by
    refine ⟨fun z hz => ?_, fun f r => ?_⟩
    · obtain ⟨a, b, c, rfl, _⟩ := (mem_shift_iff hM).mp hz
      exact ⟨![b, a], c, rfl⟩
    · rw [swapAdj, mem_shift_iff hM]
      constructor
      · rintro ⟨a, b, c, heq, hmem⟩
        obtain ⟨hb, h12⟩ := (pair_eq_iff hM).mp heq
        obtain ⟨ha, hc⟩ := (pair_eq_iff hM).mp h12
        subst hb ha hc
        have hsw : nTuple hM (f ∘ swapLast 0) r = pair hM (f 1) (pair hM (f 0) r) := by
          simp [nTuple, swapLast]
        rwa [hsw]
      · intro hmem
        refine ⟨f 1, f 0, r, rfl, ?_⟩
        have hsw : nTuple hM (f ∘ swapLast 0) r = pair hM (f 1) (pair hM (f 0) r) := by
          simp [nTuple, swapLast]
        rwa [← hsw]
  | 1, S, _ => by
    refine ⟨fun z hz => ?_, fun f r => ?_⟩
    · obtain ⟨d, a, b, c, rfl, _⟩ := (mem_innerShift_iff hM).mp hz
      exact ⟨![d, b, a], c, rfl⟩
    · rw [swapAdj, mem_innerShift_iff hM]
      constructor
      · rintro ⟨d, a, b, c, heq, hmem⟩
        obtain ⟨hd, h12⟩ := (pair_eq_iff hM).mp heq
        obtain ⟨hb, h23⟩ := (pair_eq_iff hM).mp h12
        obtain ⟨ha, hc⟩ := (pair_eq_iff hM).mp h23
        subst hd hb ha hc
        have hsw : nTuple hM (f ∘ swapLast 1) r = pair hM (f 0) (pair hM (f 2) (pair hM (f 1) r)) := by
          simp [nTuple, swapLast]
        rwa [hsw]
      · intro hmem
        refine ⟨f 0, f 2, f 1, r, rfl, ?_⟩
        have hsw : nTuple hM (f ∘ swapLast 1) r = pair hM (f 0) (pair hM (f 2) (pair hM (f 1) r)) := by
          simp [nTuple, swapLast]
        rwa [← hsw]
  | j + 2, S, hS => by
    let pack : (Fin (j + 4) → M) → Fin (j + 3) → M :=
      fun f => Fin.cons (pair hM (f 0) (f 1)) (fun t => f ⟨t.1 + 2, by omega⟩)
    have hpack_ntuple : ∀ (f : Fin (j + 4) → M) (r : M),
        nTuple hM (pack f) r = pair hM (pair hM (f 0) (f 1)) (nTuple hM (fun t : Fin (j + 2) => f ⟨t.1 + 2, by omega⟩) r) := by
      intro f r; rfl
    have hntuple_split : ∀ (f : Fin (j + 4) → M) (r : M),
        nTuple hM f r = pair hM (f 0) (pair hM (f 1) (nTuple hM (fun t : Fin (j + 2) => f ⟨t.1 + 2, by omega⟩) r)) := by
      intro f r; rfl
    have hpull_shape : ∀ z : M, MemRelM z (pull hM S) →
        ∃ (g : Fin (j + 3) → M) (r : M), z = nTuple hM g r := by
      intro z hz
      obtain ⟨a, b, c, rfl, hmem⟩ := (mem_pull_iff hM).mp hz
      obtain ⟨f, r, hfeq⟩ := hS _ hmem
      rw [hntuple_split] at hfeq
      obtain ⟨ha, hbc⟩ := (pair_eq_iff hM).mp hfeq
      obtain ⟨hb, hc⟩ := (pair_eq_iff hM).mp hbc
      refine ⟨pack f, r, ?_⟩
      rw [hpack_ntuple, ← ha, ← hb, ← hc]
    have hpull_mem : ∀ (f : Fin (j + 4) → M) (r : M),
        MemRelM (nTuple hM (pack f) r) (pull hM S) ↔ MemRelM (nTuple hM f r) S := by
      intro f r
      rw [mem_pull_iff hM]
      constructor
      · rintro ⟨a, b, c, heq, hmem⟩
        rw [hpack_ntuple] at heq
        obtain ⟨hab, hc⟩ := (pair_eq_iff hM).mp heq
        obtain ⟨ha, hb⟩ := (pair_eq_iff hM).mp hab
        rw [hntuple_split, ha, hb, hc]
        exact hmem
      · intro hmem
        exact ⟨f 0, f 1, nTuple hM (fun t : Fin (j + 2) => f ⟨t.1 + 2, by omega⟩) r, rfl, hmem⟩
    have hpack_swap : ∀ (f : Fin (j + 4) → M),
        pack (f ∘ swapLast (j + 2)) = pack f ∘ swapLast (j + 1) := by
      intro f
      ext ⟨t, ht⟩
      cases t with
      | zero =>
        simp [pack, swapLast]
      | succ t' =>
        by_cases h1 : t' = j
        · subst h1; simp [pack, swapLast, Fin.cons]
        · by_cases h2 : t' = j + 1
          · subst h2; simp [pack, swapLast, Fin.cons]
          · simp [pack, swapLast, Fin.cons, h1, h2]
    have hih := swapAdj_spec (j + 1) (pull hM S) hpull_shape
    refine ⟨fun z hz => ?_, fun f r => ?_⟩
    · obtain ⟨a, b, c, rfl, hmem⟩ := (mem_push_iff hM).mp hz
      obtain ⟨g, r, hgeq⟩ := hih.1 _ hmem
      obtain ⟨_, htail⟩ := (pair_eq_iff hM).mp hgeq
      let f' : Fin (j + 4) → M := Fin.cons a (Fin.cons b (g ∘ Fin.succ))
      refine ⟨f', r, ?_⟩
      rw [hntuple_split]
      have htail' : (fun t : Fin (j + 2) => f' ⟨t.1 + 2, by omega⟩) = g ∘ Fin.succ := by
        ext ⟨t, ht⟩; rfl
      rw [htail', ← htail]; rfl
    · rw [swapAdj, mem_push_iff hM]
      constructor
      · rintro ⟨a, b, c, heq, hmem⟩
        rw [hntuple_split] at heq
        obtain ⟨ha, hbc⟩ := (pair_eq_iff hM).mp heq
        obtain ⟨hb, hc⟩ := (pair_eq_iff hM).mp hbc
        have heq_pack : pair hM (pair hM a b) c = nTuple hM (pack f) r := by
          rw [hpack_ntuple, ha, hb, hc]
        rw [heq_pack, hih.2, ← hpack_swap, hpull_mem] at hmem
        exact hmem
      · intro hmem
        refine ⟨f 0, f 1, nTuple hM (fun t : Fin (j + 2) => f ⟨t.1 + 2, by omega⟩) r, rfl, ?_⟩
        change MemRelM (nTuple hM (pack f) r) (swapAdj hM (j + 1) (pull hM S))
        rw [hih.2, ← hpack_swap, hpull_mem]
        exact hmem

private lemma tuple_congr_len {a b : ℕ} (h : a = b) (f : Fin a → M) (g : Fin b → M)
    (hfg : ∀ i : ℕ, (ha : i < a) → (hb : i < b) → f ⟨i, ha⟩ = g ⟨i, hb⟩) :
    tuple hM f = tuple hM g := by
  subst h
  congr 1
  ext ⟨i, hi⟩
  exact hfg i hi hi

private lemma tuple_eq_nTuple_split {m : ℕ} (k : ℕ) (hk : k ≤ m) (f : Fin m → M) :
    tuple hM f =
      nTuple hM (fun t : Fin k => f ⟨t.1, by omega⟩)
        (tuple hM (fun t : Fin (m - k) => f ⟨t.1 + k, by omega⟩)) := by
  induction k generalizing m with
  | zero =>
    simp [nTuple, tuple]
  | succ k ih =>
    cases m with
    | zero => omega
    | succ m' =>
      have hk' : k ≤ m' := by omega
      simp only [tuple, nTuple]
      congr 1
      have hih := ih hk' (f ∘ Fin.succ)
      rw [tuple] at hih
      rw [hih]
      have h1 : (fun t : Fin k => (f ∘ Fin.succ) ⟨t.1, by omega⟩) =
          ((fun t : Fin (k + 1) => f ⟨t.1, by omega⟩) ∘ Fin.succ) := by
        ext t; rfl
      have h2 : tuple hM (fun t : Fin (m' - k) => (f ∘ Fin.succ) ⟨t.1 + k, by omega⟩) =
          tuple hM (fun t : Fin (m' + 1 - (k + 1)) => f ⟨t.1 + (k + 1), by omega⟩) :=
        tuple_congr_len hM (Nat.succ_sub_succ_eq_sub m' k).symm _ _ fun _ _ _ => rfl
      rw [← h1]
      exact congrArg (nTuple hM _) h2

private lemma swapAdj_powT_spec (T : M) {m : ℕ} (idx : ℕ) (hidx : idx + 1 < m) (S : M)
    (hS : ∀ z : M, MemRelM z S → MemRelM z (powT hM T m)) :
    (∀ z : M, MemRelM z (swapAdj hM idx S) → MemRelM z (powT hM T m)) ∧
    (∀ f : Fin m → M,
      MemRelM (tuple hM f) (swapAdj hM idx S) ↔
        MemRelM (tuple hM (f ∘ swapAt idx hidx)) S) := by
  have hshape : ∀ z : M, MemRelM z S →
      ∃ (g : Fin (idx + 2) → M) (r : M), z = nTuple hM g r := by
    intro z hz
    obtain ⟨f, _, rfl⟩ := (mem_powT_iff hM T).mp (hS z hz)
    exact ⟨fun t => f ⟨t.1, by omega⟩,
      tuple hM (fun t : Fin (m - (idx + 2)) => f ⟨t.1 + (idx + 2), by omega⟩),
      tuple_eq_nTuple_split hM (idx + 2) (by omega) f⟩
  have hsp := swapAdj_spec hM idx S hshape
  have hiff : ∀ f : Fin m → M,
      MemRelM (tuple hM f) (swapAdj hM idx S) ↔
        MemRelM (tuple hM (f ∘ swapAt idx hidx)) S := by
    intro f
    rw [tuple_eq_nTuple_split hM (idx + 2) (by omega) f, hsp.2]
    have heq : nTuple hM ((fun t : Fin (idx + 2) => f ⟨t.1, by omega⟩) ∘ swapLast idx)
        (tuple hM (fun t : Fin (m - (idx + 2)) => f ⟨t.1 + (idx + 2), by omega⟩)) =
        tuple hM (f ∘ swapAt idx hidx) := by
      rw [tuple_eq_nTuple_split hM (idx + 2) (by omega) (f ∘ swapAt idx hidx)]
      congr 1
      · ext ⟨t, ht⟩; simp only [Function.comp_apply, swapLast, swapAt]; split_ifs <;> rfl
      · congr 1; ext ⟨t, ht⟩
        have h1 : t + (idx + 2) ≠ idx := by omega
        have h2 : t + (idx + 2) ≠ idx + 1 := by omega
        simp [Function.comp_apply, swapAt, h1, h2]
    rw [heq]
  refine ⟨fun z hz => ?_, hiff⟩
  obtain ⟨g, r, rfl⟩ := hsp.1 z hz
  have hmemS : MemRelM (nTuple hM (g ∘ swapLast idx) r) S := (hsp.2 g r).mp hz
  obtain ⟨f, hfT, hfeq⟩ := (mem_powT_iff hM T).mp (hS _ hmemS)
  rw [tuple_eq_nTuple_split hM (idx + 2) (by omega) f] at hfeq
  obtain ⟨hgf, hrf⟩ := nTuple_inj hM hfeq
  have hg_eq : g = (fun t : Fin (idx + 2) => (f ∘ swapAt idx hidx) ⟨t.1, by omega⟩) := by
    ext ⟨t, ht⟩
    have h1 := congrFun hgf (swapLast idx ⟨t, ht⟩)
    simp only [Function.comp_apply, swapLast_invol] at h1
    rw [h1]
    simp only [Function.comp_apply, swapLast, swapAt]
    split_ifs <;> rfl
  have hz_eq : nTuple hM g r = tuple hM (f ∘ swapAt idx hidx) := by
    rw [hg_eq, hrf, tuple_eq_nTuple_split hM (idx + 2) (by omega) (f ∘ swapAt idx hidx)]
    congr 2; ext ⟨t, ht⟩
    have h1 : t + (idx + 2) ≠ idx := by omega
    have h2 : t + (idx + 2) ≠ idx + 1 := by omega
    simp [Function.comp_apply, swapAt, h1, h2]
  rw [hz_eq]
  exact (mem_powT_iff hM T).mpr ⟨f ∘ swapAt idx hidx, fun i => hfT _, rfl⟩

private def applySwaps {m : ℕ} : List { idx : ℕ // idx + 1 < m } → M → M
  | [], S => S
  | a :: l, S => swapAdj hM a.1 (applySwaps l S)

private lemma k_applySwaps (k : M → M) (hk : IsGodelCofinalEmb k) {m : ℕ} :
    ∀ (l : List { idx : ℕ // idx + 1 < m }) (S : M),
      k (applySwaps hM l S) = applySwaps hM l (k S)
  | [], _ => rfl
  | a :: l, S => by
    simp only [applySwaps, k_swapAdj hM k hk, k_applySwaps k hk l S]

private lemma applySwaps_powT_spec (T : M) {m : ℕ} :
    ∀ (l : List { idx : ℕ // idx + 1 < m }) (S : M),
      (∀ z : M, MemRelM z S → MemRelM z (powT hM T m)) →
      (∀ z : M, MemRelM z (applySwaps hM l S) → MemRelM z (powT hM T m)) ∧
      (∀ f : Fin m → M,
        MemRelM (tuple hM f) (applySwaps hM l S) ↔
          MemRelM (tuple hM (f ∘ permOfSwaps l)) S)
  | [], S, hS => ⟨hS, fun _ => Iff.rfl⟩
  | a :: l, S, hS => by
    have ih := applySwaps_powT_spec T l S hS
    have hsp := swapAdj_powT_spec hM T a.1 a.2 (applySwaps hM l S) ih.1
    refine ⟨hsp.1, fun f => ?_⟩
    rw [applySwaps, hsp.2, ih.2]
    rfl

private lemma push_prod_powT_spec (T R : M) {m : ℕ} (hm : 2 ≤ m)
    (hR : ∀ z : M, MemRelM z R → ∃ a b : M, MemRelM a T ∧ MemRelM b T ∧ z = pair hM a b) :
    (∀ z : M, MemRelM z (push hM (prod hM R (powT hM T (m - 2)))) → MemRelM z (powT hM T m)) ∧
    (∀ f : Fin m → M, (∀ t : Fin m, MemRelM (f t) T) →
      (MemRelM (tuple hM f) (push hM (prod hM R (powT hM T (m - 2)))) ↔
        MemRelM (pair hM (f ⟨0, by omega⟩) (f ⟨1, by omega⟩)) R)) := by
  have hm2 : 2 ≤ m := hm
  refine ⟨fun z hz => ?_, fun f hfT => ?_⟩
  · obtain ⟨a, b, c, rfl, hmem⟩ := (mem_push_iff hM).mp hz
    obtain ⟨ab, c', habR, hc', heq⟩ := (mem_prod_iff hM).mp hmem
    obtain ⟨habEq, hcEq⟩ := (pair_eq_iff hM).mp heq
    subst hcEq
    obtain ⟨a', b', ha'T, hb'T, hab'⟩ := hR ab habR
    have habEq' := habEq.trans hab'
    obtain ⟨haEq, hbEq⟩ := (pair_eq_iff hM).mp habEq'
    subst haEq hbEq
    obtain ⟨g, hgT, rfl⟩ := (mem_powT_iff hM T).mp hc'
    let f : Fin m → M := fun t =>
      if h0 : t.1 = 0 then a
      else if h1 : t.1 = 1 then b
      else g ⟨t.1 - 2, by omega⟩
    have hfT : ∀ t : Fin m, MemRelM (f t) T := by
      intro t; dsimp [f]; split_ifs
      · exact ha'T
      · exact hb'T
      · exact hgT _
    have hfeq : tuple hM f = pair hM a (pair hM b (tuple hM g)) := by
      rw [tuple_eq_nTuple_split hM 2 hm2 f]
      simp only [nTuple]
      refine congrArg₂ (pair hM) (by simp [f]) (congrArg₂ (pair hM) (by simp [f]) (congrArg (tuple hM) ?_))
      ext ⟨t, ht⟩; simp [f]
    exact (mem_powT_iff hM T).mpr ⟨f, hfT, hfeq.symm⟩
  · rw [mem_push_iff hM]
    rw [tuple_eq_nTuple_split hM 2 hm2 f]
    simp only [nTuple]
    constructor
    · rintro ⟨a, b, c, heq, hmem⟩
      obtain ⟨ha, hbc⟩ := (pair_eq_iff hM).mp heq
      obtain ⟨hb, _⟩ := (pair_eq_iff hM).mp hbc
      obtain ⟨ab, c', habR, _, heq2⟩ := (mem_prod_iff hM).mp hmem
      obtain ⟨habEq, _⟩ := (pair_eq_iff hM).mp heq2
      have ha' : f ⟨0, by omega⟩ = a := ha
      have hb' : f ⟨1, by omega⟩ = b := hb
      rw [ha', hb', habEq]
      exact habR
    · intro hRmem
      refine ⟨f ⟨0, by omega⟩, f ⟨1, by omega⟩,
        tuple hM (fun t : Fin (m - 2) => f ⟨t.1 + 2, by omega⟩), rfl, ?_⟩
      exact (mem_prod_iff hM).mpr ⟨pair hM (f ⟨0, by omega⟩) (f ⟨1, by omega⟩),
        tuple hM (fun t : Fin (m - 2) => f ⟨t.1 + 2, by omega⟩),
        hRmem, (mem_powT_iff hM T).mpr ⟨fun t => f ⟨t.1 + 2, by omega⟩, fun t => hfT _, rfl⟩, rfl⟩

private def evalMem (T : M) {m : ℕ} (i j : Fin m) : M :=
  if h : i = j then emp hM
  else applySwaps hM (swapsFor i j h) (push hM (prod hM (memGraph hM T) (powT hM T (m - 2))))

private lemma k_evalMem (k : M → M) (hk : IsGodelCofinalEmb k) (T : M)
    {m : ℕ} (i j : Fin m) : k (evalMem hM T i j) = evalMem hM (k T) i j := by
  simp only [evalMem]
  split_ifs
  · exact k_emp hM k hk
  · rw [k_applySwaps hM k hk, k_push hM k hk, k_prod hM k hk,
      k_memGraph hM k hk, k_powT hM k hk]

private lemma evalMem_spec (T : M) {m : ℕ} (i j : Fin m) :
    (∀ z : M, MemRelM z (evalMem hM T i j) → MemRelM z (powT hM T m)) ∧
    (∀ f : Fin m → M, (∀ t : Fin m, MemRelM (f t) T) →
      (MemRelM (tuple hM f) (evalMem hM T i j) ↔ MemRelM (f i) (f j))) := by
  by_cases h : i = j
  · subst h
    simp only [evalMem, ↓reduceDIte]
    exact ⟨fun z hz => absurd hz (emp_spec hM z),
      fun f _ => ⟨fun hz => absurd hz (emp_spec hM _), fun hm => absurd hm (mem_irrefl hM _)⟩⟩
  · simp only [evalMem, h, ↓reduceDIte]
    have hm2 : 2 ≤ m := by
      have hne : i.1 ≠ j.1 := fun heq => h (Fin.ext heq)
      omega
    have hbase := push_prod_powT_spec hM T (memGraph hM T) hm2 (fun z hz => by
      obtain ⟨a, b, ha, hb, _, rfl⟩ := (mem_memGraph_iff hM).mp hz
      exact ⟨a, b, ha, hb, rfl⟩)
    have hsw := applySwaps_powT_spec hM T (swapsFor i j h) _ hbase.1
    have hperm := permOfSwaps_swapsFor i j h
    refine ⟨hsw.1, fun f hfT => ?_⟩
    rw [hsw.2, hbase.2 (f ∘ permOfSwaps (swapsFor i j h)) (fun t => hfT _)]
    simp only [Function.comp_apply, hperm.1, hperm.2, mem_memGraph_iff hM]
    constructor
    · rintro ⟨a, b, _, _, hab, heq⟩
      obtain ⟨h1, h2⟩ := (pair_eq_iff hM).mp heq
      rwa [h1, h2]
    · intro hab; exact ⟨f i, f j, hfT i, hfT j, hab, rfl⟩

private def evalSet (T : M) : ∀ {m : ℕ}, BForm m → M
  | _, .falsum => emp hM
  | m, .eq i j =>
    if h : i = j then powT hM T m
    else applySwaps hM (swapsFor i j h) (push hM (prod hM (eqGraph hM T) (powT hM T (m - 2))))
  | _, .mem i j => evalMem hM T i j
  | m, .imp φ ψ => diff hM (powT hM T m) (diff hM (evalSet T φ) (evalSet T ψ))
  | _, .bEx i φ =>
    dom hM (swap hM (diff hM (evalSet T φ) (diff hM (evalSet T φ) (evalMem hM T 0 i.succ))))

private lemma k_evalSet (k : M → M) (hk : IsGodelCofinalEmb k) (T : M) :
    ∀ {m : ℕ} (φ : BForm m), k (evalSet hM T φ) = evalSet hM (k T) φ
  | _, .falsum => k_emp hM k hk
  | m, .eq i j => by
    simp only [evalSet]
    split_ifs
    · exact k_powT hM k hk T m
    · rw [k_applySwaps hM k hk, k_push hM k hk, k_prod hM k hk,
        k_eqGraph hM k hk, k_powT hM k hk]
  | _, .mem i j => k_evalMem hM k hk T i j
  | m, .imp φ ψ => by
    simp only [evalSet, k_diff hM k hk, k_powT hM k hk, k_evalSet k hk T φ, k_evalSet k hk T ψ]
  | _, .bEx i φ => by
    simp only [evalSet, k_dom hM k hk, k_swap hM k hk, k_diff hM k hk,
      k_evalSet k hk T φ, k_evalMem hM k hk T 0 i.succ]

private lemma evalSet_spec (T : M) (hT : Trans T) :
    ∀ {m : ℕ} (φ : BForm m),
      (∀ z : M, MemRelM z (evalSet hM T φ) → MemRelM z (powT hM T m)) ∧
      (∀ f : Fin m → M, (∀ t : Fin m, MemRelM (f t) T) →
        (MemRelM (tuple hM f) (evalSet hM T φ) ↔ φ.eval f))
  | _, .falsum => ⟨fun z hz => absurd hz (emp_spec hM z),
      fun _ _ => ⟨fun hz => absurd hz (emp_spec hM _), False.elim⟩⟩
  | m, .eq i j => by
    by_cases h : i = j
    · subst h
      simp only [evalSet, ↓reduceDIte, BForm.eval, iff_true]
      exact ⟨fun _ hz => hz, fun f hfT => (mem_powT_iff hM T).mpr ⟨f, hfT, rfl⟩⟩
    · simp only [evalSet, h, ↓reduceDIte, BForm.eval]
      have hm2 : 2 ≤ m := by
        have hne : i.1 ≠ j.1 := fun heq => h (Fin.ext heq)
        omega
      have hbase := push_prod_powT_spec hM T (eqGraph hM T) hm2 (fun z hz => by
        obtain ⟨a, ha, rfl⟩ := (mem_eqGraph_iff hM).mp hz
        exact ⟨a, a, ha, ha, rfl⟩)
      have hsw := applySwaps_powT_spec hM T (swapsFor i j h) _ hbase.1
      have hperm := permOfSwaps_swapsFor i j h
      refine ⟨hsw.1, fun f hfT => ?_⟩
      rw [hsw.2, hbase.2 (f ∘ permOfSwaps (swapsFor i j h)) (fun t => hfT _)]
      simp only [Function.comp_apply, hperm.1, hperm.2, mem_eqGraph_iff hM]
      constructor
      · rintro ⟨a, _, heq⟩
        obtain ⟨h1, h2⟩ := (pair_eq_iff hM).mp heq
        exact h1.trans h2.symm
      · intro heq; exact ⟨f i, hfT i, by rw [heq]⟩
  | _, .mem i j => evalMem_spec hM T i j
  | m, .imp φ ψ => by
    have ih1 := evalSet_spec T hT φ
    have ih2 := evalSet_spec T hT ψ
    refine ⟨fun z hz => ((diff_spec hM _ _ z).mp hz).1, fun f hfT => ?_⟩
    simp only [evalSet, BForm.eval]
    rw [diff_spec hM, diff_spec hM, ih1.2 f hfT, ih2.2 f hfT]
    have hpow : MemRelM (tuple hM f) (powT hM T m) := (mem_powT_iff hM T).mpr ⟨f, hfT, rfl⟩
    tauto
  | m, .bEx i φ => by
    have ihφ := evalSet_spec T hT φ
    have ihM := evalMem_spec hM T (0 : Fin (m + 1)) i.succ
    refine ⟨fun z hz => ?_, fun f hfT => ?_⟩
    · obtain ⟨w, hws⟩ := (mem_dom_iff hM).mp hz
      obtain ⟨a, b, heq, hab⟩ := (mem_swap_iff hM).mp hws
      obtain ⟨hzb, _⟩ := (pair_eq_iff hM).mp heq
      have hpow := ihφ.1 _ ((diff_spec hM _ _ _).mp hab).1
      obtain ⟨g, hgT, hgeq⟩ := (mem_powT_iff hM T).mp hpow
      obtain ⟨_, hbg⟩ := (pair_eq_iff hM).mp hgeq
      rw [hzb, hbg]
      exact (mem_powT_iff hM T).mpr ⟨g ∘ Fin.succ, fun t => hgT t.succ, rfl⟩
    · simp only [evalSet, mem_dom_iff hM, mem_swap_iff hM, BForm.eval]
      constructor
      · rintro ⟨w, a, b, heq, hab⟩
        obtain ⟨hfb, hwa⟩ := (pair_eq_iff hM).mp heq
        subst hwa
        have h1 : MemRelM (pair hM w (tuple hM f)) (evalSet hM T φ) := by
          rw [hfb]; exact ((diff_spec hM _ _ _).mp hab).1
        have h2 : MemRelM (pair hM w (tuple hM f)) (evalMem hM T 0 i.succ) := by
          rw [hfb]
          have hnot := ((diff_spec hM _ _ _).mp hab).2
          by_contra hnm
          exact hnot ((diff_spec hM _ _ _).mpr ⟨((diff_spec hM _ _ _).mp hab).1, hnm⟩)
        have hpow := ihφ.1 _ h1
        obtain ⟨g, hgT, hgeq⟩ := (mem_powT_iff hM T).mp hpow
        have hg_eq : g = Fin.cons w f := tuple_inj hM hgeq.symm
        subst hg_eq
        have hmem := (ihM.2 _ hgT).mp h2
        have hφ := (ihφ.2 _ hgT).mp h1
        exact ⟨w, hmem, hφ⟩
      · rintro ⟨w, hwi, hφ⟩
        have hwT : MemRelM w T := hT (f i) (hfT i) w hwi
        have hf'T : ∀ t : Fin (m + 1), MemRelM (Fin.cons (α := fun _ => M) w f t) T :=
          fun t => Fin.cases hwT hfT t
        have h1 : MemRelM (tuple hM (Fin.cons w f)) (evalSet hM T φ) := (ihφ.2 _ hf'T).mpr hφ
        have h2 : MemRelM (tuple hM (Fin.cons w f)) (evalMem hM T 0 i.succ) :=
          (ihM.2 _ hf'T).mpr hwi
        refine ⟨w, w, tuple hM f, rfl, (diff_spec hM _ _ _).mpr ⟨h1, fun hd => ?_⟩⟩
        exact ((diff_spec hM _ _ _).mp hd).2 h2

private lemma bForm_pres (k : M → M) (hk : IsGodelCofinalEmb k) {m : ℕ} (φ : BForm m)
    (f : Fin m → M) : φ.eval f ↔ φ.eval (k ∘ f) := by
  obtain ⟨T, hT, hfT⟩ := exists_transitive_superset_fin hM f
  have hkT : Trans (k T) := k_trans hM k hk hT
  have hkfT : ∀ i : Fin m, MemRelM (k (f i)) (k T) := fun i => (hk.pres_mem _ _).mp (hfT i)
  rw [← (evalSet_spec hM T hT φ).2 f hfT,
      ← (evalSet_spec hM (k T) hkT φ).2 (k ∘ f) hkfT,
      hk.pres_mem, k_tuple hM k hk, k_evalSet hM k hk]

/-! Simultaneous closure of `Levy n` under `or`, `and`, `bEx`, `bAll`, and `ex` (for `n + 1`) -/

private def levyOps : ∀ n : ℕ, LevyOps (M := M) n
  | 0 =>
    { or := BForm.or
      and := BForm.and
      bEx := BForm.bEx
      bAll := BForm.bAll
      eval_or := BForm.eval_or
      eval_and := BForm.eval_and
      eval_bEx := fun _ _ _ => Iff.rfl
      eval_bAll := BForm.eval_bAll }
  | n + 1 =>
    let prev := levyOps n
    let or' : ∀ {m}, Levy (n + 1) m → Levy (n + 1) m → Levy (n + 1) m :=
      fun φ ψ => Levy.step (prev.and (Levy.unstep φ) (Levy.unstep ψ))
    let bEx' : ∀ {m}, Fin m → Levy (n + 1) (m + 1) → Levy (n + 1) m :=
      fun {m} i φ => Levy.step (prev.bAll i.succ
        (Levy.lift (n := n) (m := m + 2) (m' := m + 2) (Levy.unstep φ) swap01))
    let bAll' : ∀ {m}, Fin m → Levy (n + 1) (m + 1) → Levy (n + 1) m :=
      fun {m} i φ => Levy.step (prev.bEx i.succ (prev.bAll 1
        (Levy.lift (n := n) (m := m + 2) (m' := m + 3) (Levy.unstep φ)
          (Fin.cons 0 (Fin.cons 1 (Fin.succ ∘ Fin.succ ∘ Fin.succ))))))
    let and' : ∀ {m}, Levy (n + 1) m → Levy (n + 1) m → Levy (n + 1) m := fun {m} φ ψ =>
      let pairNeg : Levy n (m + 5) :=
        Levy.ofBForm n (isPairBForm.not.lift (Fin.cons 4 (Fin.cons 2 (Fin.cons 0 Fin.elim0))))
      let φ' : Levy n (m + 5) :=
        Levy.lift (n := n) (m := m + 1) (m' := m + 5) (Levy.unstep φ)
          (Fin.cons 2 (Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ))
      let ψ' : Levy n (m + 5) :=
        Levy.lift (n := n) (m := m + 1) (m' := m + 5) (Levy.unstep ψ)
          (Fin.cons 0 (Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ))
      let body : Levy n (m + 5) := prev.or pairNeg (prev.or φ' ψ')
      Levy.step (prev.bAll 0 (prev.bAll 0 (prev.bAll 2 (prev.bAll 0 body))))
    { or := or'
      and := and'
      bEx := bEx'
      bAll := bAll'
      eval_or := fun φ ψ f => by
        simp only [or', Levy.eval_unstep, Levy.unstep_step, prev.eval_and]
        constructor
        · rintro ⟨u, hu⟩
          by_cases h1 : Levy.eval (n := n) (Levy.unstep φ) (Fin.cons u f)
          · exact Or.inr ⟨u, fun h2 => hu ⟨h1, h2⟩⟩
          · exact Or.inl ⟨u, h1⟩
        · rintro (⟨u, hu⟩ | ⟨u, hu⟩)
          · exact ⟨u, fun h => hu h.1⟩
          · exact ⟨u, fun h => hu h.2⟩
      eval_and := fun {m} φ ψ f => by
        simp only [and', Levy.eval_unstep, Levy.unstep_step, prev.eval_bAll, prev.eval_or,
          Levy.eval_ofBForm, BForm.eval_lift, BForm.eval_not, Levy.eval_lift]
        have hpair : ∀ (p s u t v : M),
            isPairBForm.eval (Fin.cons v (Fin.cons t (Fin.cons u (Fin.cons s (Fin.cons p f)))) ∘
              Fin.cons 4 (Fin.cons 2 (Fin.cons 0 Fin.elim0))) ↔ IsPairM p u v := by
          intro p s u t v
          rw [eval_isPairBForm hM]; rfl
        have hφ : ∀ (p s u t v : M),
            Fin.cons v (Fin.cons t (Fin.cons u (Fin.cons s (Fin.cons p f)))) ∘
              Fin.cons 2 (Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ) = Fin.cons u f := by
          intro p s u t v; ext j; refine Fin.cases rfl (fun _ => rfl) j
        have hψ : ∀ (p s u t v : M),
            Fin.cons v (Fin.cons t (Fin.cons u (Fin.cons s (Fin.cons p f)))) ∘
              Fin.cons 0 (Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ) = Fin.cons v f := by
          intro p s u t v; ext j; refine Fin.cases rfl (fun _ => rfl) j
        constructor
        · rintro ⟨p, hp⟩
          by_contra hnot
          apply hp
          intro s hsp u hus t htp v hvt
          rw [hpair, hφ, hψ]
          by_cases hpuv : IsPairM p u v
          · by_cases h1 : Levy.eval (n := n) (Levy.unstep φ) (Fin.cons u f)
            · exact Or.inr (Or.inl h1)
            · by_cases h2 : Levy.eval (n := n) (Levy.unstep ψ) (Fin.cons v f)
              · exact Or.inr (Or.inr h2)
              · exact absurd ⟨⟨u, h1⟩, ⟨v, h2⟩⟩ hnot
          · exact Or.inl hpuv
        · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
          let p := pair hM u v
          let d := dbl hM u v
          have hdp : MemRelM d p := (pair_spec hM u v d).mpr (Or.inr (dbl_spec hM u v))
          have hud : MemRelM u d := (dbl_spec hM u v u).mpr (Or.inl rfl)
          have hvd : MemRelM v d := (dbl_spec hM u v v).mpr (Or.inr rfl)
          refine ⟨p, fun hall => ?_⟩
          have h := hall d hdp u hud d hdp v hvd
          rw [hpair, hφ, hψ] at h
          rcases h with hnp | h1 | h2
          · exact hnp (pair_spec hM u v)
          · exact hu h1
          · exact hv h2
      eval_bEx := fun i φ f => by
        simp only [bEx', Levy.eval_unstep, Levy.unstep_step, prev.eval_bAll, Levy.eval_lift,
          cons_comp_swap01]
        constructor
        · rintro ⟨u, hu⟩
          push Not at hu
          obtain ⟨w, hwi, hw⟩ := hu
          exact ⟨w, hwi, u, hw⟩
        · rintro ⟨w, hwi, u, hu⟩
          exact ⟨u, fun hall => hu (hall w hwi)⟩
      eval_bAll := fun {m} i φ f => by
        simp only [bAll', Levy.eval_unstep, Levy.unstep_step, prev.eval_bEx, prev.eval_bAll,
          Levy.eval_lift]
        have hcomp : ∀ (B w u : M),
            Fin.cons u (Fin.cons w (Fin.cons B f)) ∘
              Fin.cons 0 (Fin.cons 1 (Fin.succ ∘ Fin.succ ∘ Fin.succ)) =
              Fin.cons u (Fin.cons w f) := by
          intro B w u
          ext j
          refine Fin.cases rfl (fun j' => Fin.cases rfl (fun _ => rfl) j') j
        simp only [hcomp]
        constructor
        · rintro ⟨B, hB⟩ w hwi
          by_contra hnot
          apply hB
          refine ⟨w, hwi, fun u _ => ?_⟩
          by_contra hu
          exact hnot ⟨u, hu⟩
        · intro hall
          let vars : Fin (m + 2) → ℕ := Fin.cons (m + 1) (Fin.cons m (fun t : Fin m => t.1))
          let ψF : SFormula := ∼(Levy.toFormula (n := n) (m := m + 2) (Levy.unstep φ) vars (m + 4))
          have hvars : ∀ j : Fin (m + 2), vars j < m + 4 := by
            intro j
            refine Fin.cases (by simp only [vars, Fin.cons_zero]; omega) (fun j' =>
              Fin.cases (by simp only [vars, Fin.cons_succ, Fin.cons_zero]; omega)
                (fun k => by simp only [vars, Fin.cons_succ]; omega) j') j
          have hhb : (m + 3 : ℕ) ∉ ψF.freeVarFinset := fun h => by
            obtain ⟨j, hj⟩ := Levy.fv_toFormula (n := n) (m := m + 2) (Levy.unstep φ) vars (m + 4) (mem_freeVarFinset_not h)
            refine Fin.cases (fun h' => by simp only [vars, Fin.cons_zero] at h'; omega)
              (fun j' => Fin.cases (fun h' => by simp only [vars, Fin.cons_succ, Fin.cons_zero] at h'; omega)
                (fun k h' => by simp only [vars, Fin.cons_succ] at h'; omega) j') j hj
          let env : ℕ → M := fun k =>
            if hk : k < m then f ⟨k, hk⟩ else f i
          have hnodup : [m, m + 1, m + 2, m + 3].Nodup := by
            simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨⟨by omega, by omega, by omega⟩, ⟨by omega, by omega⟩, by omega,
              not_false, List.nodup_nil⟩
          have htot : ∀ w : M, MemRelM w (env (m + 2)) →
              ∃ u : M, Formula.Realize ψF (Function.update (Function.update env m w) (m + 1) u) := by
            intro w hw
            have hwi : MemRelM w (f i) := by
              have hne : ¬ (m + 2 < m) := by omega
              simpa [env, hne] using hw
            obtain ⟨u, hu⟩ := hall w hwi
            refine ⟨u, ?_⟩
            simp only [ψF, Formula.realize_not,
              Levy.realize_toFormula (n := n) (m := m + 2) (Levy.unstep φ) vars (m + 4) hvars]
            have hev : Function.update (Function.update env m w) (m + 1) u ∘ vars =
                Fin.cons u (Fin.cons w f) := by
              ext j
              refine Fin.cases ?_ (fun j' => Fin.cases ?_ ?_ j') j
              · simp [vars]
              · simp [vars]
              · intro k
                simp [vars, env, k.2, Function.update_of_ne (by omega : k.1 ≠ m + 1),
                  Function.update_of_ne (by omega : k.1 ≠ m)]
            rwa [hev]
          obtain ⟨B, hB⟩ := ax_coll hM ψF m (m + 1) (m + 2) (m + 3) hnodup hhb env htot
          refine ⟨B, ?_⟩
          rintro ⟨w, hwi, hwall⟩
          have hwenv : MemRelM w (env (m + 2)) := by
            have hne : ¬ (m + 2 < m) := by omega
            simpa [env, hne] using hwi
          obtain ⟨u, huB, huφ⟩ := hB w hwenv
          simp only [ψF, Formula.realize_not,
            Levy.realize_toFormula (n := n) (m := m + 2) (Levy.unstep φ) vars (m + 4) hvars] at huφ
          have hev : Function.update (Function.update env m w) (m + 1) u ∘ vars =
              Fin.cons u (Fin.cons w f) := by
            ext j
            refine Fin.cases ?_ (fun j' => Fin.cases ?_ ?_ j') j
            · simp [vars]
            · simp [vars]
            · intro k
              simp [vars, env, k.2, Function.update_of_ne (by omega : k.1 ≠ m + 1),
                Function.update_of_ne (by omega : k.1 ≠ m)]
          rw [hev] at huφ
          exact huφ (hwall u huB) }

private def levyEx {n m : ℕ} (φ : Levy (n + 1) (m + 1)) : Levy (n + 1) m :=
  let prev := levyOps hM n
  let pairNeg : Levy n (m + 5) :=
    Levy.ofBForm n (isPairBForm.not.lift (Fin.cons 4 (Fin.cons 2 (Fin.cons 0 Fin.elim0))))
  let φ' : Levy n (m + 5) :=
    Levy.lift (n := n) (m := m + 2) (m' := m + 5) (Levy.unstep φ)
      (Fin.cons 2 (Fin.cons 0 (Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ)))
  let body : Levy n (m + 5) := prev.or pairNeg φ'
  Levy.step (prev.bAll 0 (prev.bAll 0 (prev.bAll 2 (prev.bAll 0 body))))

private lemma eval_levyEx {n m : ℕ} (φ : Levy (n + 1) (m + 1)) (f : Fin m → M) :
    Levy.eval (n := n + 1) (levyEx hM φ) f ↔ ∃ v : M, Levy.eval (n := n + 1) φ (Fin.cons v f) := by
  simp only [levyEx, Levy.eval_unstep, Levy.unstep_step, (levyOps hM n).eval_bAll,
    (levyOps hM n).eval_or, Levy.eval_ofBForm, BForm.eval_lift, BForm.eval_not, Levy.eval_lift]
  have hpair : ∀ (p s u t v : M),
      isPairBForm.eval (Fin.cons v (Fin.cons t (Fin.cons u (Fin.cons s (Fin.cons p f)))) ∘
        Fin.cons 4 (Fin.cons 2 (Fin.cons 0 Fin.elim0))) ↔ IsPairM p u v := by
    intro p s u t v; rw [eval_isPairBForm hM]; rfl
  have hφ : ∀ (p s u t v : M),
      Fin.cons v (Fin.cons t (Fin.cons u (Fin.cons s (Fin.cons p f)))) ∘
        Fin.cons 2 (Fin.cons 0 (Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ ∘ Fin.succ)) =
        Fin.cons u (Fin.cons v f) := by
    intro p s u t v; ext j; refine Fin.cases rfl (fun j' => Fin.cases rfl (fun _ => rfl) j') j
  constructor
  · rintro ⟨p, hp⟩
    by_contra hnot
    apply hp
    intro s hsp u hus t htp v hvt
    rw [hpair, hφ]
    by_cases hpuv : IsPairM p u v
    · refine Or.inr ?_
      by_contra h1
      exact hnot ⟨v, u, h1⟩
    · exact Or.inl hpuv
  · rintro ⟨v, u, hu⟩
    let p := pair hM u v
    let d := dbl hM u v
    have hdp : MemRelM d p := (pair_spec hM u v d).mpr (Or.inr (dbl_spec hM u v))
    have hud : MemRelM u d := (dbl_spec hM u v u).mpr (Or.inl rfl)
    have hvd : MemRelM v d := (dbl_spec hM u v v).mpr (Or.inr rfl)
    refine ⟨p, fun hall => ?_⟩
    have h := hall d hdp u hud d hdp v hvd
    rw [hpair, hφ] at h
    rcases h with hnp | h1
    · exact hnp (pair_spec hM u v)
    · exact hu h1

/-! Gaifman's Lemma on `Levy n m` -/

private lemma gaifman_levy (k : M → M) (hk : IsGodelCofinalEmb k) :
    ∀ {n m : ℕ} (φ : Levy n m) (f : Fin m → M),
      Levy.eval (n := n) φ f ↔ Levy.eval (n := n) φ (k ∘ f)
  | 0, _, b, f => bForm_pres hM k hk b f
  | n + 1, m, ψ, f => by
    simp only [Levy.eval_unstep]
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨k u, fun h => hu ?_⟩
      have hcomp : Fin.cons (k u) (k ∘ f) = k ∘ Fin.cons u f := by
        ext j; refine Fin.cases rfl (fun _ => rfl) j
      rw [hcomp] at h
      exact (gaifman_levy k hk (n := n) (m := m + 1) (Levy.unstep ψ) (Fin.cons u f)).mpr h
    · rintro ⟨w, hw⟩
      obtain ⟨b, hwb⟩ := hk.cofinal w
      let prev := levyOps hM n
      let χ : Levy n (m + 1) := prev.bAll 0
        (Levy.lift (n := n) (m := m + 1) (m' := m + 2) (Levy.unstep ψ) (Fin.cons 0 (Fin.succ ∘ Fin.succ)))
      have hχ_eval : ∀ (B : M) (g : Fin m → M),
          Levy.eval (n := n) χ (Fin.cons B g) ↔
            ∀ u : M, MemRelM u B → Levy.eval (n := n) (Levy.unstep ψ) (Fin.cons u g) := by
        intro B g
        simp only [χ, prev.eval_bAll, Levy.eval_lift, Fin.cons_zero]
        refine forall_congr' fun u => imp_congr_right fun _ => ?_
        have hc : Fin.cons u (Fin.cons B g) ∘ Fin.cons 0 (Fin.succ ∘ Fin.succ) = Fin.cons u g := by
          ext j; refine Fin.cases rfl (fun _ => rfl) j
        rw [hc]
      have hnot_k : ¬ Levy.eval (n := n) χ (k ∘ Fin.cons b f) := by
        have hcomp : k ∘ Fin.cons b f = Fin.cons (k b) (k ∘ f) := by
          ext j; refine Fin.cases rfl (fun _ => rfl) j
        rw [hcomp, hχ_eval]
        intro hall
        exact hw (hall w hwb)
      have hnot_b : ¬ Levy.eval (n := n) χ (Fin.cons b f) := fun h =>
        hnot_k ((gaifman_levy k hk (n := n) (m := m + 1) χ (Fin.cons b f)).mp h)
      rw [hχ_eval] at hnot_b
      push Not at hnot_b
      obtain ⟨u, _, hu⟩ := hnot_b
      exact ⟨u, hu⟩

/-! ### Part 8: Translating any `setLang.BoundedFormula ℕ l` to `Levy` -/

private def toLevy {m : ℕ} :
    ∀ {l : ℕ} (φ : setLang.BoundedFormula ℕ l),
      (∀ a ∈ φ.freeVarFinset, a < m) →
      Σ n : ℕ, { ψ : Levy n (m + l) //
        ∀ (v : ℕ → M) (xs : Fin l → M),
          Levy.eval (n := n) ψ (Fin.append (fun i : Fin m => v i.1) xs) ↔
            BoundedFormula.Realize φ v xs }
  | _, .falsum, _ =>
    ⟨0, ⟨BForm.falsum, fun _ _ => Iff.rfl⟩⟩
  | _, .equal t₁ t₂, hφ =>
    have ht₁ : ∀ a ∈ t₁.varFinsetLeft, a < m := fun a ha =>
      hφ a (by simp [BoundedFormula.freeVarFinset, ha])
    have ht₂ : ∀ a ∈ t₂.varFinsetLeft, a < m := fun a ha =>
      hφ a (by simp [BoundedFormula.freeVarFinset, ha])
    ⟨0, ⟨BForm.eq (termIdx t₁ ht₁) (termIdx t₂ ht₂), fun v xs => by
      simp only [Levy.eval, BForm.eval, realize_termIdx, BoundedFormula.Realize]⟩⟩
  | _, .rel R ts, hφ => by
    cases R with
    | mem =>
      have ht0 : ∀ a ∈ (ts 0).varFinsetLeft, a < m := fun a ha =>
        hφ a (by simp only [BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨0, ha⟩)
      have ht1 : ∀ a ∈ (ts 1).varFinsetLeft, a < m := fun a ha =>
        hφ a (by simp only [BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and]; exact ⟨1, ha⟩)
      refine ⟨0, ⟨BForm.mem (termIdx (ts 0) ht0) (termIdx (ts 1) ht1), fun v xs => ?_⟩⟩
      simp only [Levy.eval, BForm.eval, realize_termIdx, BoundedFormula.Realize, MemRelM]
      have hvec : (fun i : Fin 2 => (ts i).realize (Sum.elim v xs)) =
          ![(ts 0).realize (Sum.elim v xs), (ts 1).realize (Sum.elim v xs)] := by
        ext ⟨i, hi⟩
        match i with
        | 0 => rfl
        | 1 => rfl
        | _ + 2 => omega
      rw [hvec]
      rfl
  | _, .imp φ₁ φ₂, hφ =>
    have h₁ : ∀ a ∈ φ₁.freeVarFinset, a < m := fun a ha =>
      hφ a (by simp [BoundedFormula.freeVarFinset, ha])
    have h₂ : ∀ a ∈ φ₂.freeVarFinset, a < m := fun a ha =>
      hφ a (by simp [BoundedFormula.freeVarFinset, ha])
    let r₁ := toLevy φ₁ h₁
    let r₂ := toLevy φ₂ h₂
    let N := max r₁.1 r₂.1
    let ψ₁ : Levy (N + 1) _ := Levy.neg (Levy.raiseLe (le_max_left _ _) r₁.2.1)
    let ψ₂ : Levy (N + 1) _ := Levy.raiseLe (Nat.le_succ_of_le (le_max_right _ _)) r₂.2.1
    ⟨N + 1, ⟨(levyOps hM (N + 1)).or ψ₁ ψ₂, fun v xs => by
      simp only [(levyOps hM (N + 1)).eval_or, ψ₁, ψ₂, Levy.eval_neg, Levy.eval_raiseLe,
        r₁.2.2 v xs, r₂.2.2 v xs, BoundedFormula.Realize]
      tauto⟩⟩
  | l, .all φ, hφ =>
    let r := toLevy φ hφ
    let ψ_rot : Levy r.1 (m + l + 1) := Levy.lift (n := r.1) r.2.1 (consToSnoc (m + l))
    let ψ_ex : Levy (r.1 + 1) (m + l) := levyEx hM (Levy.neg ψ_rot)
    ⟨r.1 + 2, ⟨Levy.neg ψ_ex, fun v xs => by
      simp only [Levy.eval_neg, ψ_ex, eval_levyEx hM, ψ_rot, Levy.eval_lift,
        cons_comp_consToSnoc, ← append_snoc, r.2.2 v, BoundedFormula.Realize]
      push Not; rfl⟩⟩

private lemma gaifman_main (k : M → M) (hk : IsGodelCofinalEmb k)
    (φ : SFormula) (v : ℕ → M) :
    Formula.Realize (incl.onBoundedFormula φ) v ↔
      Formula.Realize (incl.onBoundedFormula φ) (k ∘ v) := by
  rw [realize_onBoundedFormula_formula, realize_onBoundedFormula_formula]
  let m : ℕ := φ.freeVarFinset.sup id + 1
  have hm : ∀ a ∈ φ.freeVarFinset, a < m := fun a ha =>
    Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
  let r := toLevy hM (m := m) φ hm
  have h1 := r.2.2 v default
  have h2 := r.2.2 (k ∘ v) default
  change Levy.eval (n := r.1) r.2.1 (Fin.append (fun i : Fin m => v i.1) default) ↔ Formula.Realize φ v at h1
  change Levy.eval (n := r.1) r.2.1 (Fin.append (fun i : Fin m => k (v i.1)) default) ↔ Formula.Realize φ (k ∘ v) at h2
  have hcomp : Fin.append (fun i : Fin m => k (v i.1)) (default : Fin 0 → M) =
      k ∘ Fin.append (fun i : Fin m => v i.1) default := by
    ext ⟨i, hi⟩
    have him : i < m := by omega
    simp [Fin.append, Fin.addCases, him]
  rw [← h1, ← h2, hcomp]
  exact gaifman_levy hM k hk (n := r.1) r.2.1 _

end ZFjNonempty

end ZFjPart

end Semantics2

end KunenZFGaifman

theorem solution {M : Type u} [setLangJ.Structure M] [Nonempty M]
    (hM : M ⊨ ZFj) (k : M → M) (hk : IsGodelCofinalEmb k)
    (φ : ContinuumHypothesis.SFormula) (v : ℕ → M) :
    Formula.Realize (incl.onBoundedFormula φ) v ↔
      Formula.Realize (incl.onBoundedFormula φ) (k ∘ v) :=
  KunenZFGaifman.gaifman_main hM k hk φ v

