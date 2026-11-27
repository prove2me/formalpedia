-- Prove2me | solution 1 for KunenZF.nontrivial_moves_ordinal_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @teargosling
-- created : 2026-11-27T03:41:44.126092+00:00
-- url     : https://prove2.me/submissions/02205f8f-1aee-4483-975b-f4e82f8589d6

import Mathlib.ModelTheory.Semantics
import Definitions.Def_CH_SetTheoryLanguage
import Definitions.Def_CH_ZFC
import Definitions.Def_KunenZF_language
import Definitions.Def_KunenZF_theory

universe u

open FirstOrder FirstOrder.Language ContinuumHypothesis ContinuumHypothesis.SFormula
open KunenZF KunenZF.SFormulaJ

namespace KunenZFProof

/-! ### Part 1: Generic `freeVarFinset` and realization helpers -/

private lemma realize_congr_freeVar {L : FirstOrder.Language} {M : Type u} [L.Structure M]
    {α : Type*} [DecidableEq α] {φ : L.Formula α} {v₁ v₂ : α → M}
    (h : ∀ a ∈ φ.freeVarFinset, v₁ a = v₂ a) :
    φ.Realize v₁ ↔ φ.Realize v₂ := by
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

private lemma mem_freeVarFinset_allJ {x : ℕ} {φ : SFormulaJ} {v : ℕ}
    (hv : v ∈ (allJ x φ).freeVarFinset) : v ∈ φ.freeVarFinset ∧ v ≠ x := by
  have h1 := mem_freeVarFinset_iAlls _ hv
  obtain ⟨a, ha, hga⟩ := mem_freeVarFinset_formula_relabel _ φ h1
  by_cases hax : a = x
  · simp [hax] at hga
  · simp only [hax, ↓reduceIte, Sum.inl.injEq] at hga
    subst hga
    exact ⟨ha, hax⟩

private lemma mem_freeVarFinset_exJ {x : ℕ} {φ : SFormulaJ} {v : ℕ}
    (hv : v ∈ (exJ x φ).freeVarFinset) : v ∈ φ.freeVarFinset ∧ v ≠ x := by
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

private lemma mem_freeVarFinset_memJ {x y v : ℕ} (hv : v ∈ (memJ x y).freeVarFinset) :
    v = x ∨ v = y := by
  simp only [memJ, Relations.formula₂, Relations.formula, Relations.boundedFormula,
    BoundedFormula.freeVarFinset, Finset.mem_biUnion, Finset.mem_univ, true_and] at hv
  obtain ⟨⟨i, hi⟩, hmem⟩ := hv
  match i with
  | 0 => simp [Term.relabel, Term.varFinsetLeft] at hmem; exact Or.inl hmem
  | 1 => simp [Term.relabel, Term.varFinsetLeft] at hmem; exact Or.inr hmem
  | _ + 2 => omega

private lemma mem_freeVarFinset_eqJ {x y v : ℕ} (hv : v ∈ (eqJ x y).freeVarFinset) :
    v = x ∨ v = y := by
  simp only [eqJ, Term.equal, Term.bdEqual, Term.relabel, BoundedFormula.freeVarFinset,
    Finset.mem_union, Term.varFinsetLeft, Finset.mem_singleton] at hv
  exact hv

private lemma mem_freeVarFinset_jEq {x y v : ℕ}
    (hv : v ∈ (Term.equal (jTerm x) (Term.var y)).freeVarFinset) : v = x ∨ v = y := by
  simp only [jTerm, Term.equal, Term.bdEqual, Term.relabel, BoundedFormula.freeVarFinset,
    Finset.mem_union, Term.varFinsetLeft, Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_singleton] at hv
  rcases hv with ⟨_, h⟩ | h
  · exact Or.inl h
  · exact Or.inr h

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

/-! ### Part 2: Pure set-theory formulas for `Ord`, `Union`, `Chain`, `VSeq`, `VAt` -/

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

def isVSeqF (s α : ℕ) : SFormula :=
  isOrdF α ⊓
  ex 2020 (isSucc 2020 α ⊓
    all 2021 (mem 2021 s ⟹ ex 2022 (mem 2022 2020 ⊓ ex 2023 (isPair 2021 2022 2023))) ⊓
    all 2022 (mem 2022 2020 ⟹ ex 2023 (pairIn s 2022 2023)) ⊓
    all 2022 (all 2023 (all 2024 ((pairIn s 2022 2023 ⊓ pairIn s 2022 2024) ⟹ eq 2023 2024))) ⊓
    all 2022 (all 2023 ((mem 2022 2020 ⊓ pairIn s 2022 2023) ⟹
      all 2025 (mem 2025 2023 ⇔
        ex 2026 (mem 2026 2022 ⊓ ex 2027 (pairIn s 2026 2027 ⊓ subset 2025 2027))))))

def isVAtF (v α : ℕ) : SFormula :=
  isOrdF α ⊓ ex 2030 (isVSeqF 2030 α ⊓ pairIn 2030 α v)

end

/-! ### Part 3: Free-variable bounds for our helper formulas -/

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

private lemma fv_isPowerset {p x v : ℕ} (hv : v ∈ (isPowerset p x).freeVarFinset) :
    v = p ∨ v = x := by
  obtain ⟨h, hne⟩ := mem_freeVarFinset_all hv
  rcases mem_freeVarFinset_iff h with h1 | h2
  · rcases mem_freeVarFinset_mem h1 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inl rfl]
  · rcases fv_subset h2 with rfl | rfl <;> [exact absurd rfl hne; exact Or.inr rfl]

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

private lemma fv_isVSeqF {s α v : ℕ} (hv : v ∈ (isVSeqF s α).freeVarFinset) : v = s ∨ v = α := by
  rcases mem_freeVarFinset_inf hv with h0 | h1
  · exact Or.inr (fv_isOrdF h0)
  · obtain ⟨h, hne20⟩ := mem_freeVarFinset_ex h1
    rcases mem_freeVarFinset_inf h with h1234 | h5
    · rcases mem_freeVarFinset_inf h1234 with h123 | h4
      · rcases mem_freeVarFinset_inf h123 with h12 | h3
        · rcases mem_freeVarFinset_inf h12 with ha | hb
          · rcases fv_isSucc ha with rfl | rfl <;> [exact absurd rfl hne20; exact Or.inr rfl]
          · obtain ⟨hb, hne21⟩ := mem_freeVarFinset_all hb
            rcases mem_freeVarFinset_imp hb with hc | hd
            · rcases mem_freeVarFinset_mem hc with rfl | rfl <;> [exact absurd rfl hne21; exact Or.inl rfl]
            · obtain ⟨hd, hne22⟩ := mem_freeVarFinset_ex hd
              rcases mem_freeVarFinset_inf hd with he | hf
              · rcases mem_freeVarFinset_mem he with rfl | rfl <;> [exact absurd rfl hne22; exact absurd rfl hne20]
              · obtain ⟨hf, hne23⟩ := mem_freeVarFinset_ex hf
                rcases fv_isPair hf with rfl | rfl | rfl <;>
                  [exact absurd rfl hne21; exact absurd rfl hne22; exact absurd rfl hne23]
        · obtain ⟨h3, hne22⟩ := mem_freeVarFinset_all h3
          rcases mem_freeVarFinset_imp h3 with ha | hb
          · rcases mem_freeVarFinset_mem ha with rfl | rfl <;> [exact absurd rfl hne22; exact absurd rfl hne20]
          · obtain ⟨hb, hne23⟩ := mem_freeVarFinset_ex hb
            rcases fv_pairIn hb with rfl | rfl | rfl <;>
              [exact Or.inl rfl; exact absurd rfl hne22; exact absurd rfl hne23]
      · obtain ⟨h4, hne22⟩ := mem_freeVarFinset_all h4
        obtain ⟨h4, hne23⟩ := mem_freeVarFinset_all h4
        obtain ⟨h4, hne24⟩ := mem_freeVarFinset_all h4
        rcases mem_freeVarFinset_imp h4 with ha | hb
        · rcases mem_freeVarFinset_inf ha with hc | hd
          · rcases fv_pairIn hc with rfl | rfl | rfl <;>
              [exact Or.inl rfl; exact absurd rfl hne22; exact absurd rfl hne23]
          · rcases fv_pairIn hd with rfl | rfl | rfl <;>
              [exact Or.inl rfl; exact absurd rfl hne22; exact absurd rfl hne24]
        · rcases mem_freeVarFinset_eq hb with rfl | rfl <;> [exact absurd rfl hne23; exact absurd rfl hne24]
    · obtain ⟨h5, hne22⟩ := mem_freeVarFinset_all h5
      obtain ⟨h5, hne23⟩ := mem_freeVarFinset_all h5
      rcases mem_freeVarFinset_imp h5 with ha | hb
      · rcases mem_freeVarFinset_inf ha with hc | hd
        · rcases mem_freeVarFinset_mem hc with rfl | rfl <;> [exact absurd rfl hne22; exact absurd rfl hne20]
        · rcases fv_pairIn hd with rfl | rfl | rfl <;>
            [exact Or.inl rfl; exact absurd rfl hne22; exact absurd rfl hne23]
      · obtain ⟨hb, hne25⟩ := mem_freeVarFinset_all hb
        rcases mem_freeVarFinset_iff hb with hc | hd
        · rcases mem_freeVarFinset_mem hc with rfl | rfl <;> [exact absurd rfl hne25; exact absurd rfl hne23]
        · obtain ⟨hd, hne26⟩ := mem_freeVarFinset_ex hd
          rcases mem_freeVarFinset_inf hd with he | hf
          · rcases mem_freeVarFinset_mem he with rfl | rfl <;> [exact absurd rfl hne26; exact absurd rfl hne22]
          · obtain ⟨hf, hne27⟩ := mem_freeVarFinset_ex hf
            rcases mem_freeVarFinset_inf hf with hg | hh
            · rcases fv_pairIn hg with rfl | rfl | rfl <;>
                [exact Or.inl rfl; exact absurd rfl hne26; exact absurd rfl hne27]
            · rcases fv_subset hh with rfl | rfl <;> [exact absurd rfl hne25; exact absurd rfl hne27]

private lemma fv_isVAtF {v α w : ℕ} (hw : w ∈ (isVAtF v α).freeVarFinset) : w = v ∨ w = α := by
  rcases mem_freeVarFinset_inf hw with h1 | h2
  · exact Or.inr (fv_isOrdF h1)
  · obtain ⟨h, hne30⟩ := mem_freeVarFinset_ex h2
    rcases mem_freeVarFinset_inf h with ha | hb
    · rcases fv_isVSeqF ha with rfl | rfl <;> [exact absurd rfl hne30; exact Or.inr rfl]
    · rcases fv_pairIn hb with rfl | rfl | rfl <;>
        [exact absurd rfl hne30; exact Or.inr rfl; exact Or.inl rfl]

/-! ### Part 4: Semantic layer on a nonempty model `M` of `reinhardtTheory ∪ {fixesOrdinals}` -/

section Semantics

variable {M : Type u} [setLangJ.Structure M]

local instance setLangReduct : setLang.Structure M := incl.reduct M

def Mem (a b : M) : Prop := Structure.RelMap (L := setLangJ) SetRel.mem ![a, b]
def jVal (a : M) : M := Structure.funMap (L := setLangJ) JFun.j ![a]
def Sub (a b : M) : Prop := ∀ z : M, Mem z a → Mem z b
def IsEmp (e : M) : Prop := ∀ z : M, ¬ Mem z e
def IsSucc (s a : M) : Prop := ∀ z : M, Mem z s ↔ Mem z a ∨ z = a
def IsInd (w : M) : Prop :=
  (∃ e : M, IsEmp e ∧ Mem e w) ∧ ∀ a : M, Mem a w → ∃ s : M, IsSucc s a ∧ Mem s w
def IsPow (p x : M) : Prop := ∀ z : M, Mem z p ↔ Sub z x
def IsSing (t a : M) : Prop := ∀ z : M, Mem z t ↔ z = a
def IsDbl (t a b : M) : Prop := ∀ z : M, Mem z t ↔ z = a ∨ z = b
def IsPair (p a b : M) : Prop := ∀ w : M, Mem w p ↔ IsSing w a ∨ IsDbl w a b
def PairIn (f a b : M) : Prop := ∃ p : M, IsPair p a b ∧ Mem p f
def Trans (t : M) : Prop := ∀ x : M, Mem x t → Sub x t
def Ord (α : M) : Prop := Trans α ∧ ∀ β : M, Mem β α → Trans β
def IsUnion (u x : M) : Prop := ∀ z : M, Mem z u ↔ ∃ y : M, Mem y x ∧ Mem z y

def IsChain (f n x : M) : Prop :=
  ∃ s : M, IsSucc s n ∧
    (∀ p : M, Mem p f → ∃ k : M, Mem k s ∧ ∃ v : M, IsPair p k v) ∧
    (∀ k : M, Mem k s → ∃ v : M, PairIn f k v) ∧
    (∀ k v₁ v₂ : M, PairIn f k v₁ → PairIn f k v₂ → v₁ = v₂) ∧
    (∀ e : M, IsEmp e → ∀ v : M, PairIn f e v → IsSing v x) ∧
    (∀ k k' v v' : M, Mem k n → IsSucc k' k → PairIn f k v → PairIn f k' v' → IsUnion v' v)

def IsVSeq (s α : M) : Prop :=
  Ord α ∧
  ∃ a : M, IsSucc a α ∧
    (∀ p : M, Mem p s → ∃ γ : M, Mem γ a ∧ ∃ v : M, IsPair p γ v) ∧
    (∀ γ : M, Mem γ a → ∃ v : M, PairIn s γ v) ∧
    (∀ γ v₁ v₂ : M, PairIn s γ v₁ → PairIn s γ v₂ → v₁ = v₂) ∧
    (∀ γ v : M, Mem γ a → PairIn s γ v →
      ∀ z : M, Mem z v ↔ ∃ δ : M, Mem δ γ ∧ ∃ u : M, PairIn s δ u ∧ Sub z u)

def IsVAt (v α : M) : Prop := Ord α ∧ ∃ s : M, IsVSeq s α ∧ PairIn s α v

/-! Realization bridge lemmas -/

private lemma realize_mem (v : ℕ → M) (x y : ℕ) :
    Formula.Realize (mem x y) v ↔ Mem (v x) (v y) := by
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
    Formula.Realize (memJ x y) v ↔ Mem (v x) (v y) := by
  rw [memJ, Formula.realize_rel₂]; rfl

private lemma realize_eqJ (v : ℕ → M) (x y : ℕ) :
    Formula.Realize (eqJ x y) v ↔ v x = v y := by
  rw [eqJ, Formula.realize_equal]; rfl

private lemma realize_jTerm (v : ℕ → M) (x : ℕ) :
    Term.realize v (jTerm x) = jVal (v x) := by
  simp only [jTerm, Term.realize, jVal]
  congr 1
  ext i
  rw [Fin.eq_zero i]
  rfl

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

private lemma realize_subst_formula (φ : SFormulaJ) (tf : ℕ → setLangJ.Term ℕ) (v : ℕ → M) :
    Formula.Realize (φ.subst tf) v ↔ Formula.Realize φ (fun n => (tf n).realize v) :=
  BoundedFormula.realize_subst

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
    Formula.Realize (isSingleton t a) v ↔ IsSing (v t) (v a) := by
  simp [isSingleton, IsSing, realize_all, realize_mem, realize_eq,
    Function.update_of_ne ht, Function.update_of_ne ha]

private lemma r_isDoubleton (v : ℕ → M) {t a b : ℕ} (ht : t ≠ 1009) (ha : a ≠ 1009) (hb : b ≠ 1009) :
    Formula.Realize (isDoubleton t a b) v ↔ IsDbl (v t) (v a) (v b) := by
  simp [isDoubleton, IsDbl, realize_all, realize_mem, realize_eq,
    Function.update_of_ne ht, Function.update_of_ne ha, Function.update_of_ne hb]

private lemma r_isPair (v : ℕ → M) {z a b : ℕ}
    (hz : z ≠ 1010) (ha : a ≠ 1008 ∧ a ≠ 1009 ∧ a ≠ 1010) (hb : b ≠ 1009 ∧ b ≠ 1010) :
    Formula.Realize (isPair z a b) v ↔ IsPair (v z) (v a) (v b) := by
  simp only [isPair, IsPair, realize_all, Formula.realize_iff, realize_mem,
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
    Formula.Realize (isUnionF u x) v ↔ IsUnion (v u) (v x) := by
  simp only [isUnionF, IsUnion, realize_all, realize_ex, Formula.realize_iff,
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

private lemma r_isVSeqF (v : ℕ → M) {s α : ℕ} (hs : s < 1000 ∨ 2030 ≤ s) (hα : α < 1000) :
    Formula.Realize (isVSeqF s α) v ↔ IsVSeq (v s) (v α) := by
  simp only [isVSeqF, IsVSeq, realize_ex, realize_all, Formula.realize_inf,
    Formula.realize_imp, Formula.realize_iff, realize_mem, realize_eq,
    r_isOrdF (α := α) _ ⟨by omega, by omega, by omega⟩,
    r_isSucc (s := 2020) (z := α) _ (by omega) (by omega),
    r_isPair (z := 2021) (a := 2022) (b := 2023) _ (by omega)
      ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩,
    r_pairIn (f := s) (a := 2022) (b := 2023) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩,
    r_pairIn (f := s) (a := 2022) (b := 2024) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩,
    r_pairIn (f := s) (a := 2026) (b := 2027) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩,
    r_subset (x := 2025) (y := 2027) _ (by omega) (by omega)]
  simp only [Function.update_self,
    Function.update_of_ne (by omega : s ≠ 2020),
    Function.update_of_ne (by omega : s ≠ 2021),
    Function.update_of_ne (by omega : s ≠ 2022),
    Function.update_of_ne (by omega : s ≠ 2023),
    Function.update_of_ne (by omega : s ≠ 2024),
    Function.update_of_ne (by omega : s ≠ 2025),
    Function.update_of_ne (by omega : s ≠ 2026),
    Function.update_of_ne (by omega : s ≠ 2027),
    Function.update_of_ne (by omega : α ≠ 2020),
    Function.update_of_ne (by omega : (2020 : ℕ) ≠ 2021),
    Function.update_of_ne (by omega : (2020 : ℕ) ≠ 2022),
    Function.update_of_ne (by omega : (2020 : ℕ) ≠ 2023),
    Function.update_of_ne (by omega : (2021 : ℕ) ≠ 2022),
    Function.update_of_ne (by omega : (2021 : ℕ) ≠ 2023),
    Function.update_of_ne (by omega : (2022 : ℕ) ≠ 2023),
    Function.update_of_ne (by omega : (2022 : ℕ) ≠ 2024),
    Function.update_of_ne (by omega : (2022 : ℕ) ≠ 2025),
    Function.update_of_ne (by omega : (2022 : ℕ) ≠ 2026),
    Function.update_of_ne (by omega : (2023 : ℕ) ≠ 2024),
    Function.update_of_ne (by omega : (2023 : ℕ) ≠ 2025),
    Function.update_of_ne (by omega : (2025 : ℕ) ≠ 2026),
    Function.update_of_ne (by omega : (2025 : ℕ) ≠ 2027),
    Function.update_of_ne (by omega : (2026 : ℕ) ≠ 2027)]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨a, ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩
    exact ⟨a, h1, h2, h3, fun γ v₁ v₂ p q => h4 γ v₁ v₂ ⟨p, q⟩,
      fun γ u p q => h5 γ u ⟨p, q⟩⟩
  · rintro ⟨a, h1, h2, h3, h4, h5⟩
    exact ⟨a, ⟨⟨⟨⟨h1, h2⟩, h3⟩, fun γ v₁ v₂ ⟨p, q⟩ => h4 γ v₁ v₂ p q⟩,
      fun γ u ⟨p, q⟩ => h5 γ u p q⟩⟩

private lemma r_isVAtF (env : ℕ → M) {v α : ℕ} (hv : v < 1000) (hα : α < 1000) :
    Formula.Realize (isVAtF v α) env ↔ IsVAt (env v) (env α) := by
  simp only [isVAtF, IsVAt, Formula.realize_inf, realize_ex,
    r_isOrdF (α := α) _ ⟨by omega, by omega, by omega⟩,
    r_isVSeqF (s := 2030) (α := α) _ (Or.inr (by omega)) hα,
    r_pairIn (f := 2030) (a := α) (b := v) _ (by omega)
      ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega, by omega⟩]
  simp [Function.update_of_ne (by omega : v ≠ 2030),
    Function.update_of_ne (by omega : α ≠ 2030)]

private lemma r_isOrdinalJ (v : ℕ → M) {α : ℕ} (hα : α < 1000) :
    Formula.Realize (isOrdinalJ α) v ↔ Ord (v α) := by
  have r_subJ : ∀ (w : ℕ → M) (x y : ℕ), x ≠ 1040 → y ≠ 1040 →
      (Formula.Realize (subsetJ x y) w ↔ Sub (w x) (w y)) := fun w x y hx hy => by
    simp [subsetJ, Sub, realize_allJ, realize_memJ, Function.update_of_ne hx, Function.update_of_ne hy]
  have r_trJ : ∀ (w : ℕ → M) (t : ℕ), t ≠ 1040 → t ≠ 1041 →
      (Formula.Realize (isTransitiveJ t) w ↔ Trans (w t)) := fun w t h0 h1 => by
    simp [isTransitiveJ, Trans, realize_allJ, realize_memJ, r_subJ _ 1041 t (by omega) h0,
      Function.update_of_ne h1]
  simp [isOrdinalJ, Ord, realize_allJ, realize_memJ,
    r_trJ _ α (by omega) (by omega),
    r_trJ _ 1042 (by omega) (by omega),
    Function.update_of_ne (by omega : α ≠ 1042)]

private lemma ord_emp {e : M} (he : IsEmp e) : Ord e :=
  ⟨fun x hx => absurd hx (he x), fun β hβ => absurd hβ (he β)⟩

private lemma ord_mem {α β : M} (hα : Ord α) (hβα : Mem β α) : Ord β :=
  ⟨hα.2 β hβα, fun γ hγβ => hα.2 γ (hα.1 β hβα γ hγβ)⟩

private lemma ord_succ {α s : M} (hα : Ord α) (hs : IsSucc s α) : Ord s := by
  refine ⟨fun x hx z hzx => ?_, fun β hβ => ?_⟩
  · rcases (hs x).mp hx with hxα | rfl
    · exact (hs z).mpr (Or.inl (hα.1 x hxα z hzx))
    · exact (hs z).mpr (Or.inl hzx)
  · rcases (hs β).mp hβ with hβα | rfl
    · exact hα.2 β hβα
    · exact hα.1

private lemma ord_union {A u : M} (hA : ∀ α : M, Mem α A → Ord α) (hu : IsUnion u A) : Ord u := by
  refine ⟨fun x hx z hzx => ?_, fun β hβ => ?_⟩
  · obtain ⟨α, hαA, hxα⟩ := (hu x).mp hx
    exact (hu z).mpr ⟨α, hαA, (hA α hαA).1 x hxα z hzx⟩
  · obtain ⟨α, hαA, hβα⟩ := (hu β).mp hβ
    exact (hA α hαA).2 β hβα

/-! ### Part 5: Extracting axioms from `hM` -/

variable (hM : M ⊨ (reinhardtTheory ∪ {closeJ fixesOrdinalsFormula}))
include hM

private lemma model_zf_axiom {φ : SFormula} (hφ : φ ∈ ZFAxioms) :
    ∀ v : ℕ → M, Formula.Realize φ v := by
  intro v
  have hmem : incl.onSentence (close φ) ∈ reinhardtTheory ∪ {closeJ fixesOrdinalsFormula} :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨close φ, ⟨φ, hφ, rfl⟩, rfl⟩))))
  have hreal : M ⊨ incl.onSentence (close φ) := hM.realize_of_mem _ hmem
  rw [LHom.realize_onSentence] at hreal
  exact realize_of_close hreal v

private lemma ax_ext (x y : M) (h : ∀ z : M, Mem z x ↔ Mem z y) : x = y := by
  have h0 := model_zf_axiom (φ := extensionality) hM (Or.inl (Or.inl (by simp))) (fun _ => x)
  simp only [extensionality, realize_all, Formula.realize_imp, Formula.realize_iff,
    realize_mem, realize_eq] at h0
  exact h0 x y (by simpa using h)

private lemma ax_found (x : M) (hne : ∃ y : M, Mem y x) :
    ∃ y : M, Mem y x ∧ ∀ z : M, ¬ (Mem z y ∧ Mem z x) := by
  have h0 := model_zf_axiom (φ := foundation) hM (Or.inl (Or.inl (by simp))) (fun _ => x)
  simp only [foundation, realize_all, realize_ex, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_not, realize_mem] at h0
  simpa using h0 x hne

private lemma ax_pair (a b : M) : ∃ p : M, IsDbl p a b := by
  have h0 := model_zf_axiom (φ := pairing) hM (Or.inl (Or.inl (by simp))) (fun _ => a)
  simp only [pairing, realize_all, realize_ex,
    r_isDoubleton _ (by omega : (2 : ℕ) ≠ 1009) (by omega : (0 : ℕ) ≠ 1009)
      (by omega : (1 : ℕ) ≠ 1009)] at h0
  simpa using h0 a b

private lemma ax_union (x : M) : ∃ u : M, IsUnion u x := by
  have h0 := model_zf_axiom (φ := union) hM (Or.inl (Or.inl (by simp))) (fun _ => x)
  simp only [union, realize_all, realize_ex, Formula.realize_iff,
    Formula.realize_inf, realize_mem] at h0
  simpa [IsUnion] using h0 x

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
    ∃ B : M, ∀ z : M, Mem z B ↔ Mem z (v a) ∧ Formula.Realize φ (Function.update v x z) := by
  let σ : SFormulaJ := allJ a (exJ b (allJ x (memJ x b ⇔ (memJ x a ⊓ φ))))
  have hσ : IsSeparationJ σ := ⟨φ, x, a, b, hxa, hxb, hab, hb, rfl⟩
  have hmem : closeJ σ ∈ reinhardtTheory ∪ {closeJ fixesOrdinalsFormula} :=
    Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨σ, hσ, rfl⟩))))
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
    ∃ B : M, ∀ z : M, Mem z B ↔ Mem z (v a) ∧ Formula.Realize φ (Function.update v x z) := by
  have hbJ : b ∉ (incl.onBoundedFormula φ).freeVarFinset := fun h =>
    hb (mem_freeVarFinset_onBoundedFormula incl φ h)
  obtain ⟨B, hB⟩ := ax_sepJ hM (incl.onBoundedFormula φ) x a b hxa hxb hab hbJ v
  refine ⟨B, fun z => ?_⟩
  simpa [realize_onBoundedFormula_formula] using hB z

private lemma ax_collJ (φ : SFormulaJ) (x y a b : ℕ) (hnodup : [x, y, a, b].Nodup)
    (hb : b ∉ φ.freeVarFinset) (v : ℕ → M)
    (htot : ∀ u : M, Mem u (v a) →
      ∃ w : M, Formula.Realize φ (Function.update (Function.update v x u) y w)) :
    ∃ B : M, ∀ u : M, Mem u (v a) →
      ∃ w : M, Mem w B ∧ Formula.Realize φ (Function.update (Function.update v x u) y w) := by
  let σ : SFormulaJ := allJ a ((allJ x (memJ x a ⟹ exJ y φ)) ⟹
    exJ b (allJ x (memJ x a ⟹ exJ y (memJ y b ⊓ φ))))
  have hσ : IsCollectionJ σ := ⟨φ, x, y, a, b, hnodup, hb, rfl⟩
  have hmem : closeJ σ ∈ reinhardtTheory ∪ {closeJ fixesOrdinalsFormula} :=
    Or.inl (Or.inl (Or.inl (Or.inr ⟨σ, hσ, rfl⟩)))
  have hreal := realize_of_closeJ (hM.realize_of_mem _ hmem) v
  simp only [σ, realize_allJ, realize_exJ, Formula.realize_imp,
    Formula.realize_inf, realize_memJ] at hreal
  have hnodup' := hnodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnodup'
  rcases hnodup' with ⟨⟨hxy, hxa, hxb⟩, ⟨hya, hyb⟩, hab, _⟩
  have hpre : ∀ u : M, Mem (Function.update (Function.update v a (v a)) x u x)
        (Function.update (Function.update v a (v a)) x u a) →
      ∃ w : M, Formula.Realize φ (Function.update (Function.update (Function.update v a (v a)) x u) y w) := by
    intro u hu
    have hu0 : Mem u (v a) := by
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
  have hu' : Mem (Function.update (Function.update (Function.update v a (v a)) b B) x u x)
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
    (htot : ∀ u : M, Mem u (v a) →
      ∃ w : M, Formula.Realize φ (Function.update (Function.update v x u) y w)) :
    ∃ B : M, ∀ u : M, Mem u (v a) →
      ∃ w : M, Mem w B ∧ Formula.Realize φ (Function.update (Function.update v x u) y w) := by
  have hbJ : b ∉ (incl.onBoundedFormula φ).freeVarFinset := fun h =>
    hb (mem_freeVarFinset_onBoundedFormula incl φ h)
  have htot' : ∀ u : M, Mem u (v a) →
      ∃ w : M, Formula.Realize (incl.onBoundedFormula φ) (Function.update (Function.update v x u) y w) := by
    intro u hu
    obtain ⟨w, hw⟩ := htot u hu
    exact ⟨w, (realize_onBoundedFormula_formula φ _).mpr hw⟩
  obtain ⟨B, hB⟩ := ax_collJ hM (incl.onBoundedFormula φ) x y a b hnodup hbJ v htot'
  refine ⟨B, fun u hu => ?_⟩
  obtain ⟨w, hwB, hwφ⟩ := hB u hu
  exact ⟨w, hwB, (realize_onBoundedFormula_formula φ _).mp hwφ⟩

private lemma ax_elem (φ : SFormula) (v : ℕ → M) :
    Formula.Realize φ v ↔ Formula.Realize φ (jVal ∘ v) := by
  have hmem : closeJ (elemFormula φ) ∈ reinhardtTheory ∪ {closeJ fixesOrdinalsFormula} :=
    Or.inl (Or.inl (Or.inr ⟨elemFormula φ, ⟨φ, rfl⟩, rfl⟩))
  have hreal := realize_of_closeJ (hM.realize_of_mem _ hmem) v
  simp only [elemFormula, Formula.realize_iff, realize_onBoundedFormula_formula] at hreal
  rw [realize_subst_formula, realize_onBoundedFormula_formula] at hreal
  convert hreal using 2
  ext n
  exact (realize_jTerm v n).symm

private lemma ax_nontriv [Nonempty M] : ∃ x : M, jVal x ≠ x := by
  have hmem : closeJ nontrivFormula ∈ reinhardtTheory ∪ {closeJ fixesOrdinalsFormula} :=
    Or.inl (Or.inr rfl)
  have hreal := realize_of_closeJ (hM.realize_of_mem _ hmem) (fun _ => Classical.arbitrary M)
  simp only [nontrivFormula, realize_exJ, Formula.realize_not,
    Formula.realize_equal, realize_jTerm, Term.realize_var, Function.update_self] at hreal
  exact hreal

private lemma ax_fixesOrd (α : M) (hα : Ord α) : jVal α = α := by
  have hmem : closeJ fixesOrdinalsFormula ∈ reinhardtTheory ∪ {closeJ fixesOrdinalsFormula} :=
    Or.inr rfl
  have hreal := realize_of_closeJ (hM.realize_of_mem _ hmem) (fun _ => α)
  simp only [fixesOrdinalsFormula, realize_allJ, Formula.realize_imp,
    r_isOrdinalJ _ (by omega : (0 : ℕ) < 1000), Formula.realize_equal,
    realize_jTerm, Term.realize_var, Function.update_self] at hreal
  exact hreal α hα

/-! ### Part 6: Basic set-theoretic constructions inside `M` -/

private lemma emp_ex [Nonempty M] : ∃ e : M, IsEmp e := by
  obtain ⟨w, ⟨e, he, _⟩, _⟩ := ax_infinity hM
  exact ⟨e, he⟩

private lemma emp_uniq {e₁ e₂ : M} (h₁ : IsEmp e₁) (h₂ : IsEmp e₂) : e₁ = e₂ :=
  ax_ext hM e₁ e₂ fun z => ⟨fun hz => absurd hz (h₁ z), fun hz => absurd hz (h₂ z)⟩

private lemma sing_ex (a : M) : ∃ s : M, IsSing s a := by
  obtain ⟨s, hs⟩ := ax_pair hM a a
  exact ⟨s, fun z => by simpa [IsDbl] using hs z⟩

private lemma sing_uniq {s₁ s₂ a : M} (h₁ : IsSing s₁ a) (h₂ : IsSing s₂ a) : s₁ = s₂ :=
  ax_ext hM s₁ s₂ fun z => (h₁ z).trans (h₂ z).symm

private lemma binUnion_ex (a b : M) : ∃ u : M, ∀ z : M, Mem z u ↔ Mem z a ∨ Mem z b := by
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

private lemma pair_ex (a b : M) : ∃ p : M, IsPair p a b := by
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

private lemma pair_inj {p₁ p₂ a₁ b₁ a₂ b₂ : M}
    (h₁ : IsPair p₁ a₁ b₁) (h₂ : IsPair p₂ a₂ b₂) (heq : p₁ = p₂) :
    a₁ = a₂ ∧ b₁ = b₂ := by
  subst heq
  obtain ⟨s₁, hs₁⟩ := sing_ex hM a₁
  obtain ⟨d₁, hd₁⟩ := ax_pair hM a₁ b₁
  obtain ⟨s₂, hs₂⟩ := sing_ex hM a₂
  obtain ⟨d₂, hd₂⟩ := ax_pair hM a₂ b₂
  have hs₁_mem : Mem s₁ p₁ := (h₁ s₁).mpr (Or.inl hs₁)
  have hd₁_mem : Mem d₁ p₁ := (h₁ d₁).mpr (Or.inr hd₁)
  have hs₂_mem : Mem s₂ p₁ := (h₂ s₂).mpr (Or.inl hs₂)
  have hd₂_mem : Mem d₂ p₁ := (h₂ d₂).mpr (Or.inr hd₂)
  have ha : a₁ = a₂ := by
    rcases (h₂ s₁).mp hs₁_mem with hs | hd
    · exact ((hs a₁).mp ((hs₁ a₁).mpr rfl))
    · have h1 := (hd a₁).mp ((hs₁ a₁).mpr rfl)
      have h2 := (hs₁ a₂).mp ((hd a₂).mpr (Or.inl rfl))
      exact h2.symm
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

private lemma mem_irrefl (x : M) : ¬ Mem x x := by
  intro hxx
  obtain ⟨s, hs⟩ := sing_ex hM x
  obtain ⟨y, hys, hmin⟩ := ax_found hM s ⟨x, (hs x).mpr rfl⟩
  have hyx : y = x := (hs y).mp hys
  subst hyx
  exact hmin y ⟨hxx, hys⟩

private lemma mem_asym {x y : M} (hxy : Mem x y) : ¬ Mem y x := by
  intro hyx
  obtain ⟨d, hd⟩ := ax_pair hM x y
  obtain ⟨w, hwd, hmin⟩ := ax_found hM d ⟨x, (hd x).mpr (Or.inl rfl)⟩
  rcases (hd w).mp hwd with rfl | rfl
  · exact hmin y ⟨hyx, (hd y).mpr (Or.inr rfl)⟩
  · exact hmin x ⟨hxy, (hd x).mpr (Or.inl rfl)⟩

private lemma succ_inj_ord {a b s : M} (ha : Ord a) (hb : Ord b)
    (hsa : IsSucc s a) (hsb : IsSucc s b) : a = b := by
  have ha_s : Mem a s := (hsa a).mpr (Or.inr rfl)
  have hb_s : Mem b s := (hsb b).mpr (Or.inr rfl)
  rcases (hsb a).mp ha_s with hab | rfl
  · rcases (hsa b).mp hb_s with hba | rfl
    · exact absurd hba (mem_asym hM hab)
    · rfl
  · rfl

/-! ### Part 7: `ω` and transitive closure inside `M` -/

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
  have hω_mem : ∀ z : M, Mem z ω ↔ Mem z w₀ ∧ ∀ u : M, IsInd u → Mem z u := by
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
    have haw : Mem a w₀ := ((hω_mem a).mp ha).1
    obtain ⟨s, hsa, hsw⟩ := hw₀.2 a haw
    refine ⟨s, hsa, (hω_mem s).mpr ⟨hsw, fun u hu => ?_⟩⟩
    have hau : Mem a u := ((hω_mem a).mp ha).2 u hu
    obtain ⟨s', hs'a, hs'u⟩ := hu.2 a hau
    rwa [succ_uniq hM hsa hs'a]

private lemma chain_ex_and_uniq (ω : M) (hω_ind : IsInd ω) (hω_min : ∀ u : M, IsInd u → Sub ω u)
    (x : M) :
    (∀ n : M, Mem n ω → Ord n) ∧
    (∀ n : M, Mem n ω → ∃ f : M, IsChain f n x) ∧
    (∀ n₁ n₂ f₁ f₂ k v₁ v₂ : M, Mem n₁ ω → Mem n₂ ω →
      IsChain f₁ n₁ x → IsChain f₂ n₂ x → Mem k ω →
      PairIn f₁ k v₁ → PairIn f₂ k v₂ → v₁ = v₂) := by
  have hω_ord : ∀ n : M, Mem n ω → Ord n := by
    have hhb : (2 : ℕ) ∉ (isOrdF 0).freeVarFinset := fun h => by
      have := fv_isOrdF h; omega
    obtain ⟨U, hU⟩ := ax_sep hM (isOrdF 0) 0 1 2 (by omega) (by omega) (by omega) hhb (fun _ => ω)
    have hU_mem : ∀ z : M, Mem z U ↔ Mem z ω ∧ Ord z := fun z => by
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
  have hchain_ex : ∀ n : M, Mem n ω → ∃ f : M, IsChain f n x := by
    let φ : SFormula := ex 3 (isChainF 3 0 4)
    have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
      obtain ⟨h1, hne3⟩ := mem_freeVarFinset_ex h
      rcases fv_isChainF h1 with h3 | h0 | h4 <;> omega
    let env : ℕ → M := Function.update (fun _ => ω) 4 x
    obtain ⟨U, hU⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
    have hU_mem : ∀ n : M, Mem n U ↔ Mem n ω ∧ ∃ f : M, IsChain f n x := fun n => by
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
        have hf'_mem : ∀ q : M, Mem q f' ↔ Mem q f ∨ q = p_new := fun q => by
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
        have hn'_not_in_n' : ¬ Mem n' n' := mem_irrefl hM n'
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
              have hk_eq_n : k = n := succ_inj_ord hM (ord_mem (hω_ord n hnω) hkn) (hω_ord n hnω) hk'k hn'n
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
  have hchain_uniq : ∀ n₁ n₂ f₁ f₂ k v₁ v₂ : M, Mem n₁ ω → Mem n₂ ω →
      IsChain f₁ n₁ x → IsChain f₂ n₂ x → Mem k ω →
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
    have hU_mem : ∀ m : M, Mem m U ↔ Mem m ω ∧ ∀ w₁ w₂ : M, PairIn f₁ m w₁ → PairIn f₂ m w₂ → w₁ = w₂ := by
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
        have hm'_s1 : Mem m' s₁ := by
          obtain ⟨q, hq, hqf⟩ := h1'
          obtain ⟨k', hk', _, hkw⟩ := hf₁_p q hqf
          have heq := (pair_inj hM hq hkw rfl).1
          rwa [heq]
        have hm'_s2 : Mem m' s₂ := by
          obtain ⟨q, hq, hqf⟩ := h2'
          obtain ⟨k', hk', _, hkw⟩ := hf₂_p q hqf
          have heq := (pair_inj hM hq hkw rfl).1
          rwa [heq]
        have hm_n1 : Mem m n₁ := by
          rcases (hs₁ m').mp hm'_s1 with hm'n1 | rfl
          · exact (hω_ord n₁ hn₁).1 m' hm'n1 m ((hm'm m).mpr (Or.inr rfl))
          · exact (hm'm m).mpr (Or.inr rfl)
        have hm_n2 : Mem m n₂ := by
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

private lemma exists_transitive_superset [Nonempty M] (x : M) : ∃ T : M, Mem x T ∧ Trans T := by
  obtain ⟨ω, hω_ind, hω_min⟩ := omega_ex hM
  obtain ⟨_, hchain_ex, hchain_uniq⟩ := chain_ex_and_uniq hM ω hω_ind hω_min x
  let φ : SFormula := ex 5 (isChainF 5 0 6 ⊓ pairIn 5 0 1)
  have hhb : (3 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne5⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with ha | hb
    · rcases fv_isChainF ha with h5 | h0 | h6 <;> omega
    · rcases fv_pairIn hb with h5 | h0 | h1 <;> omega
  let env : ℕ → M := Function.update (fun _ => ω) 6 x
  have htot : ∀ n : M, Mem n (env 2) →
      ∃ y : M, Formula.Realize φ (Function.update (Function.update env 0 n) 1 y) := by
    intro n hn
    have hnω : Mem n ω := by simpa [env] using hn
    obtain ⟨f, hf⟩ := hchain_ex n hnω
    have ⟨s, hs, _, hf_dom, _, _, _⟩ := hf
    obtain ⟨y, hy⟩ := hf_dom n ((hs n).mpr (Or.inr rfl))
    refine ⟨y, ?_⟩
    simp only [φ, realize_ex, Formula.realize_inf,
      r_isChainF (f := 5) (n := 0) (x := 6) _ (by omega) (by omega) (by omega),
      r_pairIn (f := 5) (a := 0) (b := 1) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩]
    refine ⟨f, ?_, ?_⟩
    · simpa [env] using hf
    · simpa [env] using hy
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
  have hC_mem : ∀ y : M, Mem y C ↔ Mem y B ∧ ∃ n : M, Mem n ω ∧ ∃ f : M, IsChain f n x ∧ PairIn f n y := by
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
    have hyC : Mem y C := (hC_mem y).mpr ⟨hyB, e, heω, f, hf, hfy⟩
    obtain ⟨_, _, _, _, _, hf_z, _⟩ := hf
    have hxy : Mem x y := (hf_z e he y hfy x).mpr rfl
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
    have hy'C : Mem y' C := (hC_mem y').mpr ⟨hy'B, n', hn'ω, f', hf', hf'y'⟩
    have ⟨s', hs', _, hf'_d, _, _, hf'_s⟩ := hf'
    have hn_s' : Mem n s' := (hs' n).mpr (Or.inl ((hn'n n).mpr (Or.inr rfl)))
    obtain ⟨yn, hyn⟩ := hf'_d n hn_s'
    have hyEq : yn = y := hchain_uniq n' n f' f n yn y hn'ω hnω hf' hf hnω hyn hfy
    subst hyEq
    have hunion : IsUnion y' yn :=
      hf'_s n n' yn y' ((hn'n n).mpr (Or.inr rfl)) hn'n hyn hf'y'
    have hby' : Mem b y' := (hunion b).mpr ⟨a, hay, hba⟩
    exact (hT b).mpr ⟨y', hy'C, hby'⟩

/-! ### Part 8: Von Neumann hierarchy `V_α` inside `M` -/

private lemma vseq_restrict {s α β a : M} (hs : IsVSeq s α) (ha : IsSucc a α) (hβa : Mem β a) :
    ∃ s' : M, IsVSeq s' β ∧ ∀ γ v : M, PairIn s' γ v ↔ ∃ b : M, IsSucc b β ∧ Mem γ b ∧ PairIn s γ v := by
  obtain ⟨hαOrd, a', ha', hs_p, hs_d, hs_f, hs_r⟩ := hs
  have haEq : a' = a := succ_uniq hM ha' ha
  subst a'
  have haOrd : Ord a := ord_succ hαOrd ha
  have hβOrd : Ord β := ord_mem haOrd hβa
  obtain ⟨b, hb⟩ := succ_ex hM β
  have hb_sub_a : Sub b a := by
    intro γ hγb
    rcases (hb γ).mp hγb with hγβ | rfl
    · exact haOrd.1 β hβa γ hγβ
    · exact hβa
  let φ : SFormula := ex 3 (mem 3 4 ⊓ ex 5 (isPair 0 3 5))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · rcases mem_freeVarFinset_mem h1 with h3 | h4 <;> omega
    · obtain ⟨h2, hne5⟩ := mem_freeVarFinset_ex h2
      rcases fv_isPair h2 with h0 | h3 | h5 <;> omega
  let env : ℕ → M := Function.update (fun _ => s) 4 b
  obtain ⟨s', hs'⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  have hs'_mem : ∀ p : M, Mem p s' ↔ Mem p s ∧ ∃ γ : M, Mem γ b ∧ ∃ v : M, IsPair p γ v := by
    intro p
    rw [hs' p]
    have h1 : env 1 = s := by simp [env]
    rw [h1]
    refine and_congr_right fun _ => ?_
    simp [φ, realize_ex, Formula.realize_inf, realize_mem,
      r_isPair (z := 0) (a := 3) (b := 5) _ (by omega) ⟨by omega, by omega, by omega⟩ ⟨by omega, by omega⟩, env]
  have hs'_pair : ∀ γ v : M, PairIn s' γ v ↔ Mem γ b ∧ PairIn s γ v := by
    intro γ v
    constructor
    · rintro ⟨p, hp, hps'⟩
      obtain ⟨hps, γ', hγ'b, v', hp'⟩ := (hs'_mem p).mp hps'
      have hγeq : γ = γ' := (pair_inj hM hp hp' rfl).1
      subst hγeq
      exact ⟨hγ'b, p, hp, hps⟩
    · rintro ⟨hγb, p, hp, hps⟩
      exact ⟨p, hp, (hs'_mem p).mpr ⟨hps, γ, hγb, v, hp⟩⟩
  refine ⟨s', ⟨hβOrd, b, hb, ?_, ?_, ?_, ?_⟩, fun γ v => ?_⟩
  · intro p hps'
    exact ((hs'_mem p).mp hps').2
  · intro γ hγb
    obtain ⟨v, hv⟩ := hs_d γ (hb_sub_a γ hγb)
    exact ⟨v, (hs'_pair γ v).mpr ⟨hγb, hv⟩⟩
  · intro γ v₁ v₂ h1 h2
    exact hs_f γ v₁ v₂ ((hs'_pair γ v₁).mp h1).2 ((hs'_pair γ v₂).mp h2).2
  · intro γ v hγb hγv z
    have hγv_s : PairIn s γ v := ((hs'_pair γ v).mp hγv).2
    rw [hs_r γ v (hb_sub_a γ hγb) hγv_s z]
    have hbOrd : Ord b := ord_succ hβOrd hb
    constructor
    · rintro ⟨δ, hδγ, u, hδu, hzu⟩
      exact ⟨δ, hδγ, u, (hs'_pair δ u).mpr ⟨hbOrd.1 γ hγb δ hδγ, hδu⟩, hzu⟩
    · rintro ⟨δ, hδγ, u, hδu, hzu⟩
      exact ⟨δ, hδγ, u, ((hs'_pair δ u).mp hδu).2, hzu⟩
  · rw [hs'_pair]
    exact ⟨fun ⟨hγb, h⟩ => ⟨b, hb, hγb, h⟩,
      fun ⟨b', hb', hγb', h⟩ => ⟨(succ_uniq hM hb' hb) ▸ hγb', h⟩⟩

private lemma vseq_uniq {s₁ s₂ α : M} (h₁ : IsVSeq s₁ α) (h₂ : IsVSeq s₂ α) : s₁ = s₂ := by
  obtain ⟨hαOrd, a, ha, h1_p, h1_d, h1_f, h1_r⟩ := h₁
  obtain ⟨_, a₂, ha₂, h2_p, h2_d, h2_f, h2_r⟩ := h₂
  have haEq : a₂ = a := succ_uniq hM ha₂ ha
  subst a₂
  have haOrd : Ord a := ord_succ hαOrd ha
  let φ : SFormula := ex 3 (ex 4 (pairIn 5 0 3 ⊓ pairIn 6 0 4 ⊓ ∼(eq 3 4)))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex h
    obtain ⟨h, hne4⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h12 | h3
    · rcases mem_freeVarFinset_inf h12 with h1 | h2
      · rcases fv_pairIn h1 with h5 | h0 | h3 <;> omega
      · rcases fv_pairIn h2 with h6 | h0 | h4 <;> omega
    · rcases mem_freeVarFinset_eq (mem_freeVarFinset_not h3) with h3' | h4' <;> omega
  let env : ℕ → M := Function.update (Function.update (fun _ => a) 5 s₁) 6 s₂
  obtain ⟨D, hD⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb env
  have hD_mem : ∀ γ : M, Mem γ D ↔ Mem γ a ∧ ∃ v₁ v₂ : M, PairIn s₁ γ v₁ ∧ PairIn s₂ γ v₂ ∧ v₁ ≠ v₂ := by
    intro γ
    rw [hD γ]
    have h1 : env 1 = a := by simp [env]
    rw [h1]
    refine and_congr_right fun _ => ?_
    simp only [φ, realize_ex, Formula.realize_inf, Formula.realize_not, realize_eq,
      r_pairIn (f := 5) (a := 0) (b := 3) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩,
      r_pairIn (f := 6) (a := 0) (b := 4) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩, env]
    simp [and_assoc]
  have hD_emp : ∀ γ : M, ¬ Mem γ D := by
    intro γ₀ hγ₀
    obtain ⟨γ, hγD, hmin⟩ := ax_found hM D ⟨γ₀, hγ₀⟩
    obtain ⟨hγa, v₁, v₂, hv₁, hv₂, hne⟩ := (hD_mem γ).mp hγD
    apply hne
    apply ax_ext hM v₁ v₂
    intro z
    rw [h1_r γ v₁ hγa hv₁ z, h2_r γ v₂ hγa hv₂ z]
    have hagree : ∀ δ u₁ u₂ : M, Mem δ γ → PairIn s₁ δ u₁ → PairIn s₂ δ u₂ → u₁ = u₂ := by
      intro δ u₁ u₂ hδγ hu₁ hu₂
      by_contra hune
      have hδD : Mem δ D := (hD_mem δ).mpr ⟨haOrd.1 γ hγa δ hδγ, u₁, u₂, hu₁, hu₂, hune⟩
      exact hmin δ ⟨hδγ, hδD⟩
    constructor
    · rintro ⟨δ, hδγ, u₁, hu₁, hzu⟩
      obtain ⟨u₂, hu₂⟩ := h2_d δ (haOrd.1 γ hγa δ hδγ)
      have heq := hagree δ u₁ u₂ hδγ hu₁ hu₂
      exact ⟨δ, hδγ, u₂, hu₂, heq ▸ hzu⟩
    · rintro ⟨δ, hδγ, u₂, hu₂, hzu⟩
      obtain ⟨u₁, hu₁⟩ := h1_d δ (haOrd.1 γ hγa δ hδγ)
      have heq := hagree δ u₁ u₂ hδγ hu₁ hu₂
      exact ⟨δ, hδγ, u₁, hu₁, heq.symm ▸ hzu⟩
  apply ax_ext hM s₁ s₂
  intro p
  constructor
  · intro hp1
    obtain ⟨γ, hγa, v₁, hpv₁⟩ := h1_p p hp1
    obtain ⟨v₂, p₂, hp₂, hp₂s2⟩ := h2_d γ hγa
    have hvEq : v₁ = v₂ := by
      by_contra hne
      exact hD_emp γ ((hD_mem γ).mpr ⟨hγa, v₁, v₂, ⟨p, hpv₁, hp1⟩, ⟨p₂, hp₂, hp₂s2⟩, hne⟩)
    subst hvEq
    have hpEq : p = p₂ := ax_ext hM p p₂ fun w => (hpv₁ w).trans (hp₂ w).symm
    exact hpEq ▸ hp₂s2
  · intro hp2
    obtain ⟨γ, hγa, v₂, hpv₂⟩ := h2_p p hp2
    obtain ⟨v₁, p₁, hp₁, hp₁s1⟩ := h1_d γ hγa
    have hvEq : v₁ = v₂ := by
      by_contra hne
      exact hD_emp γ ((hD_mem γ).mpr ⟨hγa, v₁, v₂, ⟨p₁, hp₁, hp₁s1⟩, ⟨p, hpv₂, hp2⟩, hne⟩)
    subst hvEq
    have hpEq : p = p₁ := ax_ext hM p p₁ fun w => (hpv₂ w).trans (hp₁ w).symm
    exact hpEq ▸ hp₁s1

private lemma vseq_agree {s₁ s₂ α₁ α₂ γ v₁ v₂ : M}
    (h₁ : IsVSeq s₁ α₁) (h₂ : IsVSeq s₂ α₂) (hp₁ : PairIn s₁ γ v₁) (hp₂ : PairIn s₂ γ v₂) :
    v₁ = v₂ := by
  have ⟨_, a₁, ha₁, h1_p, _, _, _⟩ := h₁
  have ⟨_, a₂, ha₂, h2_p, _, _, _⟩ := h₂
  have hγa1 : Mem γ a₁ := by
    obtain ⟨p, hp, hps⟩ := hp₁
    obtain ⟨γ', hγ', _, hp'⟩ := h1_p p hps
    rwa [(pair_inj hM hp hp' rfl).1]
  have hγa2 : Mem γ a₂ := by
    obtain ⟨p, hp, hps⟩ := hp₂
    obtain ⟨γ', hγ', _, hp'⟩ := h2_p p hps
    rwa [(pair_inj hM hp hp' rfl).1]
  obtain ⟨r₁, hr₁, hr₁_p⟩ := vseq_restrict hM h₁ ha₁ hγa1
  obtain ⟨r₂, hr₂, hr₂_p⟩ := vseq_restrict hM h₂ ha₂ hγa2
  have hrEq : r₁ = r₂ := vseq_uniq hM hr₁ hr₂
  subst hrEq
  obtain ⟨b, hb⟩ := succ_ex hM γ
  have hp1' : PairIn r₁ γ v₁ := (hr₁_p γ v₁).mpr ⟨b, hb, (hb γ).mpr (Or.inr rfl), hp₁⟩
  have hp2' : PairIn r₁ γ v₂ := (hr₂_p γ v₂).mpr ⟨b, hb, (hb γ).mpr (Or.inr rfl), hp₂⟩
  exact hr₁.2.choose_spec.2.2.2.1 γ v₁ v₂ hp1' hp2'

private lemma vseq_ex {α : M} (hα : Ord α) : ∃ s : M, IsVSeq s α := by
  by_contra hno
  obtain ⟨a, ha⟩ := succ_ex hM α
  have haOrd : Ord a := ord_succ hα ha
  let φ : SFormula := ∼(ex 3 (isVSeqF 3 0))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex (mem_freeVarFinset_not h)
    rcases fv_isVSeqF h with h3 | h0 <;> omega
  obtain ⟨B, hB⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb (fun _ => a)
  have hB_mem : ∀ γ : M, Mem γ B ↔ Mem γ a ∧ ¬ ∃ s : M, IsVSeq s γ := fun γ => by
    simpa [φ, realize_ex, r_isVSeqF (s := 3) (α := 0) _ (Or.inl (by omega)) (by omega)] using hB γ
  have hαB : Mem α B := (hB_mem α).mpr ⟨(ha α).mpr (Or.inr rfl), hno⟩
  obtain ⟨γ₀, hγ₀B, hmin⟩ := ax_found hM B ⟨α, hαB⟩
  obtain ⟨hγ₀a, hγ₀no⟩ := (hB_mem γ₀).mp hγ₀B
  have hγ₀Ord : Ord γ₀ := ord_mem haOrd hγ₀a
  have hprev_ex : ∀ δ : M, Mem δ γ₀ → ∃ s : M, IsVSeq s δ := by
    intro δ hδγ₀
    by_contra hδno
    have hδB : Mem δ B := (hB_mem δ).mpr ⟨haOrd.1 γ₀ hγ₀a δ hδγ₀, hδno⟩
    exact hmin δ ⟨hδγ₀, hδB⟩
  -- Collect `s_δ` for all `δ ∈ γ₀` via `ax_coll`.
  have hhb_c : (3 : ℕ) ∉ (isVSeqF 1 0).freeVarFinset := fun h => by
    rcases fv_isVSeqF h with h1 | h0 <;> omega
  have htot_c : ∀ δ : M, Mem δ γ₀ →
      ∃ s : M, Formula.Realize (isVSeqF 1 0) (Function.update (Function.update (fun _ => γ₀) 0 δ) 1 s) := by
    intro δ hδ
    obtain ⟨s, hs⟩ := hprev_ex δ hδ
    exact ⟨s, by simpa [r_isVSeqF (s := 1) (α := 0) _ (Or.inl (by omega)) (by omega)] using hs⟩
  obtain ⟨C₀, hC₀⟩ := ax_coll hM (isVSeqF 1 0) 0 1 2 3 (by decide) hhb_c (fun _ => γ₀) htot_c
  let φC : SFormula := ex 0 (mem 0 4 ⊓ isVSeqF 1 0)
  have hhb_C : (3 : ℕ) ∉ φC.freeVarFinset := fun h => by
    obtain ⟨h, hne0⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · rcases mem_freeVarFinset_mem h1 with h0 | h4 <;> omega
    · rcases fv_isVSeqF h2 with h1' | h0 <;> omega
  let envC : ℕ → M := Function.update (fun _ => C₀) 4 γ₀
  obtain ⟨C, hC⟩ := ax_sep hM φC 1 2 3 (by omega) (by omega) (by omega) hhb_C envC
  have hC_mem : ∀ s : M, Mem s C ↔ Mem s C₀ ∧ ∃ δ : M, Mem δ γ₀ ∧ IsVSeq s δ := fun s => by
    rw [hC s]
    have h2 : envC 2 = C₀ := by simp [envC]
    rw [h2]
    refine and_congr_right fun _ => ?_
    simp [φC, realize_ex, Formula.realize_inf, realize_mem,
      r_isVSeqF (s := 1) (α := 0) _ (Or.inl (by omega)) (by omega), envC]
  obtain ⟨s_prev, hs_prev⟩ := ax_union hM C
  have hs_prev_pair : ∀ δ u : M, PairIn s_prev δ u →
      ∃ η s : M, Mem η γ₀ ∧ IsVSeq s η ∧ PairIn s δ u := by
    rintro δ u ⟨p, hp, hpsp⟩
    obtain ⟨s, hsC, hps⟩ := (hs_prev p).mp hpsp
    obtain ⟨_, η, hηγ₀, hsη⟩ := (hC_mem s).mp hsC
    exact ⟨η, s, hηγ₀, hsη, p, hp, hps⟩
  have hs_prev_dom : ∀ δ : M, Mem δ γ₀ → ∃ u : M, PairIn s_prev δ u := by
    intro δ hδγ₀
    obtain ⟨s, hsC₀, hsφ⟩ := hC₀ δ hδγ₀
    have hsδ : IsVSeq s δ := by
      simpa [r_isVSeqF (s := 1) (α := 0) _ (Or.inl (by omega)) (by omega)] using hsφ
    have hsC : Mem s C := (hC_mem s).mpr ⟨hsC₀, δ, hδγ₀, hsδ⟩
    obtain ⟨_, d, hd, _, hs_d, _, _⟩ := hsδ
    obtain ⟨u, p, hp, hps⟩ := hs_d δ ((hd δ).mpr (Or.inr rfl))
    exact ⟨u, p, hp, (hs_prev p).mpr ⟨s, hsC, hps⟩⟩
  have hs_prev_fun : ∀ δ u₁ u₂ : M, PairIn s_prev δ u₁ → PairIn s_prev δ u₂ → u₁ = u₂ := by
    intro δ u₁ u₂ h1 h2
    obtain ⟨η₁, s₁, _, hs₁, hp₁⟩ := hs_prev_pair δ u₁ h1
    obtain ⟨η₂, s₂, _, hs₂, hp₂⟩ := hs_prev_pair δ u₂ h2
    exact vseq_agree hM hs₁ hs₂ hp₁ hp₂
  have hs_prev_mem : ∀ p : M, Mem p s_prev → ∃ δ : M, Mem δ γ₀ ∧ ∃ u : M, IsPair p δ u := by
    intro p hpsp
    obtain ⟨s, hsC, hps⟩ := (hs_prev p).mp hpsp
    obtain ⟨_, η, hηγ₀, hsη⟩ := (hC_mem s).mp hsC
    obtain ⟨_, d, hd, hs_p, _, _, _⟩ := hsη
    obtain ⟨δ, hδd, u, hp⟩ := hs_p p hps
    have hδγ₀ : Mem δ γ₀ := by
      rcases (hd δ).mp hδd with hδη | rfl
      · exact hγ₀Ord.1 η hηγ₀ δ hδη
      · exact hηγ₀
    exact ⟨δ, hδγ₀, u, hp⟩
  -- Build `V_{γ₀} = ⋃_{δ ∈ γ₀} 𝒫(s_prev(δ))` via Collection + Separation + Union.
  let φP : SFormula := ex 5 (pairIn 6 0 5 ⊓ isPowerset 1 5)
  have hhb_P : (3 : ℕ) ∉ φP.freeVarFinset := fun h => by
    obtain ⟨h, hne5⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · rcases fv_pairIn h1 with h6 | h0 | h5 <;> omega
    · rcases fv_isPowerset h2 with h1' | h5 <;> omega
  let envP : ℕ → M := Function.update (fun _ => γ₀) 6 s_prev
  have htot_P : ∀ δ : M, Mem δ (envP 2) →
      ∃ p : M, Formula.Realize φP (Function.update (Function.update envP 0 δ) 1 p) := by
    intro δ hδ
    have hδγ₀ : Mem δ γ₀ := by simpa [envP] using hδ
    obtain ⟨u, hu⟩ := hs_prev_dom δ hδγ₀
    obtain ⟨p, hp⟩ := ax_powerset hM u
    refine ⟨p, ?_⟩
    simp only [φP, realize_ex, Formula.realize_inf,
      r_pairIn (f := 6) (a := 0) (b := 5) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩,
      r_isPowerset (p := 1) (x := 5) _ (by omega) (by omega) (by omega)]
    exact ⟨u, by simpa [envP] using hu, by simpa [envP] using hp⟩
  obtain ⟨P₀, hP₀⟩ := ax_coll hM φP 0 1 2 3 (by decide) hhb_P envP htot_P
  let φP' : SFormula := ex 0 (mem 0 7 ⊓ ex 5 (pairIn 6 0 5 ⊓ isPowerset 1 5))
  have hhb_P' : (4 : ℕ) ∉ φP'.freeVarFinset := fun h => by
    obtain ⟨h, hne0⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · rcases mem_freeVarFinset_mem h1 with h0 | h7 <;> omega
    · obtain ⟨h2, hne5⟩ := mem_freeVarFinset_ex h2
      rcases mem_freeVarFinset_inf h2 with h3 | h4
      · rcases fv_pairIn h3 with h6 | h0 | h5 <;> omega
      · rcases fv_isPowerset h4 with h1' | h5 <;> omega
  let envP' : ℕ → M := Function.update (Function.update (fun _ => P₀) 7 γ₀) 6 s_prev
  obtain ⟨P, hP⟩ := ax_sep hM φP' 1 2 4 (by omega) (by omega) (by omega) hhb_P' envP'
  have hP_mem : ∀ p : M, Mem p P ↔ Mem p P₀ ∧ ∃ δ : M, Mem δ γ₀ ∧ ∃ u : M, PairIn s_prev δ u ∧ IsPow p u := by
    intro p
    rw [hP p]
    have h2 : envP' 2 = P₀ := by simp [envP']
    rw [h2]
    refine and_congr_right fun _ => ?_
    simp [φP', realize_ex, Formula.realize_inf, realize_mem,
      r_pairIn (f := 6) (a := 0) (b := 5) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
        ⟨by omega, by omega, by omega⟩,
      r_isPowerset (p := 1) (x := 5) _ (by omega) (by omega) (by omega), envP']
  obtain ⟨V0, hV0⟩ := ax_union hM P
  have hV0_mem : ∀ z : M, Mem z V0 ↔ ∃ δ : M, Mem δ γ₀ ∧ ∃ u : M, PairIn s_prev δ u ∧ Sub z u := by
    intro z
    rw [hV0]
    constructor
    · rintro ⟨p, hpP, hzp⟩
      obtain ⟨_, δ, hδγ₀, u, hδu, hpu⟩ := (hP_mem p).mp hpP
      exact ⟨δ, hδγ₀, u, hδu, (hpu z).mp hzp⟩
    · rintro ⟨δ, hδγ₀, u, hδu, hzu⟩
      obtain ⟨p, hpP₀, hpφ⟩ := hP₀ δ (by simpa [envP] using hδγ₀)
      simp only [φP, realize_ex, Formula.realize_inf,
        r_pairIn (f := 6) (a := 0) (b := 5) _ (by omega) ⟨by omega, by omega, by omega, by omega⟩
          ⟨by omega, by omega, by omega⟩,
        r_isPowerset (p := 1) (x := 5) _ (by omega) (by omega) (by omega), envP, Function.update_self,
        Function.update_of_ne (by omega : (0 : ℕ) ≠ 5),
        Function.update_of_ne (by omega : (0 : ℕ) ≠ 1),
        Function.update_of_ne (by omega : (1 : ℕ) ≠ 5),
        Function.update_of_ne (by omega : (6 : ℕ) ≠ 5),
        Function.update_of_ne (by omega : (6 : ℕ) ≠ 1),
        Function.update_of_ne (by omega : (6 : ℕ) ≠ 0)] at hpφ
      obtain ⟨u', hδu', hpu'⟩ := hpφ
      have huEq : u' = u := hs_prev_fun δ u' u hδu' hδu
      subst huEq
      exact ⟨p, (hP_mem p).mpr ⟨hpP₀, δ, hδγ₀, u', hδu', hpu'⟩, (hpu' z).mpr hzu⟩
  -- Extend `s_prev` by `(γ₀, V0)`.
  obtain ⟨a₀, ha₀⟩ := succ_ex hM γ₀
  obtain ⟨q0, hq0⟩ := pair_ex hM γ₀ V0
  obtain ⟨sq0, hsq0⟩ := sing_ex hM q0
  obtain ⟨s_new, hs_new⟩ := binUnion_ex hM s_prev sq0
  have hs_new_mem : ∀ q : M, Mem q s_new ↔ Mem q s_prev ∨ q = q0 := fun q => by
    rw [hs_new, hsq0]
  have hs_new_pair : ∀ γ v : M, PairIn s_new γ v ↔ PairIn s_prev γ v ∨ (γ = γ₀ ∧ v = V0) := by
    intro γ v
    constructor
    · rintro ⟨q, hq, hqs⟩
      rcases (hs_new_mem q).mp hqs with hqp | rfl
      · exact Or.inl ⟨q, hq, hqp⟩
      · exact Or.inr (pair_inj hM hq hq0 rfl)
    · rintro (⟨q, hq, hqp⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, hq, (hs_new_mem q).mpr (Or.inl hqp)⟩
      · exact ⟨q0, hq0, (hs_new_mem q0).mpr (Or.inr rfl)⟩
  have hγ₀_not_prev : ∀ v : M, ¬ PairIn s_prev γ₀ v := by
    rintro v ⟨q, hq, hqp⟩
    obtain ⟨δ, hδγ₀, u, hqu⟩ := hs_prev_mem q hqp
    have heq : γ₀ = δ := (pair_inj hM hq hqu rfl).1
    subst δ
    exact mem_irrefl hM γ₀ hδγ₀
  apply hγ₀no
  refine ⟨s_new, hγ₀Ord, a₀, ha₀, ?_, ?_, ?_, ?_⟩
  · intro q hqs
    rcases (hs_new_mem q).mp hqs with hqp | rfl
    · obtain ⟨δ, hδγ₀, u, hqu⟩ := hs_prev_mem q hqp
      exact ⟨δ, (ha₀ δ).mpr (Or.inl hδγ₀), u, hqu⟩
    · exact ⟨γ₀, (ha₀ γ₀).mpr (Or.inr rfl), V0, hq0⟩
  · intro γ hγa₀
    rcases (ha₀ γ).mp hγa₀ with hγγ₀ | hγeq
    · obtain ⟨u, hu⟩ := hs_prev_dom γ hγγ₀
      exact ⟨u, (hs_new_pair γ u).mpr (Or.inl hu)⟩
    · subst γ
      exact ⟨V0, (hs_new_pair γ₀ V0).mpr (Or.inr ⟨rfl, rfl⟩)⟩
  · intro γ v₁ v₂ h1 h2
    rcases (hs_new_pair γ v₁).mp h1 with h1p | ⟨hγeq, rfl⟩
    · rcases (hs_new_pair γ v₂).mp h2 with h2p | ⟨hγeq, rfl⟩
      · exact hs_prev_fun γ v₁ v₂ h1p h2p
      · subst γ; exact absurd h1p (hγ₀_not_prev v₁)
    · subst γ
      rcases (hs_new_pair γ₀ v₂).mp h2 with h2p | ⟨_, rfl⟩
      · exact absurd h2p (hγ₀_not_prev v₂)
      · rfl
  · intro γ v hγa₀ hγv z
    rcases (ha₀ γ).mp hγa₀ with hγγ₀ | hγeq
    · have hγne : γ ≠ γ₀ := fun h => mem_irrefl hM γ₀ (h ▸ hγγ₀)
      have hγvp : PairIn s_prev γ v := by
        rcases (hs_new_pair γ v).mp hγv with h | ⟨h, _⟩
        · exact h
        · exact absurd h hγne
      obtain ⟨η, sη, hηγ₀, hsη, hγvs⟩ := hs_prev_pair γ v hγvp
      have ⟨_, dη, hdη, hsη_p, hsη_d, _, hsη_r⟩ := hsη
      have hγdη : Mem γ dη := by
        obtain ⟨q, hq, hqs⟩ := hγvs
        obtain ⟨γ', hγ', _, hq'⟩ := hsη_p q hqs
        rwa [(pair_inj hM hq hq' rfl).1]
      rw [hsη_r γ v hγdη hγvs z]
      constructor
      · rintro ⟨δ, hδγ, u, hδu, hzu⟩
        have hδγ₀ : Mem δ γ₀ := hγ₀Ord.1 γ hγγ₀ δ hδγ
        obtain ⟨u', hδu'⟩ := hs_prev_dom δ hδγ₀
        obtain ⟨η', sη', _, hsη', hδu's⟩ := hs_prev_pair δ u' hδu'
        have huEq : u' = u := vseq_agree hM hsη' hsη hδu's hδu
        subst huEq
        exact ⟨δ, hδγ, u', (hs_new_pair δ u').mpr (Or.inl hδu'), hzu⟩
      · rintro ⟨δ, hδγ, u, hδu, hzu⟩
        have hδγ₀ : Mem δ γ₀ := hγ₀Ord.1 γ hγγ₀ δ hδγ
        have hδne : δ ≠ γ₀ := fun h => mem_irrefl hM γ₀ (h ▸ hδγ₀)
        have hδup : PairIn s_prev δ u := by
          rcases (hs_new_pair δ u).mp hδu with h | ⟨h, _⟩
          · exact h
          · exact absurd h hδne
        obtain ⟨η', sη', _, hsη', hδus'⟩ := hs_prev_pair δ u hδup
        have hdηOrd : Ord dη := ord_succ (ord_mem hγ₀Ord hηγ₀) hdη
        obtain ⟨u', hδu'⟩ := hsη_d δ (hdηOrd.1 γ hγdη δ hδγ)
        have huEq : u' = u := vseq_agree hM hsη hsη' hδu' hδus'
        subst huEq
        exact ⟨δ, hδγ, u', hδu', hzu⟩
    · subst γ
      have hvEq : v = V0 := by
        rcases (hs_new_pair γ₀ v).mp hγv with h | ⟨_, rfl⟩
        · exact absurd h (hγ₀_not_prev v)
        · rfl
      subst hvEq
      rw [hV0_mem z]
      constructor
      · rintro ⟨δ, hδγ₀, u, hδu, hzu⟩
        exact ⟨δ, hδγ₀, u, (hs_new_pair δ u).mpr (Or.inl hδu), hzu⟩
      · rintro ⟨δ, hδγ₀, u, hδu, hzu⟩
        have hδne : δ ≠ γ₀ := fun h => mem_irrefl hM γ₀ (h ▸ hδγ₀)
        rcases (hs_new_pair δ u).mp hδu with h | ⟨h, _⟩
        · exact ⟨δ, hδγ₀, u, h, hzu⟩
        · exact absurd h hδne

private lemma vat_ex {α : M} (hα : Ord α) : ∃ v : M, IsVAt v α := by
  obtain ⟨s, hs⟩ := vseq_ex hM hα
  have ⟨_, a, ha, _, hs_d, _, _⟩ := hs
  obtain ⟨v, hv⟩ := hs_d α ((ha α).mpr (Or.inr rfl))
  exact ⟨v, hα, s, hs, hv⟩

private lemma vat_uniq {v₁ v₂ α : M} (h₁ : IsVAt v₁ α) (h₂ : IsVAt v₂ α) : v₁ = v₂ := by
  obtain ⟨_, s₁, hs₁, hp₁⟩ := h₁
  obtain ⟨_, s₂, hs₂, hp₂⟩ := h₂
  exact vseq_agree hM hs₁ hs₂ hp₁ hp₂

private lemma vat_mem_iff {v α z : M} (hv : IsVAt v α) :
    Mem z v ↔ ∃ δ : M, Mem δ α ∧ ∃ u : M, IsVAt u δ ∧ Sub z u := by
  obtain ⟨hαOrd, s, hs, hps⟩ := hv
  have ⟨_, a, ha, _, hs_d, _, hs_r⟩ := hs
  have hαa : Mem α a := (ha α).mpr (Or.inr rfl)
  rw [hs_r α v hαa hps z]
  constructor
  · rintro ⟨δ, hδα, u, hδu, hzu⟩
    have hδOrd : Ord δ := ord_mem hαOrd hδα
    obtain ⟨r, hr, hr_p⟩ := vseq_restrict hM hs ha ((ha δ).mpr (Or.inl hδα))
    obtain ⟨b, hb⟩ := succ_ex hM δ
    exact ⟨δ, hδα, u, ⟨hδOrd, r, hr, (hr_p δ u).mpr ⟨b, hb, (hb δ).mpr (Or.inr rfl), hδu⟩⟩, hzu⟩
  · rintro ⟨δ, hδα, u, ⟨_, r, hr, hru⟩, hzu⟩
    obtain ⟨u', hδu'⟩ := hs_d δ ((ha δ).mpr (Or.inl hδα))
    have huEq : u' = u := vseq_agree hM hs hr hδu' hru
    subst huEq
    exact ⟨δ, hδα, u', hδu', hzu⟩

private lemma every_set_in_V [Nonempty M] (x : M) : ∃ α v : M, IsVAt v α ∧ Mem x v := by
  by_contra hno
  obtain ⟨T, hxT, hTtrans⟩ := exists_transitive_superset hM x
  let φ : SFormula := ∼(ex 3 (ex 4 (isVAtF 4 3 ⊓ mem 0 4)))
  have hhb : (2 : ℕ) ∉ φ.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_ex (mem_freeVarFinset_not h)
    obtain ⟨h, hne4⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · rcases fv_isVAtF h1 with h4 | h3 <;> omega
    · rcases mem_freeVarFinset_mem h2 with h0 | h4 <;> omega
  obtain ⟨D, hD⟩ := ax_sep hM φ 0 1 2 (by omega) (by omega) (by omega) hhb (fun _ => T)
  have hD_mem : ∀ y : M, Mem y D ↔ Mem y T ∧ ¬ ∃ α v : M, IsVAt v α ∧ Mem y v := fun y => by
    simpa [φ, realize_ex, Formula.realize_inf, realize_mem,
      r_isVAtF (v := 4) (α := 3) _ (by omega) (by omega)] using hD y
  obtain ⟨y, hyD, hmin⟩ := ax_found hM D ⟨x, (hD_mem x).mpr ⟨hxT, hno⟩⟩
  obtain ⟨hyT, hyno⟩ := (hD_mem y).mp hyD
  have hy_elem : ∀ z : M, Mem z y → ∃ α v : M, IsVAt v α ∧ Mem z v := by
    intro z hzy
    by_contra hzno
    have hzD : Mem z D := (hD_mem z).mpr ⟨hTtrans y hyT z hzy, hzno⟩
    exact hmin z ⟨hzy, hzD⟩
  -- Collect ordinals `α` for all `z ∈ y`.
  let ψ : SFormula := ex 4 (isVAtF 4 1 ⊓ mem 0 4)
  have hhb_c : (3 : ℕ) ∉ ψ.freeVarFinset := fun h => by
    obtain ⟨h, hne4⟩ := mem_freeVarFinset_ex h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · rcases fv_isVAtF h1 with h4 | h1' <;> omega
    · rcases mem_freeVarFinset_mem h2 with h0 | h4 <;> omega
  have htot : ∀ z : M, Mem z y →
      ∃ α : M, Formula.Realize ψ (Function.update (Function.update (fun _ => y) 0 z) 1 α) := by
    intro z hzy
    obtain ⟨α, v, hv, hzv⟩ := hy_elem z hzy
    refine ⟨α, ?_⟩
    simp only [ψ, realize_ex, Formula.realize_inf, realize_mem,
      r_isVAtF (v := 4) (α := 1) _ (by omega) (by omega)]
    exact ⟨v, by simpa using hv, by simpa using hzv⟩
  obtain ⟨A₀, hA₀⟩ := ax_coll hM ψ 0 1 2 3 (by decide) hhb_c (fun _ => y) htot
  have hhb_A : (2 : ℕ) ∉ (isOrdF 0).freeVarFinset := fun h => by
    have := fv_isOrdF h; omega
  obtain ⟨A, hA⟩ := ax_sep hM (isOrdF 0) 0 1 2 (by omega) (by omega) (by omega) hhb_A (fun _ => A₀)
  have hA_mem : ∀ α : M, Mem α A ↔ Mem α A₀ ∧ Ord α := fun α => by
    simpa [r_isOrdF (α := 0) _ ⟨by omega, by omega, by omega⟩] using hA α
  obtain ⟨β, hβ⟩ := ax_union hM A
  have hβOrd : Ord β := ord_union (fun α hαA => ((hA_mem α).mp hαA).2) hβ
  obtain ⟨γ, hγβ⟩ := succ_ex hM β
  have hγOrd : Ord γ := ord_succ hβOrd hγβ
  obtain ⟨Vβ, hVβ⟩ := vat_ex hM hβOrd
  obtain ⟨Vγ, hVγ⟩ := vat_ex hM hγOrd
  have hy_sub_Vβ : Sub y Vβ := by
    intro z hzy
    obtain ⟨α, hαA₀, hαψ⟩ := hA₀ z hzy
    simp only [ψ, realize_ex, Formula.realize_inf, realize_mem,
      r_isVAtF (v := 4) (α := 1) _ (by omega) (by omega),
      Function.update_self, Function.update_of_ne (by omega : (0 : ℕ) ≠ 4),
      Function.update_of_ne (by omega : (0 : ℕ) ≠ 1),
      Function.update_of_ne (by omega : (1 : ℕ) ≠ 4)] at hαψ
    obtain ⟨Vα, hVα, hzVα⟩ := hαψ
    have hαA : Mem α A := (hA_mem α).mpr ⟨hαA₀, hVα.1⟩
    obtain ⟨δ, hδα, u, hu, hzu⟩ := (vat_mem_iff hM hVα).mp hzVα
    have hδβ : Mem δ β := (hβ δ).mpr ⟨α, hαA, hδα⟩
    exact (vat_mem_iff hM hVβ).mpr ⟨δ, hδβ, u, hu, hzu⟩
  have hyVγ : Mem y Vγ := (vat_mem_iff hM hVγ).mpr ⟨β, (hγβ β).mpr (Or.inr rfl), Vβ, hVβ, hy_sub_Vβ⟩
  exact hyno ⟨γ, Vγ, hVγ, hyVγ⟩

/-! ### Part 9: The critical-point contradiction -/

private lemma contradiction_of_fixes_ordinals [Nonempty M] : False := by
  obtain ⟨x₀, hx₀⟩ := ax_nontriv hM
  obtain ⟨α₀, v₀, hv₀, hx₀v₀⟩ := every_set_in_V hM x₀
  obtain ⟨a₀, ha₀⟩ := succ_ex hM α₀
  have ha₀Ord : Ord a₀ := ord_succ hv₀.1 ha₀
  -- `E = {γ ∈ succ α₀ | ∃ v x, IsVAt v γ ∧ x ∈ v ∧ j(x) ≠ x}`
  let φE : SFormulaJ :=
    exJ 3 (exJ 4 (incl.onBoundedFormula (isVAtF 3 0 ⊓ mem 4 3) ⊓
      ∼(Term.equal (jTerm 4) (Term.var 4))))
  have hhb_E : (2 : ℕ) ∉ φE.freeVarFinset := fun h => by
    obtain ⟨h, hne3⟩ := mem_freeVarFinset_exJ h
    obtain ⟨h, hne4⟩ := mem_freeVarFinset_exJ h
    rcases mem_freeVarFinset_inf h with h1 | h2
    · have h1' := mem_freeVarFinset_onBoundedFormula incl _ h1
      rcases mem_freeVarFinset_inf h1' with ha | hb
      · rcases fv_isVAtF ha with h3 | h0 <;> omega
      · rcases mem_freeVarFinset_mem hb with h4 | h3 <;> omega
    · rcases mem_freeVarFinset_jEq (mem_freeVarFinset_not h2) with h4 | h4' <;> omega
  obtain ⟨E, hE⟩ := ax_sepJ hM φE 0 1 2 (by omega) (by omega) (by omega) hhb_E (fun _ => a₀)
  have hE_mem : ∀ γ : M, Mem γ E ↔ Mem γ a₀ ∧ ∃ v x : M, IsVAt v γ ∧ Mem x v ∧ jVal x ≠ x := by
    intro γ
    rw [hE γ]
    refine and_congr_right fun _ => ?_
    simp only [φE, realize_exJ, Formula.realize_inf, Formula.realize_not,
      realize_onBoundedFormula_formula, realize_mem, Formula.realize_equal, realize_jTerm,
      Term.realize_var, r_isVAtF (v := 3) (α := 0) _ (by omega) (by omega)]
    simp [and_assoc]
  have hα₀E : Mem α₀ E := (hE_mem α₀).mpr ⟨(ha₀ α₀).mpr (Or.inr rfl), v₀, x₀, hv₀, hx₀v₀, hx₀⟩
  obtain ⟨γ, hγE, hmin⟩ := ax_found hM E ⟨α₀, hα₀E⟩
  obtain ⟨hγa₀, v, x, hvγ, hxv, hjx_ne⟩ := (hE_mem γ).mp hγE
  obtain ⟨δ, hδγ, u, huδ, hxu⟩ := (vat_mem_iff hM hvγ).mp hxv
  -- By minimality of `γ`, `j` fixes every element of `u = V_δ`.
  have hfix_u : ∀ w : M, Mem w u → jVal w = w := by
    intro w hwu
    by_contra hjw_ne
    have hδE : Mem δ E := (hE_mem δ).mpr ⟨ha₀Ord.1 γ hγa₀ δ hδγ, u, w, huδ, hwu, hjw_ne⟩
    exact hmin δ ⟨hδγ, hδE⟩
  -- Since `δ` is an ordinal, `j(δ) = δ`; by elementarity `j(u) = u` and `j(x) ⊆ u`.
  have hjδ : jVal δ = δ := ax_fixesOrd hM δ huδ.1
  have hju_vat : IsVAt (jVal u) (jVal δ) := by
    have hel := (ax_elem hM (isVAtF 0 1) (Function.update (fun _ => δ) 0 u)).mp
    have h0 : Formula.Realize (isVAtF 0 1) (Function.update (fun _ => δ) 0 u) := by
      simpa [r_isVAtF (v := 0) (α := 1) _ (by omega) (by omega)] using huδ
    have h1 := hel h0
    simpa [r_isVAtF (v := 0) (α := 1) _ (by omega) (by omega), Function.comp] using h1
  rw [hjδ] at hju_vat
  have hju : jVal u = u := vat_uniq hM hju_vat huδ
  have hjx_sub_u : Sub (jVal x) u := by
    have hel := (ax_elem hM (subset 0 1) (Function.update (fun _ => u) 0 x)).mp
    have h0 : Formula.Realize (subset 0 1) (Function.update (fun _ => u) 0 x) := by
      simpa [r_subset (x := 0) (y := 1) _ (by omega) (by omega)] using hxu
    have h1 := hel h0
    have h2 : Sub (jVal x) (jVal u) := by
      simpa [r_subset (x := 0) (y := 1) _ (by omega) (by omega), Function.comp] using h1
    rwa [hju] at h2
  -- Every `w` in `x` or `j(x)` belongs to `u`, hence `j(w) = w`; by elementarity `x = j(x)`.
  have hmem_elem : ∀ w : M, Mem w x ↔ Mem (jVal w) (jVal x) := by
    intro w
    have hel := ax_elem hM (mem 0 1) (Function.update (fun _ => x) 0 w)
    simpa [realize_mem, Function.comp] using hel
  have hjx_eq : jVal x = x := by
    apply ax_ext hM (jVal x) x
    intro w
    constructor
    · intro hwjx
      have hwu : Mem w u := hjx_sub_u w hwjx
      have hjw : jVal w = w := hfix_u w hwu
      exact (hmem_elem w).mpr (hjw.symm ▸ hwjx)
    · intro hwx
      have hwu : Mem w u := hxu w hwx
      have hjw : jVal w = w := hfix_u w hwu
      exact hjw ▸ (hmem_elem w).mp hwx
  exact hjx_ne hjx_eq

end Semantics

end KunenZFProof

theorem solution {M : Type u} [setLangJ.Structure M] [Nonempty M] :
    ¬ (M ⊨ (reinhardtTheory ∪ {SFormulaJ.closeJ fixesOrdinalsFormula})) :=
  fun hM => KunenZFProof.contradiction_of_fixes_ordinals hM
