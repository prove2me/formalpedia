-- Prove2me | solution 1 for MatchingLogic.two_copies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:22:48.887947+00:00
-- url     : https://prove2.me/submissions/88d4de4f-e574-4b6c-b453-efbaaf00253c

module
public import Definitions.Def_LeanPool_MatchingLogic_Core
public import Mathlib.Data.Set.Basic
public import Definitions.Def_LeanPool_MatchingLogic_Locality
public import Mathlib.Data.Set.Insert
public import Definitions.Def_LeanPool_MatchingLogic_DoubleCover
public import Theorems.Thm_MatchingLogic_AgreeOn_update
public import Theorems.Thm_MatchingLogic_Model_BackwardClosed_mem_of_interp
public import Theorems.Thm_MatchingLogic_denote_app
public import Theorems.Thm_MatchingLogic_denote_bot
public import Theorems.Thm_MatchingLogic_denote_ex
public import Theorems.Thm_MatchingLogic_denote_imp
public import Theorems.Thm_MatchingLogic_denote_var
public import Theorems.Thm_MatchingLogic_locality
attribute [local simp] MatchingLogic.denote_app
attribute [local simp] MatchingLogic.denote_bot
attribute [local simp] MatchingLogic.denote_ex
attribute [local simp] MatchingLogic.denote_imp
attribute [local simp] MatchingLogic.denote_var


section
@[expose] public section
namespace MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
section Cover
variable (M : Model S) (C : Set M.carrier)
private theorem proj_update (star : M.carrier) (i : Bool)
    (ν : Var → (C × Bool)) (x : Var) (n : C × Bool) :
    (fun y => proj M C star i (Function.update ν x n y)) =
      Function.update (fun y => proj M C star i (ν y)) x (proj M C star i n) := by
  funext y
  by_cases h : y = x
  · subst y
    simp
  · simp [Function.update, h]
end Cover
end MatchingLogic
end
end

set_option autoImplicit true
@[expose] public section
public section
open MatchingLogic
variable {S : Signature} {Var : Type} [DecidableEq Var]
variable (M : Model S) (C : Set M.carrier)
namespace MatchingLogic
theorem _root_.solution (hC : M.BackwardClosed C) (hne : C.Nonempty)
    (star : M.carrier) (hstar : star ∉ C)
    (ψ : Pattern S Var) (ν : Var → (C × Bool)) (p : C × Bool) :
    p ∈ (cover M C hne).denote ν ψ ↔
      (p.1 : M.carrier) ∈ M.denote (fun x => proj M C star p.2 (ν x)) ψ := by
  classical
  simp only [cover]
  induction ψ generalizing ν p with
  | var x =>
      simp only [Model.denote, Set.mem_singleton_iff]
      constructor
      · intro hp
        subst p
        simp [proj]
      · intro hp
        by_cases hb : (ν x).2 = p.2
        · apply Prod.ext
          · apply Subtype.ext
            simpa [proj, hb] using hp
          · exact hb.symm
        · exfalso
          have hpstar : (p.1 : M.carrier) = star := by
            simpa [proj, hb] using hp
          apply hstar
          rw [← hpstar]
          exact p.1.property
  | app σ f ih =>
      simp only [denote_app, Model.app, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨A, hA, hmix, hinterp⟩
        refine ⟨fun j => ((A j).1 : M.carrier), ?_, hinterp⟩
        intro j
        have hj := (ih j (ν := ν) (p := A j)).mp (hA j)
        simpa [proj, hmix j] using hj
      · rintro ⟨a, ha, hinterp⟩
        have haC : ∀ j, a j ∈ C := fun j =>
          Model.BackwardClosed.mem_of_interp M hC p.1.property hinterp j
        let A : Fin (S.arity σ) → (C × Bool) :=
          fun j => (⟨a j, haC j⟩, p.2)
        refine ⟨A, ?_, ?_, ?_⟩
        · intro j
          apply (ih j (ν := ν) (p := A j)).mpr
          simpa [A, proj] using ha j
        · intro j
          rfl
        · simpa [A] using hinterp
  | imp φ χ ihφ ihχ =>
      simp only [denote_imp, Set.mem_union, Set.mem_compl_iff]
      constructor
      · rintro (hφ | hχ)
        · left
          intro hpφ
          exact hφ ((ihφ (ν := ν) (p := p)).mpr hpφ)
        · right
          exact (ihχ (ν := ν) (p := p)).mp hχ
      · rintro (hφ | hχ)
        · left
          intro hpφ
          exact hφ ((ihφ (ν := ν) (p := p)).mp hpφ)
        · right
          exact (ihχ (ν := ν) (p := p)).mpr hχ
  | bot =>
      exact ⟨id, id⟩
  | ex x φ ih =>
      rw [denote_ex, denote_ex]
      constructor
      · intro hp
        obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hp
        apply Set.mem_iUnion.mpr
        refine ⟨proj M C star p.2 n, ?_⟩
        rw [← proj_update (M := M) (C := C) star p.2 ν x n]
        exact (ih (ν := Function.update ν x n) (p := p)).mp hn
      · intro hp
        obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hp
        by_cases haC : a ∈ C
        · let n : C × Bool := (⟨a, haC⟩, p.2)
          apply Set.mem_iUnion.mpr
          refine ⟨n, (ih (ν := Function.update ν x n) (p := p)).mpr ?_⟩
          rw [proj_update (M := M) (C := C) star p.2 ν x n]
          simpa [n, proj] using ha
        · let ρ : Var → M.carrier := fun y => proj M C star p.2 (ν y)
          have hagree : AgreeOn C (Function.update ρ x a)
              (Function.update ρ x star) := by
            intro y
            by_cases hy : y = x
            · subst y
              simp [haC, hstar]
            · simp only [Function.update, hy]
              by_cases hyC : ρ y ∈ C
              · exact Or.inl ⟨rfl, hyC⟩
              · exact Or.inr ⟨hyC, hyC⟩
          have hloc := locality M hC φ (Function.update ρ x a)
            (Function.update ρ x star) hagree
          have hstarDen : (p.1 : M.carrier) ∈
              M.denote (Function.update ρ x star) φ := by
            have hpC : (p.1 : M.carrier) ∈
                M.denote (Function.update ρ x a) φ ∩ C := ⟨ha, p.1.property⟩
            rw [hloc] at hpC
            exact hpC.1
          let n : C × Bool := (⟨hne.choose, hne.choose_spec⟩, !p.2)
          apply Set.mem_iUnion.mpr
          refine ⟨n, (ih (ν := Function.update ν x n) (p := p)).mpr ?_⟩
          rw [proj_update (M := M) (C := C) star p.2 ν x n]
          simpa [ρ, n, proj] using hstarDen
end MatchingLogic
