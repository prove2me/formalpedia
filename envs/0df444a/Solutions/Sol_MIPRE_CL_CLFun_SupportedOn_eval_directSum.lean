-- Prove2me | solution 1 for MIPRE.CL.CLFun.SupportedOn.eval_directSum
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:20:54.934182+00:00
-- url     : https://prove2.me/submissions/bdda9c60-24d0-4bee-a24b-5576d8ec184f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Closure.lean (solution of MIPRE.CL.CLFun.SupportedOn.eval_directSum);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure_B

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
theorem proj_proj_of_disjoint {S T : Finset ι} (h : Disjoint S T) (x : ι → F) :
    proj S (proj T x) = 0 := by
  rw [proj_proj, Finset.disjoint_iff_inter_eq_empty.mp h, proj_empty]
end
end MIPRE.CL

namespace MIPRE.CL.RegLinear
section
variable {F : Type*} [Semiring F] {ι : Type*} [DecidableEq ι]
variable {S T : Finset ι}
theorem proj_apply_of_disjoint (L : RegLinear F S) (h : Disjoint T S) (x : ι → F) :
    proj T (L x) = 0 := by
  rw [← L.proj_apply x, proj_proj_of_disjoint h]
end
end MIPRE.CL.RegLinear

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
variable [Fintype ι]
/-- A presentation on `V_T` reads only the coordinates in `T`. -/
theorem SupportedOn.eval_proj_of_subset {P : CLFun F ι ℓ} {T U : Finset ι} (hP : P.SupportedOn T)
    (hTU : T ⊆ U) (x : ι → F) : P.eval (proj U x) = P.eval x := by
  induction P generalizing T U x with
  | zero => rfl
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    have hsub : T \ S ⊆ Sᶜ := fun i hi => by
      simp only [Finset.mem_sdiff] at hi
      simpa using hi.2
    simp only [eval_cons, L₁.apply_proj_of_subset (hS.trans hTU), proj_proj]
    rw [ih _ (hnext _) (Finset.subset_inter hsub (Finset.sdiff_subset.trans hTU)) x,
      ih _ (hnext _) hsub x]
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun.SupportedOn
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {k ℓ : ℕ}
variable [Fintype ι]
theorem _root_.solution {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (x : ι → F) :
    (P.directSum Q).eval x = P.eval x + Q.eval x := by
  induction P generalizing T T' x with
  | zero =>
    rw [Q.eq_zero]
    simp
  | cons S L₁ next ih =>
    cases Q with
    | cons S' L₁' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      have hSS' : Disjoint S S' :=
        Finset.disjoint_of_subset_left hS (Finset.disjoint_of_subset_right hS' hTT')
      have h₁ : proj S (L₁.directSum L₁' x) = L₁ x := by
        rw [RegLinear.directSum_apply, map_add, L₁.proj_apply, L₁'.proj_apply_of_disjoint hSS',
          add_zero]
      have h₂ : proj S' (L₁.directSum L₁' x) = L₁' x := by
        rw [RegLinear.directSum_apply, map_add, L₁.proj_apply_of_disjoint hSS'.symm,
          L₁'.proj_apply, zero_add]
      have hsub : T \ S ⊆ (S ∪ S')ᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        rw [Finset.mem_compl, Finset.mem_union]
        exact fun h => h.elim hi.2 fun h' => Finset.disjoint_left.mp hTT' hi.1 (hS' h')
      have hsub' : T' \ S' ⊆ (S ∪ S')ᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        rw [Finset.mem_compl, Finset.mem_union]
        exact fun h => h.elim (fun h' => Finset.disjoint_left.mp hTT' (hS h') hi.1) hi.2
      have hS₁ : T \ S ⊆ Sᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_compl.mpr hi.2
      have hS₂ : T' \ S' ⊆ S'ᶜ := fun i hi => by
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_compl.mpr hi.2
      rw [directSum_cons, eval_cons, h₁, h₂,
        ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')) (proj (S ∪ S')ᶜ x),
        eval_cons, eval_cons, RegLinear.directSum_apply,
        (hnext _).eval_proj_of_subset hsub, (hnext' _).eval_proj_of_subset hsub',
        (hnext _).eval_proj_of_subset hS₁, (hnext' _).eval_proj_of_subset hS₂,
        add_add_add_comm]
end MIPRE.CL.CLFun.SupportedOn
