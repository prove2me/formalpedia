-- Prove2me | solution 1 for MIPRE.CL.CLFun.toBits_eval_truncate_prodCL
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:12.258258+00:00
-- url     : https://prove2.me/submissions/a9940782-f7fa-4f68-9ec0-40deea92da1c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSampler.lean (solution of MIPRE.CL.CLFun.toBits_eval_truncate_prodCL);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Embedding
import Definitions.Def_MIPRE_Foundations_CL_Product
import Definitions.Def_MIPRE_Foundations_CL_Downsize
import Definitions.Def_MIPRE_Foundations_CL_TypedSampler
import Definitions.Def_MIPRE_Foundations_CL_ProductSampler
import Theorems.Thm_MIPRE_CL_CLFun_eval_reindex
import Theorems.Thm_MIPRE_CL_CLFun_truncate_reindex
import Theorems.Thm_MIPRE_CL_pull_proj_compl

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
theorem SupportedOn.lift {P : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (h : T' ⊆ T) : (P.lift T').SupportedOn T := by
  induction P generalizing T T' with
  | zero => exact ⟨h, fun _ => trivial⟩
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    exact ⟨hS, fun v => ih v (hnext v) (Finset.sdiff_subset_sdiff h (Finset.Subset.refl S))⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
/-- Item (1) of `lem:cl-kth`: the `k`-th marginal is a `k`-level CL function on the same space. -/
theorem SupportedOn.truncate {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.SupportedOn T) (k : ℕ) :
    (P.truncate k).SupportedOn T := by
  induction k generalizing ℓ P T with
  | zero => trivial
  | succ k ih =>
    cases P with
    | zero => exact (ih (supportedOn_zero T)).lift (Finset.empty_subset T)
    | cons S L₁ next =>
      obtain ⟨hS, hnext⟩ := hP
      exact ⟨hS, fun v => ih (hnext v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.supportedOn {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    P.SupportedOn T := by
  induction P generalizing T with
  | zero => trivial
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.lift {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    (P.lift T).ExactlyOn T := by
  induction P generalizing T with
  | zero => exact ⟨Finset.Subset.refl T, fun _ => Finset.sdiff_self T⟩
  | cons S L₁ next ih => exact ⟨hP.1, fun v => ih v (hP.2 v)⟩
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
universe u v
variable {F : Type u} [Semiring F] {ι : Type v} [DecidableEq ι] {ℓ : ℕ}
theorem ExactlyOn.liftN {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (n : ℕ) :
    (P.liftN T n).ExactlyOn T := by
  induction n with
  | zero => exact hP
  | succ n ih => exact ih.lift
end
end MIPRE.CL.CLFun

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

namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
/-- Embedded factors still partition precisely the embedded original register. -/
theorem ExactlyOn.embed (e : ι ↪ κ) {P : CLFun F ι ℓ} {S : Finset ι}
    (hP : P.ExactlyOn S) : (P.embed e).ExactlyOn (S.map e) := by
  induction P generalizing S with
  | zero =>
    change S = ∅ at hP
    simp [CLFun.embed, hP]
  | cons U L next ih =>
    refine ⟨Finset.map_subset_map.mpr hP.1, fun x => ?_⟩
    rw [← Finset.map_sdiff]
    exact ih _ (hP.2 _)
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Classical
set_option linter.unusedSectionVars false
variable {F ι κ : Type*} [Semiring F] [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι] [Fintype κ]
/-- Marginal queries are transported by the same coordinate embedding. -/
theorem eval_truncate_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x : κ → F) :
    ((P.embed e).truncate j).eval x = push e ((P.truncate j).eval (pull e x)) := by
  induction j generalizing ℓ P x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => simp [embed, eval_truncate_zero]
    | cons S L next =>
      simp only [embed, truncate_succ_cons, eval_cons, RegLinear.embed_apply,
        pull_push, ih, pull_proj_compl, push_add]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
theorem ExactlyOn.castLevel {a b : ℕ} (h : a = b) {P : CLFun F ι a} {T : Finset ι}
    (hP : P.ExactlyOn T) : (P.castLevel h).ExactlyOn T := by
  subst h; exact hP
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
theorem ExactlyOn.liftTo {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (L : ℕ)
    (h : ℓ ≤ L) : (P.liftTo T L h).ExactlyOn T :=
  (hP.liftN _).castLevel _
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
omit [DecidableEq ι] [DecidableEq κ] in
theorem disjoint_map_inl_inr (S : Finset ι) (S' : Finset κ) :
    Disjoint (S.map Function.Embedding.inl) (S'.map Function.Embedding.inr) := by
  rw [Finset.disjoint_left]
  intro a ha ha'
  obtain ⟨i, -, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨j, -, h⟩ := Finset.mem_map.mp ha'
  cases h
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
theorem eval_truncate_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (j : ℕ) (x : ι → F) :
    ((P.directSum Q).truncate j).eval x = (P.truncate j).eval x + (Q.truncate j).eval x := by
  induction j generalizing ℓ P Q T T' x with
  | zero => simp
  | succ j ih =>
    cases P with
    | zero => rw [Q.eq_zero]; simp [eval_truncate_zero]
    | cons S L next =>
      cases Q with
      | cons S' L' next' =>
        obtain ⟨hS, hnext⟩ := hP
        obtain ⟨hS', hnext'⟩ := hQ
        have hSS' : Disjoint S S' :=
          Finset.disjoint_of_subset_left hS (Finset.disjoint_of_subset_right hS' hTT')
        have h₁ : proj S (L.directSum L' x) = L x := by
          rw [RegLinear.directSum_apply, map_add, L.proj_apply, L'.proj_apply_of_disjoint hSS',
            add_zero]
        have h₂ : proj S' (L.directSum L' x) = L' x := by
          rw [RegLinear.directSum_apply, map_add, L.proj_apply_of_disjoint hSS'.symm,
            L'.proj_apply, zero_add]
        rw [directSum_cons, truncate_succ_cons, eval_cons, h₁, h₂,
          ih (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
            (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')),
          truncate_succ_cons, truncate_succ_cons, eval_cons, eval_cons,
          RegLinear.directSum_apply,
          ((hnext _).truncate j).eval_proj_of_subset (sdiff_subset_compl_union hS' hTT'),
          ((hnext' _).truncate j).eval_proj_of_subset (Finset.union_comm S S' ▸
            sdiff_subset_compl_union hS hTT'.symm),
          ((hnext _).truncate j).eval_proj_of_subset sdiff_subset_compl,
          ((hnext' _).truncate j).eval_proj_of_subset sdiff_subset_compl,
          add_add_add_comm]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
variable [Fintype κ]
theorem eval_truncate_prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) (hP : P.ExactlyOn univ)
    (hQ : Q.ExactlyOn univ) (j : ℕ) (x : ι ⊕ κ → F) :
    ((P.prod Q).truncate j).eval x
      = Sum.elim ((P.truncate j).eval (fun i => x (.inl i)))
          ((Q.truncate j).eval (fun i => x (.inr i))) := by
  rw [prod, eval_truncate_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), eval_truncate_embed, eval_truncate_embed]
  funext a
  rcases a with i | i
  · simp only [Pi.add_apply, push_inl_left, push_inr_left, add_zero, Sum.elim_inl]
    rfl
  · simp only [Pi.add_apply, push_inl_right, push_inr_right, zero_add, Sum.elim_inr]
    rfl
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι]
variable [DecidableEq ι'] [Fintype ι']
variable {ℓ : ℕ}
theorem eval_reindex' (e : ι ≃ ι') (P : CLFun F ι ℓ) (y : ι' → F) :
    (P.reindex e).eval y = reindexEquiv e (P.eval ((reindexEquiv e).symm y)) := by
  conv_lhs => rw [← (reindexEquiv e).apply_symm_apply y]
  rw [eval_reindex]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL
noncomputable section
open Finset Cost
variable {a b : ℕ}
theorem toBits_append (v : Fin a → 𝔽₂) (w : Fin b → 𝔽₂) :
    toBits (Fin.append v w) = toBits v ++ toBits w := by
  simp only [toBits, List.ofFn_add, Fin.append_right]
  congr 2
  funext i
  rw [show Fin.castLE (Nat.le_add_right a b) i = Fin.castAdd b i from rfl, Fin.append_left]
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
noncomputable section
open Finset Cost
variable {a b : ℕ}
variable {ℓa ℓb : ℕ}
variable (L : ℕ) {P : CLFun 𝔽₂ (Fin a) ℓa} {Q : CLFun 𝔽₂ (Fin b) ℓb} (hP : P.ExactlyOn univ)
  (hQ : Q.ExactlyOn univ) (ha : ℓa ≤ L) (hb : ℓb ≤ L)
include hP hQ in
theorem eval_truncate_prodCL (j : ℕ) (x : Fin (a + b) → 𝔽₂) :
    ((prodCL L P Q ha hb).truncate j).eval x
      = Fin.append ((P.truncate j).eval (leftPart x)) ((Q.truncate j).eval (rightPart x)) := by
  rw [prodCL, truncate_reindex, eval_reindex', eval_truncate_prod _ _ (hP.liftTo L ha)
    (hQ.liftTo L hb), ← sumElim_reindex, split_symm]
  simp only [Sum.elim_inl, Sum.elim_inr, eval_truncate_liftTo]
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun
open Finset Cost
variable {a b : ℕ}
variable {ℓa ℓb : ℕ}
variable (L : ℕ) {P : CLFun 𝔽₂ (Fin a) ℓa} {Q : CLFun 𝔽₂ (Fin b) ℓb} (hP : P.ExactlyOn univ)
  (hQ : Q.ExactlyOn univ) (ha : ℓa ≤ L) (hb : ℓb ≤ L)
include hP hQ in
theorem _root_.solution (j : ℕ) (x : Fin (a + b) → 𝔽₂) :
    toBits (((prodCL L P Q ha hb).truncate j).eval x)
      = toBits ((P.truncate j).eval (leftPart x)) ++ toBits ((Q.truncate j).eval (rightPart x)) := by
  rw [eval_truncate_prodCL L hP hQ, toBits_append]
end MIPRE.CL.CLFun
