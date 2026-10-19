-- Prove2me | solution 1 for MIPRE.CL.CLFun.toBits_mapOfPrefix_prodCL
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:12.933329+00:00
-- url     : https://prove2.me/submissions/9c49c2f1-7a17-4575-a1b1-c1fc79ad1b13

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSampler.lean (solution of MIPRE.CL.CLFun.toBits_mapOfPrefix_prodCL);
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
import Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_mapOfPrefix_proj
import Theorems.Thm_MIPRE_CL_CLFun_mapOfPrefix_reindex
import Theorems.Thm_MIPRE_CL_pull_proj_compl

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
/-- Linear-map queries from an arbitrary prefix commute with embedding. -/
theorem mapOfPrefix_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x y : κ → F) :
    (P.embed e).mapOfPrefix j x y = push e (P.mapOfPrefix j (pull e x) (pull e y)) := by
  induction P generalizing j x with
  | zero => simp [embed]
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [embed, mapOfPrefix_cons_succ, pull_proj, ih, pull_proj_compl]
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
theorem mapOfPrefix_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (j : ℕ) (u : ι → F) :
    (P.directSum Q).mapOfPrefix j u = P.mapOfPrefix j u + Q.mapOfPrefix j u := by
  induction P generalizing T T' j u with
  | zero => rw [Q.eq_zero]; simp
  | cons S L next ih =>
    cases Q with
    | cons S' L' next' =>
      obtain ⟨hS, hnext⟩ := hP
      obtain ⟨hS', hnext'⟩ := hQ
      cases j with
      | zero => rfl
      | succ j =>
        simp only [directSum_cons, mapOfPrefix_cons_succ,
          proj_proj_of_subset Finset.subset_union_left,
          proj_proj_of_subset Finset.subset_union_right]
        rw [ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')),
          (hnext _).mapOfPrefix_proj (sdiff_subset_compl_union hS' hTT'),
          (hnext' _).mapOfPrefix_proj (Finset.union_comm S S' ▸
            sdiff_subset_compl_union hS hTT'.symm),
          (hnext _).mapOfPrefix_proj sdiff_subset_compl,
          (hnext' _).mapOfPrefix_proj sdiff_subset_compl]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
variable [Fintype κ]
theorem mapOfPrefix_prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) (hP : P.ExactlyOn univ)
    (hQ : Q.ExactlyOn univ) (j : ℕ) (u y : ι ⊕ κ → F) :
    (P.prod Q).mapOfPrefix j u y
      = Sum.elim (P.mapOfPrefix j (fun i => u (.inl i)) (fun i => y (.inl i)))
          (Q.mapOfPrefix j (fun i => u (.inr i)) (fun i => y (.inr i))) := by
  rw [prod, mapOfPrefix_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), LinearMap.add_apply, mapOfPrefix_embed, mapOfPrefix_embed]
  funext a
  rcases a with i | i
  · simp only [Pi.add_apply, push_inl_left, push_inr_left, add_zero, Sum.elim_inl]
    rfl
  · simp only [Pi.add_apply, push_inl_right, push_inr_right, zero_add, Sum.elim_inr]
    rfl
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
theorem mapOfPrefix_prodCL (k : ℕ) (u y : Fin (a + b) → 𝔽₂) :
    (prodCL L P Q ha hb).mapOfPrefix k u y
      = Fin.append (P.mapOfPrefix k (leftPart u) (leftPart y))
          (Q.mapOfPrefix k (rightPart u) (rightPart y)) := by
  have hu : u = reindexEquiv finSumFinEquiv (Sum.elim (leftPart u) (rightPart u)) := by
    rw [← split_symm, LinearEquiv.apply_symm_apply]
  rw [prodCL]
  conv_lhs => rw [hu, mapOfPrefix_reindex]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [mapOfPrefix_prod _ _ (hP.liftTo L ha) (hQ.liftTo L hb), split_symm, ← sumElim_reindex]
  simp only [Sum.elim_inl, Sum.elim_inr, mapOfPrefix_liftTo]
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
theorem _root_.solution (k : ℕ) (u y : Fin (a + b) → 𝔽₂) :
    toBits ((prodCL L P Q ha hb).mapOfPrefix k u y)
      = toBits (P.mapOfPrefix k (leftPart u) (leftPart y))
          ++ toBits (Q.mapOfPrefix k (rightPart u) (rightPart y)) := by
  rw [mapOfPrefix_prodCL L hP hQ, toBits_append]
end MIPRE.CL.CLFun
