-- Prove2me | solution 1 for MIPRE.CL.CLFun.ExactlyOn.prodCL
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:11.584152+00:00
-- url     : https://prove2.me/submissions/e7bde523-df96-4112-a99c-0a91b38b1f20

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSampler.lean (solution of MIPRE.CL.CLFun.ExactlyOn.prodCL);
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
import Theorems.Thm_MIPRE_CL_CLFun_ExactlyOn_directSum

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem ExactlyOn.prod [Fintype ι] [Fintype κ] {P : CLFun F ι ℓ} {Q : CLFun F κ ℓ}
    (hP : P.ExactlyOn univ) (hQ : Q.ExactlyOn univ) : (P.prod Q).ExactlyOn univ := by
  have h := (hP.embed Function.Embedding.inl).directSum (hQ.embed Function.Embedding.inr)
    (disjoint_map_inl_inr _ _)
  have hu : (univ : Finset ι).map Function.Embedding.inl ∪ (univ : Finset κ).map
      Function.Embedding.inr = univ := by
    ext a; rcases a with i | j <;> simp
  rwa [hu] at h
end
end MIPRE.CL.CLFun

namespace MIPRE.CL
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
theorem map_sdiff' (e : ι ≃ ι') (S T : Finset ι) :
    T.map e.toEmbedding \ S.map e.toEmbedding = (T \ S).map e.toEmbedding := by
  ext i; simp [Finset.mem_map_equiv]
end
end MIPRE.CL

namespace MIPRE.CL.CLFun
section
variable {K : Type*} [Field K] {F : Type*} [Field F] [Algebra K F]
variable {ι ι' : Type*} {κ : Type*} [Fintype κ]
variable [DecidableEq ι] [DecidableEq κ]
variable [DecidableEq ι']
variable {ℓ : ℕ}
theorem ExactlyOn.reindex (e : ι ≃ ι') {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) :
    (P.reindex e).ExactlyOn (T.map e.toEmbedding) := by
  induction P generalizing T with
  | zero =>
    have hT : T = ∅ := hP
    show T.map e.toEmbedding = ∅
    rw [hT, Finset.map_empty]
  | cons S L₁ next ih =>
    obtain ⟨hS, hnext⟩ := hP
    refine ⟨Finset.map_subset_map.mpr hS, fun v => ?_⟩
    rw [map_sdiff']
    exact ih _ (hnext _)
end
end MIPRE.CL.CLFun

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL.CLFun.ExactlyOn
open Finset Cost
variable {a b : ℕ}
variable {ℓa ℓb : ℕ}
variable (L : ℕ) {P : CLFun 𝔽₂ (Fin a) ℓa} {Q : CLFun 𝔽₂ (Fin b) ℓb} (hP : P.ExactlyOn univ)
  (hQ : Q.ExactlyOn univ) (ha : ℓa ≤ L) (hb : ℓb ≤ L)
include hP hQ in
theorem _root_.solution : (prodCL L P Q ha hb).ExactlyOn univ := by
  have h := (ExactlyOn.prod (hP.liftTo L ha) (hQ.liftTo L hb)).reindex finSumFinEquiv
  rwa [Finset.map_univ_equiv] at h
end MIPRE.CL.CLFun.ExactlyOn
