-- Prove2me | solution 1 for MIPRE.CL.CLFun.indicatorBits_factorOfPrefix_prodCL
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:42:13.695354+00:00
-- url     : https://prove2.me/submissions/3c00d949-eead-4453-9f51-a666cd12b56e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/ProductSampler.lean (solution of MIPRE.CL.CLFun.indicatorBits_factorOfPrefix_prodCL);
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
import Theorems.Thm_MIPRE_CL_CLFun_SupportedOn_factorOfPrefix_proj
import Theorems.Thm_MIPRE_CL_CLFun_factorOfPrefix_reindex
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
/-- Factor queries from an arbitrary prefix commute with embedding. -/
theorem factorOfPrefix_embed (e : ι ↪ κ) (P : CLFun F ι ℓ) (j : ℕ) (x : κ → F) :
    (P.embed e).factorOfPrefix j x = (P.factorOfPrefix j (pull e x)).map e := by
  induction P generalizing j x with
  | zero => simp [embed]
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simp only [embed, factorOfPrefix_cons_succ, pull_proj, ih, pull_proj_compl]
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
theorem factorOfPrefix_directSum {P Q : CLFun F ι ℓ} {T T' : Finset ι} (hP : P.SupportedOn T)
    (hQ : Q.SupportedOn T') (hTT' : Disjoint T T') (j : ℕ) (u : ι → F) :
    (P.directSum Q).factorOfPrefix j u = P.factorOfPrefix j u ∪ Q.factorOfPrefix j u := by
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
        simp only [directSum_cons, factorOfPrefix_cons_succ,
          proj_proj_of_subset Finset.subset_union_left,
          proj_proj_of_subset Finset.subset_union_right]
        rw [ih _ (hnext _) (hnext' _) (Finset.disjoint_of_subset_left Finset.sdiff_subset
          (Finset.disjoint_of_subset_right Finset.sdiff_subset hTT')),
          (hnext _).factorOfPrefix_proj (sdiff_subset_compl_union hS' hTT'),
          (hnext' _).factorOfPrefix_proj (Finset.union_comm S S' ▸
            sdiff_subset_compl_union hS hTT'.symm),
          (hnext _).factorOfPrefix_proj sdiff_subset_compl,
          (hnext' _).factorOfPrefix_proj sdiff_subset_compl]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
theorem factorOfPrefix_lift {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (j : ℕ)
    (u : ι → F) : (P.lift T).factorOfPrefix j u = P.factorOfPrefix j u := by
  induction P generalizing T j u with
  | zero =>
    have hT : T = ∅ := hP
    cases j <;> simp [lift, hT]
  | cons S L next ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih _ (hP.2 _) _ _
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
theorem factorOfPrefix_liftN {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (n j : ℕ)
    (u : ι → F) : (P.liftN T n).factorOfPrefix j u = P.factorOfPrefix j u := by
  induction n with
  | zero => rfl
  | succ n ih => rw [liftN, factorOfPrefix_lift (hP.liftN n), ih]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
theorem factorOfPrefix_liftTo {P : CLFun F ι ℓ} {T : Finset ι} (hP : P.ExactlyOn T) (L : ℕ)
    (h : ℓ ≤ L) (j : ℕ) (u : ι → F) :
    (P.liftTo T L h).factorOfPrefix j u = P.factorOfPrefix j u := by
  rw [liftTo, factorOfPrefix_castLevel, factorOfPrefix_liftN hP]
end
end MIPRE.CL.CLFun

namespace MIPRE.CL.CLFun
noncomputable section
open Finset
variable {F : Type*} [Semiring F] {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
variable {ℓ : ℕ}
variable [Fintype ι]
variable [Fintype κ]
theorem factorOfPrefix_prod (P : CLFun F ι ℓ) (Q : CLFun F κ ℓ) (hP : P.ExactlyOn univ)
    (hQ : Q.ExactlyOn univ) (j : ℕ) (u : ι ⊕ κ → F) :
    (P.prod Q).factorOfPrefix j u
      = (P.factorOfPrefix j (fun i => u (.inl i))).map Function.Embedding.inl ∪
          (Q.factorOfPrefix j (fun i => u (.inr i))).map Function.Embedding.inr := by
  rw [prod, factorOfPrefix_directSum ((hP.embed _).supportedOn) ((hQ.embed _).supportedOn)
    (disjoint_map_inl_inr _ _), factorOfPrefix_embed, factorOfPrefix_embed]
  rfl
end
end MIPRE.CL.CLFun

namespace MIPRE.CL
noncomputable section
open Finset Cost
variable {a b : ℕ}
theorem indicatorBits_eq_append (S : Finset (Fin (a + b))) :
    indicatorBits S = indicatorBits (S.preimage (Fin.castAdd b) (Fin.castAdd_injective _ _).injOn)
      ++ indicatorBits (S.preimage (Fin.natAdd a) (Fin.natAdd_injective _ _).injOn) := by
  simp only [indicatorBits, List.ofFn_add, Finset.mem_preimage]
  rfl
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
theorem factorOfPrefix_prodCL (k : ℕ) (u : Fin (a + b) → 𝔽₂) :
    (prodCL L P Q ha hb).factorOfPrefix k u
      = ((P.factorOfPrefix k (leftPart u)).map Function.Embedding.inl ∪
          (Q.factorOfPrefix k (rightPart u)).map Function.Embedding.inr).map
            finSumFinEquiv.toEmbedding := by
  have hu : u = reindexEquiv finSumFinEquiv (Sum.elim (leftPart u) (rightPart u)) := by
    rw [← split_symm, LinearEquiv.apply_symm_apply]
  rw [prodCL]
  conv_lhs => rw [hu, factorOfPrefix_reindex, factorOfPrefix_prod _ _ (hP.liftTo L ha)
    (hQ.liftTo L hb), factorOfPrefix_liftTo hP, factorOfPrefix_liftTo hQ]
  rfl
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
theorem _root_.solution (k : ℕ) (u : Fin (a + b) → 𝔽₂) :
    indicatorBits ((prodCL L P Q ha hb).factorOfPrefix k u)
      = indicatorBits (P.factorOfPrefix k (leftPart u))
          ++ indicatorBits (Q.factorOfPrefix k (rightPart u)) := by
  rw [factorOfPrefix_prodCL L hP hQ, indicatorBits_eq_append]
  congr 2
  · ext i
    simp only [Finset.mem_preimage, Finset.mem_map, Finset.mem_union, Equiv.toEmbedding_apply,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply]
    constructor
    · rintro ⟨p, hp, he⟩
      rcases hp with ⟨i', hi', rfl⟩ | ⟨i', hi', rfl⟩
      · rw [finSumFinEquiv_apply_left] at he
        rwa [← Fin.castAdd_injective _ _ he]
      · rw [finSumFinEquiv_apply_right] at he
        exact absurd he (Fin.ne_of_val_ne (by simp; omega))
    · intro hi
      exact ⟨.inl i, Or.inl ⟨i, hi, rfl⟩, finSumFinEquiv_apply_left i⟩
  · ext i
    simp only [Finset.mem_preimage, Finset.mem_map, Finset.mem_union, Equiv.toEmbedding_apply,
      Function.Embedding.inl_apply, Function.Embedding.inr_apply]
    constructor
    · rintro ⟨p, hp, he⟩
      rcases hp with ⟨i', hi', rfl⟩ | ⟨i', hi', rfl⟩
      · rw [finSumFinEquiv_apply_left] at he
        exact absurd he (Fin.ne_of_val_ne (by simp; omega))
      · rw [finSumFinEquiv_apply_right] at he
        rwa [← Fin.natAdd_injective _ _ he]
    · intro hi
      exact ⟨.inr i, Or.inr ⟨i, hi, rfl⟩, finSumFinEquiv_apply_right i⟩
end MIPRE.CL.CLFun
