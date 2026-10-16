-- Prove2me | solution 1 for OAI.Problem346.symmetric_update_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:29:16.713113+00:00
-- url     : https://prove2.me/submissions/93eb5fb9-874e-4116-8b9d-cb6516688a63

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/DiagonalCoefficient.lean:L66-L86
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.symmetric_update_eq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient

-- ---- from OAI.RepresentationTheory.FoulkesHowe.DiagonalCoefficient ----
namespace OAI

noncomputable section

open scoped BigOperators

namespace Problem346

universe u

variable {E : Type u} [AddCommGroup E] [Module ℂ E]

/-- Symmetry identifies the terms of the linear diagonal coefficient. -/
lemma symmetric_update_eq {a : ℕ}
    (T : MultilinearMap ℂ (fun _ : Fin a => E) ℂ)
    (hsym : ∀ (σ : Equiv.Perm (Fin a)) (v : Fin a → E),
      T (fun k => v (σ k)) = T v)
    (x y : E) (i j : Fin a) :
    T (Function.update (fun _ => x) j y) =
      T (Function.update (fun _ => x) i y) := by
  have h := hsym (Equiv.swap i j) (Function.update (fun _ => x) i y)
  convert h using 1
  congr 1
  ext k
  by_cases hi : k = i
  · subst k
    by_cases hij : i = j
    · subst j
      rw [Equiv.swap_apply_left, Function.update_self]
    · simp [hij, Ne.symm hij]
  · by_cases hj : k = j
    · subst k; simp
    · simp [Equiv.swap_apply_of_ne_of_ne hi hj, Function.update_of_ne, hi, hj]

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution.{u} : type_of% @_root_.OAI.Problem346.symmetric_update_eq.{u} := @_root_.OAI.Problem346.symmetric_update_eq.{u}
