-- Prove2me | solution 1 for OAI.Problem346.SlotPolynomial.polynomial_update_eq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:50:01.546469+00:00
-- url     : https://prove2.me/submissions/31a8041e-4d6c-4927-8a6e-87a7f78dad13

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean:L109-L126
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.SlotPolynomial.polynomial_update_eq. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Theorems.Thm_OAI_Problem346_SlotPolynomial_polynomial_reindex

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SlotDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SlotPolynomial

variable {R A S I B : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq S]

variable [Fintype S] [Fintype I]

/-- Symmetry of coefficients induces invariance under the same permutation of slot labels. -/
theorem polynomial_reindex_of_invariant (c : (S → I) → R) (l : S → B)
    (e : Equiv.Perm S) (hc : ∀ k, c (k ∘ e) = c k) :
    polynomial c (l ∘ e) = polynomial c l := by
  rw [polynomial_reindex]
  congr 1
  funext k
  exact hc k

/-- Swapping two equal-labelled slots shows that replacing either label gives the same polynomial. -/
theorem polynomial_update_eq (c : (S → I) → R) (l : S → B) (s t : S) (dst : B)
    (hl : l s = l t)
    (hc : ∀ k, c (k ∘ Equiv.swap s t) = c k) :
    polynomial c (Function.update l s dst) = polynomial c (Function.update l t dst) := by
  classical
  have hlabels : Function.update l s dst =
      Function.update l t dst ∘ Equiv.swap s t := by
    funext j
    by_cases hjs : j = s
    · subst j
      simp
    by_cases hjt : j = t
    · subst j
      simp [hjs, Ne.symm hjs, hl]
    · simp [Equiv.swap_apply_of_ne_of_ne hjs hjt, hjs, hjt]
  rw [hlabels]
  exact polynomial_reindex_of_invariant c _ _ hc

end Problem346.SlotPolynomial

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.SlotPolynomial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.SlotPolynomial.polynomial_update_eq := @_root_.OAI.Problem346.SlotPolynomial.polynomial_update_eq
