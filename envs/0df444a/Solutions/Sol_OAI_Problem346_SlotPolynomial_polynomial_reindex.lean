-- Prove2me | solution 1 for OAI.Problem346.SlotPolynomial.polynomial_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:47:16.064303+00:00
-- url     : https://prove2.me/submissions/07cc921a-3c34-4587-bb16-ff2315b68cd9

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean:L83-L98
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.SlotPolynomial.polynomial_reindex. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SlotDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SlotPolynomial

variable {R A S I B : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq S]

variable [Fintype S] [Fintype I]

/-- Reindexing slots moves the same permutation onto the coefficient array. -/
theorem polynomial_reindex (c : (S → I) → R) (l : S → B) (e : Equiv.Perm S) :
    polynomial c (l ∘ e) = polynomial (fun k => c (k ∘ e)) l := by
  classical
  unfold polynomial
  apply Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl I))
  intro k
  congr 1
  · congr 1
    change c k = c _
    congr 1
    funext s
    simp
  · apply Fintype.prod_equiv e
    intro s
    simp

end Problem346.SlotPolynomial

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.SlotPolynomial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.SlotPolynomial.polynomial_reindex := @_root_.OAI.Problem346.SlotPolynomial.polynomial_reindex
