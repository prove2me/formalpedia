-- Prove2me | solution 1 for OAI.Problem346.SlotPolynomial.derivation_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:45:41.401004+00:00
-- url     : https://prove2.me/submissions/7de630c2-8fe2-450e-9ff1-c4c757a54f31

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean:L44-L81
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.SlotPolynomial.derivation_polynomial. The node keeps its source
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
import Theorems.Thm_OAI_Problem346_SlotPolynomial_derivation_prod

-- ---- from OAI.RepresentationTheory.FoulkesHowe.SlotDerivative ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.SlotPolynomial

variable {R A S I B : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq S]

variable [Fintype S] [Fintype I]

/-- A directional block derivation replaces each occurrence of the source block in turn. -/
theorem derivation_polynomial [DecidableEq B]
    (c : (S → I) → R) (l : S → B) (src dst : B)
    (D : Derivation R (MvPolynomial (B × I) R) (MvPolynomial (B × I) R))
    (hD : ∀ b i, D (MvPolynomial.X (b, i)) =
      if b = src then MvPolynomial.X (dst, i) else 0) :
    D (polynomial c l) =
      ∑ s ∈ Finset.univ.filter (fun s => l s = src),
        polynomial c (Function.update l s dst) := by
  classical
  unfold polynomial
  rw [map_sum]
  simp_rw [D.leibniz, MvPolynomial.derivation_C, smul_zero, add_zero,
    smul_eq_mul, derivation_prod]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : l s = src
  · simp only [h, ite_true]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    by_cases hjs : j = s
    · subst j
      simp [hD]
    · simp [Function.update_of_ne hjs]
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro k hk
    have hz : (∏ j : S, Function.update (fun s => MvPolynomial.X (l s, k s))
        s (D (MvPolynomial.X (l s, k s))) j) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ s)
      simp [hD, h]
    rw [hz, mul_zero]

end Problem346.SlotPolynomial

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346 OAI.Problem346.SlotPolynomial
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.SlotPolynomial.derivation_polynomial := @_root_.OAI.Problem346.SlotPolynomial.derivation_polynomial
