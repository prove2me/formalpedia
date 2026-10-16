-- Prove2me | solution 1 for OAI.Problem346.multilinearPolynomial_eq_zero_of_replacements
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T18:07:45.272131+00:00
-- url     : https://prove2.me/submissions/fa07e394-1c94-4d78-98fa-ce5b4ae11084

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/EncodedCancellation.lean:L13-L52
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.multilinearPolynomial_eq_zero_of_replacements. The node keeps its source
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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints
import Theorems.Thm_OAI_Problem346_PolynomialShift_eq_zero_of_shift_eq_zero
import Theorems.Thm_OAI_Problem346_SlotPolynomial_derivation_polynomial

-- ---- from OAI.RepresentationTheory.FoulkesHowe.EncodingHomogeneous ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346.EncodingDegree

variable {R : Type*} [CommSemiring R]
variable {S K B : Type*} [Fintype S] [DecidableEq S] [Fintype K]

/-- A coefficient expansion has weighted degree given by the sum of the weights
of its assigned vector blocks. The coefficients can be arbitrary. -/
theorem weightedHomogeneous_expansion (c : (S → K) → R) (blocks : S → B)
    (w : B → ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun x : B × K => w x.1)
      (∑ k : S → K, MvPolynomial.C (c k) *
        ∏ i : S, MvPolynomial.X (blocks i, k i))
      (∑ i : S, w (blocks i)) := by
  classical
  apply MvPolynomial.IsWeightedHomogeneous.sum
  intro k _
  apply MvPolynomial.IsWeightedHomogeneous.C_mul
  apply MvPolynomial.IsWeightedHomogeneous.prod
  intro i _
  exact MvPolynomial.isWeightedHomogeneous_X _ _ _

/-- The degree in one block is exactly the number of occurrences of that block. -/
theorem blockHomogeneous_expansion [DecidableEq B]
    (c : (S → K) → R) (blocks : S → B) (b : B) :
    MvPolynomial.IsWeightedHomogeneous
      (fun x : B × K => if x.1 = b then 1 else 0)
      (∑ k : S → K, MvPolynomial.C (c k) *
        ∏ i : S, MvPolynomial.X (blocks i, k i))
      (Finset.univ.filter (fun i => blocks i = b)).card := by
  simpa only [Finset.sum_boole, Nat.cast_id] using
    (weightedHomogeneous_expansion c blocks (fun x => if x = b then 1 else 0))

end Problem346.EncodingDegree

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.EncodedCancellation ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- Cancel one directional derivative of a repeated-block multilinear polynomial.
It suffices that every single source-slot replacement vanishes; no normalization
or nonvanishing factorial is needed. -/
theorem multilinearPolynomial_eq_zero_of_replacements
    {V S I B : Type*} [AddCommGroup V] [Module ℂ V]
    [Fintype S] [Fintype I] [Fintype B] [hS : DecidableEq S] [hB : DecidableEq B]
    (L : MultilinearMap ℂ (fun _ : S => V) ℂ) (e : I → V)
    (blocks : S → B) (src dst : B) (hsd : src ≠ dst)
    (hdegree : (Finset.univ.filter (fun s => blocks s = dst)).card <
      (Finset.univ.filter (fun s => blocks s = src)).card)
    (hzero : ∀ s, blocks s = src →
      multilinearPolynomial L e (Function.update blocks s dst) = 0) :
    multilinearPolynomial L e blocks = 0 := by
  classical
  have hS_eq : hS = Classical.decEq S := Subsingleton.elim _ _
  cases hS_eq
  have hB_eq : hB = Classical.decEq B := Subsingleton.elim _ _
  cases hB_eq
  apply PolynomialShift.eq_zero_of_shift_eq_zero src dst hsd hdegree
  · unfold PolynomialWeights.IsBlockHomogeneous PolynomialWeights.blockWeight
    simpa only [multilinearPolynomial] using
      EncodingDegree.blockHomogeneous_expansion
        (fun k => L (fun s => e (k s))) blocks src
  · unfold PolynomialWeights.IsBlockHomogeneous PolynomialWeights.blockWeight
    simpa only [multilinearPolynomial] using
      EncodingDegree.blockHomogeneous_expansion
        (fun k => L (fun s => e (k s))) blocks dst
  · have hd := SlotPolynomial.derivation_polynomial
      (fun k => L (fun s => e (k s))) blocks src dst
      (PolynomialShift.derivation src dst) (by intro b i; simp)
    have hz : (∑ s ∈ Finset.univ.filter (fun s => blocks s = src),
        SlotPolynomial.polynomial (fun k => L (fun s => e (k s)))
          (Function.update blocks s dst)) = 0 := by
      apply Finset.sum_eq_zero
      intro s hs
      simpa only [SlotPolynomial.polynomial, multilinearPolynomial] using
        hzero s (Finset.mem_filter.mp hs).2
    rw [hz] at hd
    simpa only [PolynomialShift.shift_apply, SlotPolynomial.polynomial,
      multilinearPolynomial] using hd

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.multilinearPolynomial_eq_zero_of_replacements := @_root_.OAI.Problem346.multilinearPolynomial_eq_zero_of_replacements
