-- Prove2me | solution 1 for OAI.Problem346.derivation_pow_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:37:08.734779+00:00
-- url     : https://prove2.me/submissions/be21bff8-f86c-44e7-99eb-7a22b5c81666

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/ShiftNilpotence.lean:L13-L46
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.derivation_pow_mul_eq_zero. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.ShiftNilpotence ----
namespace OAI

noncomputable section

namespace Problem346

section Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- A derivation is locally nilpotent at a product when it is locally nilpotent
at each factor. The deliberately loose exponent avoids binomial coefficients. -/
theorem derivation_pow_mul_eq_zero (D : Derivation R A A)
    (m n : ℕ) (a b : A)
    (ha : (D.toLinearMap ^ m) a = 0)
    (hb : (D.toLinearMap ^ n) b = 0) :
    (D.toLinearMap ^ (m + n)) (a * b) = 0 := by
  induction m generalizing n a b with
  | zero =>
      simp only [pow_zero, Module.End.one_apply] at ha
      simp [ha]
  | succ m hm =>
      induction n generalizing a b with
      | zero =>
          simp only [pow_zero, Module.End.one_apply] at hb
          simp [hb]
      | succ n hn =>
          have hDa : (D.toLinearMap ^ m) (D a) = 0 := by
            rw [pow_succ, Module.End.mul_apply] at ha
            exact ha
          have hDb : (D.toLinearMap ^ n) (D b) = 0 := by
            rw [pow_succ, Module.End.mul_apply] at hb
            exact hb
          have hp := hm (n + 1) (D a) b hDa hb
          have hq := hn a (D b) ha hDb
          have he : m + 1 + (n + 1) = (m + (n + 1)) + 1 := by omega
          rw [he, pow_succ, Module.End.mul_apply]
          change (D.toLinearMap ^ (m + (n + 1))) (D (a * b)) = 0
          rw [D.leibniz, map_add]
          have hp' : (D.toLinearMap ^ (m + (n + 1))) (b * D a) = 0 := by
            simpa only [mul_comm] using hp
          have hq' : (D.toLinearMap ^ (m + (n + 1))) (a * D b) = 0 := by
            simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hq
          simp only [smul_eq_mul, hp', hq', add_zero]

end Derivation

section MvPolynomial

variable {R σ : Type*} [CommRing R]

end MvPolynomial

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346


theorem solution : type_of% @_root_.OAI.Problem346.derivation_pow_mul_eq_zero := @_root_.OAI.Problem346.derivation_pow_mul_eq_zero
