-- Prove2me | solution 1 for OAI.Problem346.derivation_eq_zero_of_positive_weight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:39:17.569357+00:00
-- url     : https://prove2.me/submissions/f085d628-d87f-4c78-9774-316c5faea950

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/DerivationInjectivity.lean:L14-L38
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.derivation_eq_zero_of_positive_weight. The node keeps its source
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
import Theorems.Thm_OAI_Problem346_ShiftInjectivity_eq_zero_of_positive_weight
import Theorems.Thm_OAI_Problem346_derivation_pow_mul_eq_zero

-- ---- from OAI.RepresentationTheory.FoulkesHowe.ShiftNilpotence ----
namespace OAI

noncomputable section

namespace Problem346

section Derivation

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- Pointwise local nilpotence of a derivation is closed under addition. -/
theorem derivation_exists_pow_add_eq_zero (D : Derivation R A A) (a b : A)
    (ha : ∃ m : ℕ, (D.toLinearMap ^ m) a = 0)
    (hb : ∃ n : ℕ, (D.toLinearMap ^ n) b = 0) :
    ∃ n : ℕ, (D.toLinearMap ^ n) (a + b) = 0 := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  refine ⟨m + n, ?_⟩
  rw [map_add, Module.End.pow_map_zero_of_le (Nat.le_add_right m n) hm,
    Module.End.pow_map_zero_of_le (Nat.le_add_left n m) hn, add_zero]

/-- Pointwise local nilpotence of a derivation is closed under multiplication. -/
theorem derivation_exists_pow_mul_eq_zero (D : Derivation R A A) (a b : A)
    (ha : ∃ m : ℕ, (D.toLinearMap ^ m) a = 0)
    (hb : ∃ n : ℕ, (D.toLinearMap ^ n) b = 0) :
    ∃ n : ℕ, (D.toLinearMap ^ n) (a * b) = 0 := by
  obtain ⟨m, hm⟩ := ha
  obtain ⟨n, hn⟩ := hb
  exact ⟨m + n, derivation_pow_mul_eq_zero D m n a b hm hn⟩

end Derivation

section MvPolynomial

variable {R σ : Type*} [CommRing R]

/-- Local nilpotence on polynomial generators implies local nilpotence everywhere.
No finiteness assumption on the variable type is needed, so spectator variables
can be retained without changing the argument. -/
theorem mvPolynomial_derivation_locally_nilpotent
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hX : ∀ i : σ, ∃ n : ℕ, (D.toLinearMap ^ n) (MvPolynomial.X i) = 0)
    (f : MvPolynomial σ R) : ∃ n : ℕ, (D.toLinearMap ^ n) f = 0 := by
  induction f using MvPolynomial.induction_on with
  | C r =>
      refine ⟨1, ?_⟩
      rw [pow_one]
      exact MvPolynomial.derivation_C D r
  | add p q hp hq =>
      exact derivation_exists_pow_add_eq_zero D p q hp hq
  | mul_X p i hp =>
      exact derivation_exists_pow_mul_eq_zero D p (MvPolynomial.X i) hp (hX i)

/-- The square-zero-on-generators criterion used for directional shifts. -/
theorem mvPolynomial_derivation_locally_nilpotent_of_square_zero_X
    (D : Derivation R (MvPolynomial σ R) (MvPolynomial σ R))
    (hX : ∀ i : σ, D (D (MvPolynomial.X i)) = 0)
    (f : MvPolynomial σ R) : ∃ n : ℕ, (D.toLinearMap ^ n) f = 0 := by
  apply mvPolynomial_derivation_locally_nilpotent D _ f
  intro i
  refine ⟨2, ?_⟩
  rw [pow_two, Module.End.mul_apply]
  exact hX i

end MvPolynomial

end Problem346

end

end OAI

-- ---- from OAI.RepresentationTheory.FoulkesHowe.DerivationInjectivity ----
namespace OAI

noncomputable section

namespace Problem346

open MvPolynomial

variable {K σ : Type*} [Field K] [CharZero K]

/-- An algebraic form of the positive-weight injectivity criterion for polynomial
derivations. The generator condition admits arbitrary spectator variables. -/
theorem derivation_eq_zero_of_positive_weight
    (D E H : Derivation K (MvPolynomial σ K) (MvPolynomial σ K))
    (hED : ⁅E, D⁆ = H) (hHE : ⁅H, E⁆ = (2 : K) • E)
    (hEX : ∀ i : σ, E (E (X i)) = 0)
    (f : MvPolynomial σ K) (p q : ℕ) (hpq : q < p)
    (hf : H f = ((p : K) - q) • f) (hDf : D f = 0) : f = 0 := by
  refine ShiftInjectivity.eq_zero_of_positive_weight D.toLinearMap E.toLinearMap
    H.toLinearMap ?_ ?_ f (p - q) (Nat.sub_pos_of_lt hpq) ?_ hDf ?_
  · intro z
    have hz := congrArg (fun F : Derivation K (MvPolynomial σ K)
      (MvPolynomial σ K) => F z) hED
    simp only [Derivation.commutator_apply] at hz
    change D (E z) = E (D z) - H z
    linear_combination -hz
  · intro z
    have hz := congrArg (fun F : Derivation K (MvPolynomial σ K)
      (MvPolynomial σ K) => F z) hHE
    simp only [Derivation.commutator_apply, Derivation.smul_apply] at hz
    change H (E z) = E (H z) + (2 : K) • E z
    linear_combination hz
  · change H f = ((p - q : ℕ) : K) • f
    simpa only [Nat.cast_sub (Nat.le_of_lt hpq)] using hf
  · exact mvPolynomial_derivation_locally_nilpotent_of_square_zero_X E hEX f

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open MvPolynomial


theorem solution : type_of% @_root_.OAI.Problem346.derivation_eq_zero_of_positive_weight := @_root_.OAI.Problem346.derivation_eq_zero_of_positive_weight
