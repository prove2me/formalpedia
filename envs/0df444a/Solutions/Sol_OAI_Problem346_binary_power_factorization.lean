-- Prove2me | solution 1 for OAI.Problem346.binary_power_factorization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T17:27:12.81913+00:00
-- url     : https://prove2.me/submissions/dc13fd4a-faf4-4f3a-a42f-1ed867f738ab

-- Generated from openai/math@1581d4c lean/OAI/RepresentationTheory/FoulkesHowe/BinaryFactorization.lean:L10-L39
-- (upload_full_project.md Phase 4): solution for node OAI.Problem346.binary_power_factorization. The node keeps its source
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

-- ---- from OAI.RepresentationTheory.FoulkesHowe.BinaryFactorization ----
namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem346

/-- Binary forms used in the first step of the vanishing argument split into linear factors. -/
theorem binary_power_factorization {A : Type*} [CommRing A] [Algebra ℂ A]
    (r : ℕ) (hr : 0 < r) (x y : A) (c : ℂ) :
    ∃ z : Fin r → ℂ, (∏ i : Fin r, (x - z i • y)) = x ^ r + c • y ^ r := by
  classical
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_pow_nat_eq (-c) hr
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / r)
  have hζ : IsPrimitiveRoot ζ r := Complex.isPrimitiveRoot_exp r hr.ne'
  have hp : (Polynomial.X ^ r - Polynomial.C (-c) : Polynomial ℂ) =
      ∏ i ∈ Finset.range r, (Polynomial.X - Polynomial.C (ζ ^ i * α)) :=
    X_pow_sub_C_eq_prod hζ hr hα
  have hh := congrArg (fun p : Polynomial ℂ => p.homogenize r) hp
  have hd : ∀ i ∈ Finset.range r,
      (Polynomial.X - Polynomial.C (ζ ^ i * α)).natDegree ≤ 1 := by
    intro i hi
    rw [Polynomial.natDegree_X_sub_C]
  have hprod := Polynomial.homogenize_finsetProd (n := fun _ : ℕ => 1) hd
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one] at hprod
  rw [hprod] at hh
  simp only [Polynomial.homogenize_sub, Polynomial.homogenize_X_pow le_rfl,
    Nat.sub_self, pow_zero, mul_one, Polynomial.homogenize_C,
    Polynomial.homogenize_X (by decide : (1 : ℕ) ≠ 0), Nat.sub_self, pow_one] at hh
  have he := congrArg (MvPolynomial.aeval ![x, y]) hh
  simp only [map_sub, map_pow, map_mul, map_prod, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    MvPolynomial.aeval_C] at he
  refine ⟨fun i => ζ ^ (i : ℕ) * α, ?_⟩
  change (∏ i : Fin r, (x - (ζ ^ (i : ℕ) * α) • y)) = _
  rw [Fin.prod_univ_eq_prod_range (fun i => x - (ζ ^ i * α) • y)]
  simpa only [Algebra.smul_def, map_neg, neg_mul, sub_neg_eq_add, map_mul, map_pow] using he.symm

end Problem346

end

end OAI

-- ---- platform node ----
open OAI OAI.Problem346
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Problem346.binary_power_factorization := @_root_.OAI.Problem346.binary_power_factorization
