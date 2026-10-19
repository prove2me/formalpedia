-- Prove2me | solution 1 for OAI.CirculantHadamard.B_root_of_unity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:24:13.531301+00:00
-- url     : https://prove2.me/submissions/91ad4327-e22d-4dcc-8b02-a42c285f389f

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_OrderHalving
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryBlocks
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryCoefficients
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicRings
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeComponents
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_PrimeCharacterEvaluations
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalizationMaps
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingProducts
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryProductTransport
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_FirstOrderResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryResidue
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_BinaryLocalFamily
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_ResidueOneAssociation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicLocalBase
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAwayLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjectionPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluationAt
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalComparison
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CoefficientEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_AlternatingLocalization
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicAdjoin

open OAI OAI.CirculantHadamard
theorem solution (u : ℕ) (z : CyclotomicRings.B u)
    (hz : ∀ σ : CyclotomicRings.B u →+* ℂ, ‖σ z‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  classical
  set S : Set ℂ := ({Complex.I} : Set ℂ) ∪ CyclotomicRings.rho '' (u.primeFactors : Set ℕ) with hS
  have hSint : ∀ x ∈ S, IsIntegral ℤ x := by
    rintro x (hx | ⟨q, hq, rfl⟩)
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact Complex.isPrimitiveRoot_I.isIntegral (by norm_num)
    · have hq0 : q ≠ 0 := (Nat.prime_of_mem_primeFactors hq).ne_zero
      exact (CyclotomicRings.rho_isPrimitiveRoot q hq0).isIntegral (Nat.pos_of_ne_zero hq0)
  haveI : Finite S := (Set.finite_singleton _ |>.union ((u.primeFactors.finite_toSet).image _)).to_subtype
  set L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ S with hL
  haveI : FiniteDimensional ℚ L :=
    IntermediateField.finiteDimensional_adjoin (fun x hx => (hSint x hx).tower_top)
  haveI : NumberField L := ⟨⟩
  have hle : ∀ y : ℂ, y ∈ CyclotomicRings.B u → y ∈ L := by
    intro y hy
    have h1 : CyclotomicRings.B u ≤ (L.toSubalgebra.restrictScalars ℤ) := by
      apply Algebra.adjoin_le
      intro x hx
      exact IntermediateField.subset_adjoin ℚ S hx
    exact h1 hy
  let ι : CyclotomicRings.B u →+* L :=
    { toFun := fun y => ⟨y.1, hle y.1 y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hzint : IsIntegral ℤ (ι z) := by
    have h1 : (z : ℂ) ∈ integralClosure ℤ ℂ := by
      have : CyclotomicRings.B u ≤ integralClosure ℤ ℂ := Algebra.adjoin_le hSint
      exact this z.2
    have h2 : IsIntegral ℤ (z : ℂ) := h1
    exact (isIntegral_algHom_iff ((IntermediateField.val L).restrictScalars ℤ)
      Subtype.val_injective).1 h2
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one L ℂ hzint
    (fun φ => hz (φ.comp ι))
  refine ⟨n, hn, ?_⟩
  apply Subtype.ext
  have := congrArg Subtype.val hpow
  simp only [IntermediateField.coe_pow, IntermediateField.coe_one] at this
  rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
  exact this
