-- Prove2me | solution 1 for GlobalTheory.InertiaLift.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:54:05.13417+00:00
-- url     : https://prove2.me/submissions/3bdb1c62-b2f8-447d-9e53-fd71463edc1c

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteGaloisInertiaLiftsAbsoluteInertiaRat
import Theorems.Thm_GlobalTheory_InertiaLift_exists_mem_Ine_lift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.style.haveILetI false
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField Pointwise
open GlobalTheory GlobalTheory.InertiaLift
variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
namespace GlobalTheory.InertiaLift
theorem _root_.solution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∀ (M : IntermediateField ℚ Ω) [FiniteDimensional ℚ M] [IsGalois ℚ M] (τ : M ≃ₐ[ℚ] M), (∀ x : M, A.valuation (x : Ω) ≤ 1 → A.valuation ((τ x : Ω) - (x : Ω)) < 1) → (∀ x : M, A.valuation ((τ x : M) : Ω) ≤ 1 ↔ A.valuation (x : Ω) ≤ 1) → ∃ σ ∈ Ine (F := ℚ) A, ∀ x : M, σ (x : Ω) = (τ x : Ω) := by
  intro Ω _ _ _ _ _ A _ M _ _ τ h _
  have hst : @IsScalarTower ℚ M Ω (DivisionRing.toRatAlgebra (R := M)).toSMul
      (inferInstance : Algebra M Ω).toSMul (‹Algebra ℚ Ω›).toSMul :=
    @IsScalarTower.of_algebraMap_eq' ℚ M Ω _ _ _ DivisionRing.toRatAlgebra _ _
      (Subsingleton.elim _ _)
  have e : (DivisionRing.toRatAlgebra : Algebra ℚ M) = M.algebra' := Subsingleton.elim _ _
  have hfd : @FiniteDimensional ℚ M _ _ (DivisionRing.toRatAlgebra (R := M)).toModule := by
    rw [e]; assumption
  exact @exists_mem_Ine_lift ℚ Ω _ _ _ _ _ A M _ DivisionRing.toRatAlgebra _ hst hfd _ τ h
end GlobalTheory.InertiaLift
