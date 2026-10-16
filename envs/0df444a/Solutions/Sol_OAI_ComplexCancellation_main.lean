-- Prove2me | solution 1 for OAI.ComplexCancellation.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:55:01.969212+00:00
-- url     : https://prove2.me/submissions/d439c0e3-2d68-413a-a056-72d1aa3618b3

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Main.lean:L31-L33
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.ComplexCancellation.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_ComplexCancellation_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler
import Definitions.Def_OAI_Algebra_AffineCancellation_Intertwining
import Theorems.Thm_OAI_ComplexCancellation_nonpolynomiality

-- ---- from OAI.Algebra.AffineCancellation.Dimension ----
namespace OAI

noncomputable section

namespace ComplexCancellation

theorem finiteType : Algebra.FiniteType ℂ A := inferInstance

theorem dimension : ringKrullDim A = 4 := by
  have hd : ringKrullDim A + 1 = 5 := by
    rw [← Polynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_of_ringEquiv Cylinder.equivalence.toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add]
    simp
  generalize ringKrullDim A = d at *
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe d =>
    have hd' : d + 1 = 5 := WithBot.coe_inj.mp (by
      simpa only [WithBot.coe_add, WithBot.coe_one, WithBot.coe_ofNat] using hd)
    induction d using ENat.recTopCoe with
    | top => simp at hd'
    | coe n =>
      have hd'' : n + 1 = 5 := by exact_mod_cast hd'
      have hn : n = 4 := by omega
      subst n
      rfl

theorem stabilization : Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) :=
  ⟨Cylinder.equivalence⟩

end ComplexCancellation

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Main ----
namespace OAI

noncomputable section

namespace ComplexCancellation
/-- A four-dimensional complex domain with polynomial cylinder, but not itself polynomial. -/
theorem main : MainStatement :=
  ⟨finiteType,domain,dimension,stabilization,nonpolynomiality⟩
end ComplexCancellation

end

end OAI

-- ---- mission target ----
open OAI OAI.ComplexCancellation

theorem solution : MainStatement := by
  first
    | exact OAI.ComplexCancellation.main
    | (apply OAI.ComplexCancellation.main <;> assumption)
    | (intros; apply OAI.ComplexCancellation.main <;> assumption)
