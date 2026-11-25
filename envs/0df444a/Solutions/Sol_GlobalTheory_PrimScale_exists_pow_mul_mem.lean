-- Prove2me | solution 1 for GlobalTheory.PrimScale.exists_pow_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:38:46.469375+00:00
-- url     : https://prove2.me/submissions/8c037456-7792-42fb-a0d9-2b99e3cc63bc

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCongruentOneModUniformizerPowGroupAndOrbitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobianStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TupleJacobianRightMulIsometryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimitiveTuplesHermitianGramCosetContentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsConjInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.PrimScale
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.PrimScale
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (e : E) :
    ∃ k : ℕ, ∀ i ≥ k, algebraMap F E ((ϖ : F) ^ i) * e ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ L.rank
  have he : IsIntegral F e := Algebra.IsIntegral.isIntegral e
  obtain ⟨⟨c, hc⟩, hce⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization (nonZeroDivisors 𝒪[F]) e he
  obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
    (nonZeroDivisors.ne_zero hc) hϖ
  refine ⟨k, fun i hi => ?_⟩
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [L.O_def]
  have h1 : IsIntegral 𝒪[F] (((u⁻¹ : (𝒪[F])ˣ) * ϖ ^ j : 𝒪[F]) • (((u : 𝒪[F]) * ϖ ^ k) • e)) :=
    IsIntegral.smul _ hce
  have h2 : ((u⁻¹ : (𝒪[F])ˣ) * ϖ ^ j : 𝒪[F]) * ((u : 𝒪[F]) * ϖ ^ k) = ϖ ^ (k + j) := by
    rw [pow_add]
    linear_combination (ϖ ^ j * ϖ ^ k) * u.inv_mul
  rw [smul_smul, h2, Algebra.smul_def, IsScalarTower.algebraMap_apply 𝒪[F] F E] at h1
  exact h1
end GlobalTheory.PrimScale
