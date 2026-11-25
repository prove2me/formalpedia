-- Prove2me | solution 1 for GlobalTheory.PrimScale.exists_conj_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:36.735827+00:00
-- url     : https://prove2.me/submissions/eaa0d89f-8014-4c5e-88f9-0a6df0fd6c87

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
import Theorems.Thm_GlobalTheory_PrimScale_exists_pow_mul_mem
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_CongGrp_exists_pow_mul_mem
import Theorems.Thm_GlobalTheory_CongTrans_exists_pow_mul_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.PrimScale
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.PrimScale
theorem _root_.solution (L : LocE F E) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) {m : ℕ}
    (A : Matrix (Fin m) (Fin m) E) (hA : IsUnit A.det) :
    ∃ k : ℕ, ∀ i ≥ k, ∀ K ∈ congK L ϖ m i, IsIntM L (A * K * A⁻¹) := by
  choose k hk using fun p : Fin m × Fin m × Fin m × Fin m =>
    exists_pow_mul_mem L hϖ (A p.1 p.2.1 * A⁻¹ p.2.2.1 p.2.2.2)
  refine ⟨Finset.univ.sup k, fun i hi K hK a b => ?_⟩
  have h1 : A * K * A⁻¹ = 1 + A * (K - 1) * A⁻¹ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_nonsing_inv _ hA]; abel
  rw [h1, Matrix.add_apply]
  refine Subring.add_mem _ ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · simp only [Matrix.mul_apply, Finset.sum_mul]
    refine Subring.sum_mem _ fun s _ => Subring.sum_mem _ fun r _ => ?_
    obtain ⟨c, hc, h⟩ := hK r s
    rw [Matrix.sub_apply, h]
    have := Subring.mul_mem _ (hk (a, r, s, b) i
      (le_trans (Finset.le_sup (Finset.mem_univ _)) hi)) hc
    convert this using 1
    ring
end GlobalTheory.PrimScale
