-- Prove2me | solution 1 for GlobalTheory.HL.HermJacobian.det_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:43:52.191632+00:00
-- url     : https://prove2.me/submissions/de67d81e-1b5c-4f56-8a84-d8f11cf59d49

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsEqZpowMulUnit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelVolMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_RelativeLatticeVolumeOfDetValuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianMatrixCongruenceContentJacobian
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical Kronecker
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.HermJacobian
variable {E : Type} [CommRing E] {m : ℕ}
namespace GlobalTheory.HL.HermJacobian
theorem _root_.solution (B A : Matrix (Fin m) (Fin m) E) :
    LinearMap.det (sandwich B A) = (B.det * A.det) ^ m := by
  let c : (Fin m × Fin m → E) ≃ₗ[E] Matrix (Fin m) (Fin m) E :=
    { toFun := fun v => Matrix.of fun i j => v (i, j)
      invFun := fun X k => X k.1 k.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have h : sandwich B A = (c : _ →ₗ[E] _) ∘ₗ Matrix.toLin' (B ⊗ₖ A.transpose) ∘ₗ (c.symm : _ →ₗ[E] _) := by
    refine LinearMap.ext fun X => ?_
    ext i j
    show (B * X * A) i j = ∑ k : Fin m × Fin m, (B i k.1 * A k.2 j) * X k.1 k.2
    simp only [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h, LinearMap.det_conj, LinearMap.det_toLin', Matrix.det_kronecker, Matrix.det_transpose,
    Fintype.card_fin, mul_pow]
end GlobalTheory.HL.HermJacobian
