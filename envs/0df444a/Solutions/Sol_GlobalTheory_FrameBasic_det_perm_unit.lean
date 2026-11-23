-- Prove2me | solution 1 for GlobalTheory.FrameBasic.det_perm_unit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:04.70423+00:00
-- url     : https://prove2.me/submissions/7bb12f72-95d9-4e5c-a9ad-ddc1295a4d95

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_BasisOfIsCompl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical TensorProduct
open GlobalTheory GlobalTheory.FrameBasic
variable {E : Type} [CommRing E]
namespace GlobalTheory.FrameBasic
theorem _root_.solution {n : ℕ} (σ : Fin n → Fin n) (h : Function.Injective σ) :
    IsUnit ((1 : Matrix (Fin n) (Fin n) E).submatrix σ id).det := by
  have hb := Finite.injective_iff_bijective.1 h
  have := Matrix.det_permute (Equiv.ofBijective σ hb) (1 : Matrix (Fin n) (Fin n) E)
  rw [Equiv.coe_ofBijective] at this
  rw [this, Matrix.det_one, mul_one]
  exact (Units.isUnit _).map (Int.castRingHom E)
end GlobalTheory.FrameBasic
