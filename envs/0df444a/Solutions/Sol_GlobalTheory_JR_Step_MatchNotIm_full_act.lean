-- Prove2me | solution 1 for GlobalTheory.JR.Step.MatchNotIm.full_act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:09:45.041428+00:00
-- url     : https://prove2.me/submissions/6c3cb493-4059-4283-9c3e-5b2514a34d89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_BorderedInvariantsAndHankelDetMapRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariantsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Step GlobalTheory.JR.Step.MatchNotIm
variable {r : ℕ} {k : Type} [CommRing k]
namespace GlobalTheory.JR.Step.MatchNotIm
theorem _root_.solution (g : GL (Fin r) k) (Y : Gl r k) :
    full (act g Y) = embHom r k (g : Matrix (Fin r) (Fin r) k) * full Y *
      embHom r k ((g⁻¹ : GL (Fin r) k) : Matrix (Fin r) (Fin r) k) := by
  simp only [full, act, embHom, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1
  congr 1
  all_goals (ext i j; simp [Matrix.mul_apply, Matrix.mulVec, Matrix.vecMul, dotProduct])
end GlobalTheory.JR.Step.MatchNotIm
