-- Prove2me | solution 1 for GlobalTheory.OneSpace.gram_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:19.697267+00:00
-- url     : https://prove2.me/submissions/098a4376-3558-4cbb-8d17-b68bbabd6160

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetMulVolMulConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsHermCoordOfDatum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FinrankEqOfInjectiveOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_SignatureHermitianModelOfDatumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsBinaryEqAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ConjEqNegOfSqEqNegNat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HermitianFormsSameSignatureSameSpace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.OneSpace
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.OneSpace
theorem _root_.solution {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (p : ℕ)
    (h : ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram (ComplexEmbedding.conjugate τ) G Q =
        Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ)) :
    ∃ Q : Matrix (Fin r) (Fin r) ℂ, Q.det ≠ 0 ∧
      FD.gram τ G Q = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  obtain ⟨Q, hQ, h⟩ := h
  refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
  · have h2 : (Q.map (starRingEnd ℂ)).det = starRingEnd ℂ Q.det := (RingHom.map_det _ Q).symm
    rw [h2]
    simpa using hQ
  · ext a b
    have := congrArg (starRingEnd ℂ) (congrFun (congrFun h a) b)
    simp only [FD.gram, FD.hermC, FD.col, Matrix.of_apply, Matrix.map_apply, map_sum, map_mul,
      ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj, Matrix.diagonal_apply] at this ⊢
    rw [this]
    split_ifs <;> simp
end GlobalTheory.OneSpace
