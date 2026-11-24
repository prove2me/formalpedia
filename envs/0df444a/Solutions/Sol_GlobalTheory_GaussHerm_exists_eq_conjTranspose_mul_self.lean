-- Prove2me | solution 1 for GlobalTheory.GaussHerm.exists_eq_conjTranspose_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:09:54.881435+00:00
-- url     : https://prove2.me/submissions/68644b54-9439-44c2-a049-2471fbfe91c3

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_IsLocalHomeomorph
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralExpNegHermitianFormPosDef

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates
open scoped ComplexOrder
open GlobalTheory GlobalTheory.GaussHerm
namespace GlobalTheory.GaussHerm
theorem _root_.solution {n : ℕ} {T : Matrix (Fin n) (Fin n) ℂ}
    (hT : T.PosSemidef) : ∃ B : Matrix (Fin n) (Fin n) ℂ, T = B.conjTranspose * B := by
  open scoped MatrixOrder in
  have h0 : 0 ≤ T := Matrix.nonneg_iff_posSemidef.mpr hT
  have hs : (CFC.sqrt T).PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg T)
  exact ⟨CFC.sqrt T, by rw [hs.1.eq, CFC.sqrt_mul_sqrt_self T h0]⟩
end GlobalTheory.GaussHerm
