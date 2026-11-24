-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.OrbitSection.continuousOn_shear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:53:53.270425+00:00
-- url     : https://prove2.me/submissions/ec8879a9-47c3-4fe5-96af-edd4a7b81fc6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OrbitSection
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}
namespace GlobalTheory.CompanionTheory.OrbitSection
theorem _root_.solution (j : Fin n) (ζ : Fin n → k) {N : Set (Fin n → k)} {c : (Fin n → k) → k}
    (hc : ContinuousOn c N) : ContinuousOn (fun ξ => shear j (c ξ) ζ ξ) N := by
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  simp only [shear, Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, Pi.sub_apply, smul_eq_mul]
  refine continuousOn_const.add (hc.mul (continuousOn_const.mul ?_))
  exact ((continuous_apply b).sub continuous_const).continuousOn
end GlobalTheory.CompanionTheory.OrbitSection
