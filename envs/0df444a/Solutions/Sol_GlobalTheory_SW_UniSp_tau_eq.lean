-- Prove2me | solution 1 for GlobalTheory.SW.UniSp.tau_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:29:38.303057+00:00
-- url     : https://prove2.me/submissions/7d9f9c26-3007-49cb-8f6f-1803dcdd83f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsRationalSymplecticOfUnitaryCmField
import Theorems.Thm_GlobalTheory_SW_UniSp_conj_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.UniSp
noncomputable section
open Classical
variable {E : Type} [Field E] [NumberField E] {n : ℕ}
variable {Ψ : Finset (E →+* ℂ)} {N : ℕ}
namespace GlobalTheory.SW.UniSp
theorem _root_.solution (Z : CM Ψ N N) :
    tauOf Ψ Z = Sm Ψ N * blockDiagonal (fun τ => fromBlocks 0 (Z τ) (Z τ)ᵀ 0) * (Sm Ψ N)ᵀ := by
  ext p q
  rw [conj_apply]
  simp only [tauOf, Matrix.of_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [Sm, vecMul, dotProduct, Fintype.sum_sum_type]
  ring
end GlobalTheory.SW.UniSp
