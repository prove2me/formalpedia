-- Prove2me | solution 1 for GlobalTheory.SW.NbAvg.moves_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:23.551206+00:00
-- url     : https://prove2.me/submissions/e5e7a499-aa7d-4163-94b5-90af5462a048

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ClassSumNb
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


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
open scoped ComplexConjugate ComplexOrder Real Classical
open GlobalTheory GlobalTheory.SW
open GlobalTheory.SW.NbAvg
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
namespace GlobalTheory.SW.NbAvg
theorem _root_.solution {h : Matrix (Fin n) (Fin n) E} (hu : ccT h * h = 1) {B X Y : Lt E n}
    (h1 : Moves h B X) (h2 : Moves h B Y) : X = Y := by
  have hu' : h * ccT h = 1 := mul_eq_one_comm.1 hu
  ext w
  have hw : h *ᵥ (ccT h *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]
  have key := (h1 (ccT h *ᵥ w)).symm.trans (h2 (ccT h *ᵥ w))
  rwa [hw] at key
end GlobalTheory.SW.NbAvg
