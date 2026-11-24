-- Prove2me | solution 1 for GlobalTheory.PairOp.U_dia
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:41.009375+00:00
-- url     : https://prove2.me/submissions/2fc0e544-eeb7-4042-ab36-13e042abe0f8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_AdjointOperatorIdentities
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PairOperatorStatement
import Theorems.Thm_GlobalTheory_PairOp_cross_dia
import Theorems.Thm_GlobalTheory_PairOp_sumOp_dia

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.IndefiniteRowSideFullHecke.AdjointOperatorIdentities
noncomputable section
open GlobalTheory GlobalTheory.PairOp
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
  {M : Type} [AddCommGroup M] [Module ℂ M]
variable (q : Unif k) (χ : AddChar 𝓀[k] ℂ)
namespace GlobalTheory.PairOp
theorem _root_.solution (c : 𝓀[k]ˣ) : (U q * dia c : Module.End ℂ (Form k n M)) = dia c * U q := by
  unfold U
  refine sumOp_dia _ _ c (fun P Q => ?_) fun _ _ _ => rfl
  simp only [Finset.mem_filter, mem_withKer, Pair.dia_lat, Pair.dia_ker]
  constructor
  · rintro ⟨h, h'⟩; exact ⟨h, by rw [cross_dia q h.symm, h']⟩
  · rintro ⟨h, h'⟩; exact ⟨h, by rw [← cross_dia q h.symm c, h']⟩
end GlobalTheory.PairOp
