-- Prove2me | solution 1 for GlobalTheory.Chow.map_rename_elimIdeal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:31:13.809653+00:00
-- url     : https://prove2.me/submissions/0df6498e-ba3e-4354-9a78-8c45310c40b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
import Theorems.Thm_GlobalTheory_Chow_rename_mem_elimIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {K : Type*} [CommRing K] {σ β β' : Type*} [Fintype σ]
namespace GlobalTheory.Chow
theorem _root_.solution (e : β ≃ β') (p : Ideal (MvPolynomial σ K)) :
    (elimIdeal β p).map (rename (Prod.map e id) : _ →ₐ[K] _) = elimIdeal β' p := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.2 fun f hf => rename_mem_elimIdeal e hf) ?_
  intro f hf
  have := Ideal.mem_map_of_mem (rename (Prod.map e id : β × σ → β' × σ) : _ →ₐ[K] _)
    (rename_mem_elimIdeal e.symm hf)
  rwa [rename_rename, Prod.map_comp_map, e.self_comp_symm, Function.id_comp, Prod.map_id,
    rename_id_apply] at this
end GlobalTheory.Chow
