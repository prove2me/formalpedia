-- Prove2me | solution 1 for GlobalTheory.BI.character_extendScalarsRep
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:22:46.644865+00:00
-- url     : https://prove2.me/submissions/2041acbf-0d44-402a-8817-73298994917e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_CharacterExtendScalarsRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.BI
noncomputable section
open GlobalTheory GlobalTheory.BI
namespace GlobalTheory.BI
theorem _root_.solution (K L : Type) [Field K] [Field L] [Algebra K L] {G : Type}
    [Group G] {n : ℕ} (ρ : Representation K G (Fin n → K)) (g : G) :
    (extendScalarsRep K L ρ).character g = algebraMap K L (ρ.character g) := by
  have h1 : (extendScalarsRep K L ρ).character g
      = ((LinearMap.toMatrix' (ρ g)).map (algebraMap K L)).trace := by
    change LinearMap.trace L _ (Matrix.toLin' _) = _
    exact Matrix.trace_toLin'_eq _
  have h2 : ρ.character g = (LinearMap.toMatrix' (ρ g)).trace := by
    change LinearMap.trace K _ (ρ g) = _
    rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_toMatrix']
  rw [h1, h2]
  simp [Matrix.trace, map_sum]
end GlobalTheory.BI
