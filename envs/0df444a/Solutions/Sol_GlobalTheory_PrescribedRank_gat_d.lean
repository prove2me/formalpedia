-- Prove2me | solution 1 for GlobalTheory.PrescribedRank.gat_d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:55:43.446836+00:00
-- url     : https://prove2.me/submissions/d909c368-9c50-4735-a6ca-7eb482d4264d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
import Theorems.Thm_GlobalTheory_PrescribedRank_constMap_injective
import Theorems.Thm_GlobalTheory_PrescribedRank_range_constMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
namespace GlobalTheory.PrescribedRank
theorem _root_.solution (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) : (gat p O Kf d).d = d := by
  have h : (gat p O Kf d).d = Module.finrank O
      (Submodule.pi Set.univ fun _ : Fin d => (trivLevel p O Kf).funMod (noPlaces p O Kf).HtupW) := rfl
  rw [h, ← range_constMap, LinearMap.finrank_range_of_inj (constMap_injective p O Kf d hinj)]
  simp
end GlobalTheory.PrescribedRank
