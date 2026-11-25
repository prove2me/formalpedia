-- Prove2me | solution 1 for GlobalTheory.KTypeCompare.isWtOn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:11:55.295804+00:00
-- url     : https://prove2.me/submissions/9af84949-b517-43ca-9430-94bedaeaa127

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsWtOnIffOfTorus
import Theorems.Thm_GlobalTheory_KTypeCompare_Kset_eq
import Theorems.Thm_GlobalTheory_KTypeCompare_torus_mem
import Theorems.Thm_GlobalTheory_KTypeCompare_isWtOn_iff_of_torus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.KTypeCompare
open GlobalTheory.IndefiniteRowSideFullHecke
variable {n : ℕ}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.KTypeCompare
theorem _root_.solution (ε : Fin n → Bool)
    (σ : Matrix (Fin n) (Fin n) ℂ → H →L[ℂ] H) (ω : Fin n → ℝ) (v : H) :
    PI.UpqRep.IsWtOn (PI.UpqRep.Kset ε) σ ω v ↔ v ∈ HarishChandraRootData.weightSpace σ ω := by
  refine isWtOn_iff_of_torus _ (fun θ => ?_) σ ω v
  rw [Kset_eq]
  exact torus_mem ε θ
end GlobalTheory.KTypeCompare
