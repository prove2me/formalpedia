-- Prove2me | solution 1 for GroundTheory.Global.finrank_kummerExtension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:45:29.429212+00:00
-- url     : https://prove2.me/submissions/72529427-8b52-43ea-ad36-7f2de8a72f4c

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerCorrespondence
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Theorems.Thm_GroundTheory_ProfCoh_finrank_kummerField


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.ProfCoh IntermediateField
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (Ω : Type*) [Field Ω] [Algebra K Ω] (Δ : Subgroup Kˣ)
variable [IsSepClosed Ω]
variable [Finite (Δ ⧸ (unitsPow K n).subgroupOf Δ)]
namespace GroundTheory.Global
theorem _root_.solution :
    Module.finrank K (kummerExtension K n Ω Δ) = Nat.card (Δ ⧸ (unitsPow K n).subgroupOf Δ) := by
  rw [kummerExtension_eq_kummerField, finrank_kummerField,
    Nat.card_congr (radicalQuotientEquiv K n Δ).toEquiv]
end GroundTheory.Global
