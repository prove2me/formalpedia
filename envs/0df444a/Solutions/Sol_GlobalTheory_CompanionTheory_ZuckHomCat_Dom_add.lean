-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ZuckHomCat.Dom.add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:30.262361+00:00
-- url     : https://prove2.me/submissions/5fac90b4-74a4-4297-b2bf-394e7279ebbf

import Mathlib
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_SmoothCyclicVectors_SmoothCyc
import Definitions.Def_CompanionTheory_AutomorphicTheory_ZuckermanCommutation_ZuckermanFunctors_IsSimpleFam
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HomCategory
import Theorems.Thm_P2M_GlobalTheory_CompanionTheory_ZuckHomCat_sum_nonneg__c895c5f25bf0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ZuckHomCat
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData CompanionTheory.D.Upq.Sm
variable {k r : ℕ}
namespace GlobalTheory.CompanionTheory.ZuckHomCat
namespace Dom
theorem _root_.solution {X : Obj k r} {φ ψ : M X → ℝ} (h : Dom X φ) (h' : Dom X ψ) :
    Dom X fun x => φ x + ψ x := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  obtain ⟨C', Ws', hW', hb'⟩ := h'
  refine ⟨|C| + |C'|, Ws ++ Ws', fun W hm => (List.mem_append.1 hm).elim (hW W) (hW' W), fun x => ?_⟩
  rw [List.map_append, List.sum_append]
  have h1 := sum_nonneg' X Ws x
  have h2 := sum_nonneg' X Ws' x
  have h3 := hb x
  have h4 := hb' x
  have h5 := mul_le_mul_of_nonneg_right (le_abs_self C) h1
  have h6 := mul_le_mul_of_nonneg_right (le_abs_self C') h2
  have h7 := mul_nonneg (abs_nonneg C) h2
  have h8 := mul_nonneg (abs_nonneg C') h1
  nlinarith
end Dom
end GlobalTheory.CompanionTheory.ZuckHomCat
