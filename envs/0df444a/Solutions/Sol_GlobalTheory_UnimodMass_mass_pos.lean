-- Prove2me | solution 1 for GlobalTheory.UnimodMass.mass_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:37:37.901326+00:00
-- url     : https://prove2.me/submissions/f2fcaefa-0a1e-4fd9-bb38-9f4509506545

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_DoubleCosetSetoidRelIffMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FiniteDcOfCover
import Theorems.Thm_GlobalTheory_UnimodMass_stabCard_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnimodMass
variable {G : Type*} [Group G]
namespace GlobalTheory.UnimodMass
theorem _root_.solution {Γ K : Subgroup G} [Finite (DC Γ K)]
    (hfin : ∀ t : G, Finite {γ : Γ // t⁻¹ * (γ : G) * t ∈ K}) : 0 < mass Γ K := by
  haveI := Fintype.ofFinite (DC Γ K)
  rw [mass, finsum_eq_sum_of_fintype]
  have hne : (Finset.univ : Finset (DC Γ K)).Nonempty := ⟨Quotient.mk'' 1, Finset.mem_univ _⟩
  refine Finset.sum_pos (fun c _ => ?_) hne
  have := stabCard_pos c.out (hfin c.out)
  positivity
end GlobalTheory.UnimodMass
