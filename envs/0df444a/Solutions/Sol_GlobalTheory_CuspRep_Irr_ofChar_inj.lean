-- Prove2me | solution 1 for GlobalTheory.CuspRep.Irr.ofChar_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:50:35.794589+00:00
-- url     : https://prove2.me/submissions/ff5f74a8-4309-46ee-9685-eb5d65ed5bfd

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsIrreducibleIff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Topology
open GlobalTheory GlobalTheory.CuspRep
variable {G : Type} [Group G]
variable [TopologicalSpace G]
attribute [instance] SmIrr.acg SmIrr.mod
variable [IsTopologicalGroup G]
namespace GlobalTheory.CuspRep
namespace Irr
theorem _root_.solution {χ χ' : G →* ℂˣ} {hχ : IsOpen {g | χ g = 1}} {hχ' : IsOpen {g | χ' g = 1}}
    (h : Irr.ofChar χ hχ = Irr.ofChar χ' hχ') : χ = χ' := by
  obtain ⟨e⟩ : Nonempty ((twRep (Representation.trivial ℂ G ℂ) χ).Equiv (twRep (Representation.trivial ℂ G ℂ) χ')) :=
    Quotient.exact h
  ext g
  have h1 : e (((χ g : ℂˣ) : ℂ) • (1 : ℂ)) = ((χ' g : ℂˣ) : ℂ) • e (1 : ℂ) :=
    LinearMap.congr_fun (e.isIntertwining' g) (1 : ℂ)
  rw [map_smul] at h1
  exact smul_left_injective ℂ ((map_ne_zero_iff e e.injective).2 (one_ne_zero (α := ℂ))) h1
end Irr
end GlobalTheory.CuspRep
