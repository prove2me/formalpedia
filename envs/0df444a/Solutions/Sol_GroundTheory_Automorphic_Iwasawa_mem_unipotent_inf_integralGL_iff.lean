-- Prove2me | solution 1 for GroundTheory.Automorphic.Iwasawa.mem_unipotent_inf_integralGL_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:19:27.227866+00:00
-- url     : https://prove2.me/submissions/e2a06bad-f6d2-44d3-93f6-49e98e208b8d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Theorems.Thm_GroundTheory_Automorphic_Iwasawa_mem_borel_inf_integralGL_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open ValuativeRel Matrix Filter
open scoped Pointwise
open GroundTheory.Automorphic.Iwasawa
open GLnLocal
variable (F : Type*) [Field F] (n : ℕ)
variable [ValuativeRel F]
namespace GroundTheory.Automorphic.Iwasawa
theorem _root_.solution {g : GL (Fin n) F} :
    g ∈ unipotent F n ⊓ integralGL F n ↔ g ∈ unipotent F n ∧ ∀ i j, g i j ∈ 𝒪[F] := by
  constructor
  · rintro ⟨hN, hK⟩
    exact ⟨hN, ((mem_integralGL_iff F n).1 hK).1⟩
  · rintro ⟨hN, h1⟩
    exact ⟨hN, ((mem_borel_inf_integralGL_iff F n).2
      ⟨hN.1, h1, fun i => by rw [hN.2 i, map_one]⟩).2⟩
end GroundTheory.Automorphic.Iwasawa
