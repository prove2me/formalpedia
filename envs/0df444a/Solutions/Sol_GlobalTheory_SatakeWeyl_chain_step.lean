-- Prove2me | solution 1 for GlobalTheory.SatakeWeyl.chain_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:04:16.054851+00:00
-- url     : https://prove2.me/submissions/722957d1-cfe3-40ee-ae5b-365fcadd9490

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContractingAutomorphismSubgroupChainIndex
import Theorems.Thm_GlobalTheory_SatakeWeyl_chain_comap_eq
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.SatakeWeyl
namespace GlobalTheory.SatakeWeyl
theorem _root_.solution {A : Type} [Group A] (U : Subgroup A) (c : MulAut A) (hc : ∀ a ∈ U, c a ∈ U) (j : ℤ) :
    U.comap (c ^ j).toMonoidHom ≤ U.comap (c ^ (j + 1)).toMonoidHom ∧
      (U.comap (c ^ j).toMonoidHom).relIndex (U.comap (c ^ (j + 1)).toMonoidHom) =
        (U.map c.toMonoidHom).relIndex U := by
  rw [chain_comap_eq U c j]
  refine ⟨Subgroup.comap_mono ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact hc x hx
  · rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective]
    exact (c ^ (j + 1)).surjective
end GlobalTheory.SatakeWeyl
