-- Prove2me | solution 1 for GlobalTheory.LevQuot.exists_subgroup_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:41:29.915639+00:00
-- url     : https://prove2.me/submissions/d6b14404-45bf-43bf-bc39-5fa30226fb35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSubgroupOfFinite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory GlobalTheory.LevQuot
variable {X Y : Scheme.{0}}
namespace GlobalTheory.LevQuot
theorem _root_.solution {G : Type} [Group G] (S : Submonoid G) [Finite S] :
    ∃ T : Subgroup G, ∀ g, g ∈ T ↔ g ∈ S := by
  refine ⟨{ S with inv_mem' := fun {x} hx => ?_ }, fun _ => Iff.rfl⟩
  have hx' : IsOfFinOrder x := by
    by_contra hne
    have hinj := injective_pow_iff_not_isOfFinOrder.mpr hne
    exact not_injective_infinite_finite (fun n : ℕ => (⟨x ^ n, S.pow_mem hx n⟩ : S))
      (fun a b hab => hinj (congrArg Subtype.val hab))
  obtain ⟨n, hn⟩ := hx'.mem_powers_iff_mem_zpowers.mpr (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  rw [← hn]
  exact S.pow_mem hx n
end GlobalTheory.LevQuot
