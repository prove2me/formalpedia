-- Prove2me | solution 1 for GroundTheory.LocalField.exists_ringEquiv_laurentSeries_of_charP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:47:34.740592+00:00
-- url     : https://prove2.me/submissions/6d0ede2b-4e18-45ad-ae07-59a45c452749

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Examples
import Definitions.Def_GroundTheory_LocalFields_ExamplesTeichmuller
import Definitions.Def_GroundTheory_LocalFields_ExamplesLaurent
import Theorems.Thm_GroundTheory_LocalField_continuous_of_vle_iff
import Theorems.Thm_GroundTheory_LocalField_EqualChar_laurentHom_vle_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries
open GroundTheory GroundTheory.LocalField
open ValuativeRel Polynomial IsLocalRing Topology Filter WithZero HahnSeries
namespace GroundTheory.LocalField
theorem _root_.solution (K : Type*) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ e : K ≃+* 𝓀[K]⸨X⸩, (∀ x y, e x ≤ᵥ e y ↔ x ≤ᵥ y) ∧ Continuous e ∧ Continuous e.symm := by
  set f := EqualChar.laurentEquiv K p
  have hf (x y : 𝓀[K]⸨X⸩) : f x ≤ᵥ f y ↔ x ≤ᵥ y := EqualChar.laurentHom_vle_iff K p x y
  have hfs (x y : K) : f.symm x ≤ᵥ f.symm y ↔ x ≤ᵥ y := by
    rw [← hf, f.apply_symm_apply, f.apply_symm_apply]
  refine ⟨f.symm, hfs, ?_, ?_⟩
  · exact continuous_of_vle_iff f.symm.toRingHom hfs f.symm.surjective
  · exact continuous_of_vle_iff f.toRingHom hf f.surjective
end GroundTheory.LocalField
