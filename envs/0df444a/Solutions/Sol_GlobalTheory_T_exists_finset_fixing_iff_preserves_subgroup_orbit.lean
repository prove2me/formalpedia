-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_fixing_iff_preserves_subgroup_orbit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T15:50:15.264002+00:00
-- url     : https://prove2.me/submissions/fcb715a1-5901-4a92-afc9-60fa22603908

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingIffPreservesSubgroupOrbit
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingIffPreservesSubgroupOrbitStatement
import Theorems.Thm_GlobalTheory_orbit_stab_cut_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (H : Subgroup (G E Ω)) (y : Ω), ∃ s : Finset Ω, ∀ σ : G E Ω, (∀ x ∈ s, σ x = x) ↔ ∀ τ ∈ H, ∃ τ' ∈ H, σ (τ y) = τ' y := by
  first | exact @GlobalTheory.orbit_stab_cut_finite | exact GlobalTheory.orbit_stab_cut_finite | (intros; apply GlobalTheory.orbit_stab_cut_finite <;> assumption)
end _root_.GlobalTheory.T
