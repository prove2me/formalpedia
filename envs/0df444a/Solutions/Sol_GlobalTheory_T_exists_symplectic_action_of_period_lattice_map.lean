-- Prove2me | solution 1 for GlobalTheory.T.exists_symplectic_action_of_period_lattice_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:22:45.070934+00:00
-- url     : https://prove2.me/submissions/04b2f6c8-fac1-40da-8946-b21db2ab763d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsSymplecticActionOfPeriodLatticeMap
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsSymplecticActionOfPeriodLatticeMapStatement
import Theorems.Thm_GlobalTheory_SymplecticPeriods_exists_symplectic_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : ((ι → ℚ) × (ι → ℚ)) →ₗ[ℚ] ((ι → ℚ) × (ι → ℚ))), (∀ u v, (F u).1 ⬝ᵥ (F v).2 - (F u).2 ⬝ᵥ (F v).1 = u.1 ⬝ᵥ v.2 - u.2 ⬝ᵥ v.1) → ∃ σ ∈ Matrix.symplecticGroup ι ℚ, ∀ τ ∈ Siegel ι, ∀ τ' M : Matrix ι ι ℂ, τ'.IsSymm → (∀ u, M *ᵥ (qv u.1 + τ *ᵥ qv u.2) = qv (F u).1 + τ' *ᵥ qv (F u).2) → τ' = spAct σ τ ∧ M = ((spDen σ τ)⁻¹)ᵀ := by
  first | exact @GlobalTheory.SymplecticPeriods.exists_symplectic_action | exact GlobalTheory.SymplecticPeriods.exists_symplectic_action | (intros; apply GlobalTheory.SymplecticPeriods.exists_symplectic_action <;> assumption)
end _root_.GlobalTheory.T
