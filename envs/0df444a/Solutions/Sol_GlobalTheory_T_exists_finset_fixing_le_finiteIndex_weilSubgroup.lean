-- Prove2me | solution 1 for GlobalTheory.T.exists_finset_fixing_le_finiteIndex_weilSubgroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:59:58.388854+00:00
-- url     : https://prove2.me/submissions/aa875b91-1fcd-4a51-87cd-464bb4be862e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingLeFiniteIndexWeilSubgroup
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinsetFixingLeFiniteIndexWeilSubgroupStatement
import Theorems.Thm_GlobalTheory_WeilOpenFin_exists_finset_fix_le


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
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), (∀ (σ : G E Ω) (s : Finset Ω), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ s, (σ ^ m) x = x) → (∀ k : ℕ, 0 < k → ∃ ζ : Ω, ∀ σ : Weil h, (σ : G E Ω) ζ = ζ → (k : ℤ) ∣ deg σ) → (∀ M : Subgroup (Ine (F := E) A), IsOpen (M : Set (Ine (F := E) A)) → ∃ s : Finset Ω, ∀ σ : Ine (F := E) A, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ M) → ∀ H : Subgroup (Weil h), H.FiniteIndex → IsOpen {σ : Ine (F := E) A | ineIncl h σ ∈ H} → ∃ s : Finset Ω, ∀ σ : Weil h, (∀ x ∈ s, (σ : G E Ω) x = x) → σ ∈ H := by
  first | exact @GlobalTheory.WeilOpenFin.exists_finset_fix_le | exact GlobalTheory.WeilOpenFin.exists_finset_fix_le | (intros; apply GlobalTheory.WeilOpenFin.exists_finset_fix_le <;> assumption)
end _root_.GlobalTheory.T
