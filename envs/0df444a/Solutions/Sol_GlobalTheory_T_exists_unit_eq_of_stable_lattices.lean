-- Prove2me | solution 1 for GlobalTheory.T.exists_unit_eq_of_stable_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:59:58.795163+00:00
-- url     : https://prove2.me/submissions/71b354af-5248-4a63-b094-870e089edd00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitEqOfStableLattices
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitEqOfStableLatticesStatement
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_LatOrb_Stab_exists_unit_eq_matLat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    (n : ℕ) (P₀ : O[X]), IsCoprime P₀ (derivative P₀) →
    ∀ γ : Matrix (Fin n) (Fin n) K, γ.charpoly = P₀.map (algebraMap O K) →
    ∀ M₁ M₂ : Submodule O (Fin n → K), IsLatV O M₁ → IsLatV O M₂ →
    (∀ v ∈ M₁, γ *ᵥ v ∈ M₁) → (∀ v ∈ M₂, γ *ᵥ v ∈ M₂) →
    ∃ p : K[X], IsUnit (aeval γ p) ∧ M₂ = matLat O (aeval γ p) M₁ := by
  first | exact @GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat | exact GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat | (intros; apply GlobalTheory.LatOrb.Stab.exists_unit_eq_matLat <;> assumption)
end _root_.GlobalTheory.T
