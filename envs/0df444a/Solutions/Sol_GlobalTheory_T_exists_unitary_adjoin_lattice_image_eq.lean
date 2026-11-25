-- Prove2me | solution 1 for GlobalTheory.T.exists_unitary_adjoin_lattice_image_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:00:00.138086+00:00
-- url     : https://prove2.me/submissions/57a500f1-0bbf-4993-9c10-6fb363035eab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEq
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitaryAdjoinLatticeImageEqStatement
import Theorems.Thm_GlobalTheory_FormalIsogeny_FiniteReduction_map
import Theorems.Thm_GlobalTheory_LatOrb_exists_unitary_matLat_eq


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
    ∀ σ : K →+* K, (∀ x, σ (σ x) = x) → (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    (γ.map σ)ᵀ * γ = 1 →
    ∀ M : Submodule O (Fin n → K), IsLatV O M → (∀ v ∈ M, γ *ᵥ v ∈ M) →
    ∀ p : K[X], IsUnit (aeval γ p) → matLat O (((aeval γ p).map σ)ᵀ * aeval γ p) M = M →
    ∃ t : Matrix (Fin n) (Fin n) K, (t.map σ)ᵀ * t = 1 ∧ t * γ = γ * t ∧ matLat O t M = matLat O (aeval γ p) M := by
  first | exact @GlobalTheory.LatOrb.exists_unitary_matLat_eq | exact GlobalTheory.LatOrb.exists_unitary_matLat_eq | (intros; apply GlobalTheory.LatOrb.exists_unitary_matLat_eq <;> assumption)
end _root_.GlobalTheory.T
