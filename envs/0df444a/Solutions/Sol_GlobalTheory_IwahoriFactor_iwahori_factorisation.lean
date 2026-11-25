-- Prove2me | solution 1 for GlobalTheory.IwahoriFactor.iwahori_factorisation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:58:07.259956+00:00
-- url     : https://prove2.me/submissions/8ebdb5a4-2afd-424e-9b3b-29957d2ea602

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UdlApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IwahoriFactorisation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DvdInvOfBlockTriangular
import Theorems.Thm_GlobalTheory_IwahoriFactor_existsUnique_factor
import Theorems.Thm_GlobalTheory_IwahoriFactor_not_isUnit_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.IwahoriFactor
namespace GlobalTheory.IwahoriFactor
theorem _root_.solution : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (n r s : ℕ), 1 ≤ s → ∀ g : GL (Fin n) O, (∀ i j, (i < j → ϖ ^ r ∣ (g : Matrix (Fin n) (Fin n) O) i j) ∧ (j < i → ϖ ^ s ∣ (g : Matrix (Fin n) (Fin n) O) i j)) → ∃! p : Matrix (Fin n) (Fin n) O × (Fin n → Oˣ) × Matrix (Fin n) (Fin n) O, (∀ i j, (j < i → p.1 i j = 0) ∧ (i = j → p.1 i j = 1) ∧ (i < j → ϖ ^ r ∣ p.1 i j)) ∧ (∀ i j, (i < j → p.2.2 i j = 0) ∧ (i = j → p.2.2 i j = 1) ∧ (j < i → ϖ ^ s ∣ p.2.2 i j)) ∧ (g : Matrix (Fin n) (Fin n) O) = p.1 * Matrix.diagonal (fun i => (p.2.1 i : O)) * p.2.2 := by
  intro O _ _ _ ϖ hϖ n r s hs g hg
  exact existsUnique_factor (not_isUnit_pow hϖ hs) g hg
end GlobalTheory.IwahoriFactor
