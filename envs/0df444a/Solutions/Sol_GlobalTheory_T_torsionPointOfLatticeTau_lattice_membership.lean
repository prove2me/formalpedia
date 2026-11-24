-- Prove2me | solution 1 for GlobalTheory.T.torsionPointOfLatticeTau_lattice_membership
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:36:06.837113+00:00
-- url     : https://prove2.me/submissions/de9ff94c-b7cf-4cc4-a583-b768a92ac018

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointOfLatticeTauLatticeMembership
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionPointOfLatticeTauLatticeMembershipStatement
import Theorems.Thm_GlobalTheory_WpFam_TorsMem_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (N : ℕ) [NeZero N] (τ : ℍ), (∀ x y : Fin 2 → ZMod N, tors N τ x - tors N τ y ∈ (tauPair τ).lattice ↔ x = y) ∧ (∀ x y : Fin 2 → ZMod N, tors N τ (x + y) - (tors N τ x + tors N τ y) ∈ (tauPair τ).lattice) ∧ (∀ x : Fin 2 → ZMod N, tors N τ x ∈ (tauPair τ).lattice ↔ x = 0) ∧ (∀ x : Fin 2 → ZMod N, (N : ℂ) * tors N τ x ∈ (tauPair τ).lattice) ∧ (∀ z : ℂ, (N : ℂ) * z ∈ (tauPair τ).lattice → ∃ x : Fin 2 → ZMod N, z - tors N τ x ∈ (tauPair τ).lattice) := by
  first | exact @GlobalTheory.WpFam.TorsMem.main | exact GlobalTheory.WpFam.TorsMem.main | (intros; apply GlobalTheory.WpFam.TorsMem.main <;> assumption)
end _root_.GlobalTheory.T
