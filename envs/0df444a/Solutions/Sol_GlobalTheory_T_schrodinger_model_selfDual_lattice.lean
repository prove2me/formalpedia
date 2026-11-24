-- Prove2me | solution 1 for GlobalTheory.T.schrodinger_model_selfDual_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:57:06.683321+00:00
-- url     : https://prove2.me/submissions/9aee2723-7ea9-41c2-9ba6-93f0bbf1b58e

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStd
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStdStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_StdLattice_exists_std


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W] {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R))), GoodChar ψ O u → IsModel ψ d μ S → ∃ (Γ : AddSubgroup W) (al : W → ℂ) (φ : SB (κ → R)), SelfDual S Γ ∧ IsSemi S al Γ ∧ Law S al Γ φ ∧ Cyclic S φ ∧ φ ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.StdLattice.exists_std | exact GlobalTheory.CompanionTheory.StdLattice.exists_std | (intros; apply GlobalTheory.CompanionTheory.StdLattice.exists_std <;> assumption)
end _root_.GlobalTheory.T
