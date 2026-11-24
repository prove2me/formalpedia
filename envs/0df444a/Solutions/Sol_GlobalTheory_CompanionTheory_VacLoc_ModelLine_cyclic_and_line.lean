-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.VacLoc.ModelLine.cyclic_and_line
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:13:29.548675+00:00
-- url     : https://prove2.me/submissions/79329183-8021-42e4-b4a2-0243d29f1508

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MembershipCriteria_GoodChar
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_RationalFiniteIdeleFactorization
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_Irreducible
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_ExistsStdStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MembershipProofs_CyclicAndLine
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_Irred_irreducible
import Theorems.Thm_GlobalTheory_CompanionTheory_FinHeis_LawLine_law_line
import Theorems.Thm_GlobalTheory_T_schrodinger_model_selfDual_lattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.FinHeis GlobalTheory.WeilM MeasureTheory Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.VacLoc GlobalTheory.CompanionTheory.VacLoc.ModelLine
namespace GlobalTheory.CompanionTheory.VacLoc.ModelLine
theorem _root_.solution : ∀ {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [T2Space R] [Invertible (2 : R)] (ψ : AddChar R ℂ) (O : Subring R) (u : Rˣ) {W : Type} [AddCommGroup W] [Module R W]
    {B : W → W → R} {κ : Type} [Fintype κ] (d : Darboux B κ) (μ : @Measure (κ → R) (borel _)) (S : Sys W (SB (κ → R)))
    (Γ : AddSubgroup W) (al : W → ℂ) (φ φ' : SB (κ → R)), GoodChar ψ O u → IsModel ψ d μ S →
    (φ ≠ 0 → Cyclic S φ) ∧
      (SelfDual S Γ → IsSemi S al Γ → Law S al Γ φ → Law S al Γ φ' → φ ≠ 0 → ∃ a : ℂ, φ' = a • φ) := by
  intro R _ _ _ _ _ _ ψ O u W _ _ B κ _ d μ S Γ al φ φ' hg hm
  obtain ⟨Γ₀, al₀, φ₀, h1, h2, h3, h4, _⟩ := GlobalTheory.T.schrodinger_model_selfDual_lattice ψ O u d μ S hg hm
  have hcyc : φ ≠ 0 → Cyclic S φ := fun h =>
    (GlobalTheory.CompanionTheory.FinHeis.Irred.irreducible S al₀ Γ₀ φ₀ h1 h2 h3 h4).2 φ h
  refine ⟨hcyc, fun hΓ hal hφ hφ' h0 => ?_⟩
  exact GlobalTheory.CompanionTheory.FinHeis.LawLine.law_line S al Γ φ φ' hΓ hal hφ (hcyc h0) hφ'
end GlobalTheory.CompanionTheory.VacLoc.ModelLine
