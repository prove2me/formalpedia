-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.genUp_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:59:56.49159+00:00
-- url     : https://prove2.me/submissions/dc266f53-d07e-4fc8-913e-fdd609af0a69

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_PB_VertClose_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
variable {R : Type} [CommRing R] {N : ℕ} {Ψ : Type}
variable {j : ℕ} {S : Type} [CommRing S]
namespace GlobalTheory.CompanionTheory.Ar.PB
theorem _root_.solution (f : MvPolynomial (UpIdx Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ) ∧ (H τ).BlockTriangular id) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2)
    (τ : Ψ) : (genUp R N j τ).map f = H τ := by
  ext a b
  rw [Matrix.map_apply, genUp]
  split_ifs with h
  · exact hf _
  · rw [map_zero]
    by_cases e : a ≤ b
    · exact ((hH τ).1 a b fun e' => h ⟨e, e'⟩).symm
    · exact ((hH τ).2 (not_le.1 e)).symm
end GlobalTheory.CompanionTheory.Ar.PB
