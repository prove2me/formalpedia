-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.genLow_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:19:18.793842+00:00
-- url     : https://prove2.me/submissions/648f36f2-fb20-4260-9778-e4eee6533bfe

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
theorem _root_.solution (f : MvPolynomial (LowIdx Ψ N j) R →+* S) {H : Ψ → Matrix (Fin N) (Fin N) S}
    (hH : ∀ τ, IsBlockDiag j (H τ) ∧ IsLowerUni (H τ)) (hf : ∀ q, f (X q) = H q.1.1 q.1.2.1 q.1.2.2) (τ : Ψ) :
    (genLow R N j τ).map f = H τ := by
  ext a b
  rw [Matrix.map_apply, genLow]
  split_ifs with h e
  · exact hf _
  · rw [map_one, e, (hH τ).2.1]
  · rw [map_zero]
    rcases lt_or_gt_of_ne e with e | e
    · exact ((hH τ).2.2 a b e).symm
    · exact ((hH τ).1 a b fun e' => h ⟨e, e'⟩).symm
end GlobalTheory.CompanionTheory.Ar.PB
