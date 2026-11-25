-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsGenericFlag.isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:32:28.132787+00:00
-- url     : https://prove2.me/submissions/471ec650-4276-4e87-a86e-25a60c1fdf94

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Statements_MetricStatements_AgreementIffGuarded
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_MetricPeriods_GenericBlockMatrixIsBlockDiag

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
namespace IsGenericFlag
theorem _root_.solution {Ω : Type} [CommRing Ω] [Algebra Ω R] {g : Ψ → Matrix (Fin N) (Fin N) R}
    (h : IsGenericFlag Ω j g) (τ : Ψ) : IsUnit (g τ).det := by
  obtain ⟨B, hB, -⟩ := h
  exact IsUnit.of_mul_eq_one (B τ).det (by rw [← det_mul, (hB τ).2.2.det])
end IsGenericFlag
end GlobalTheory.CompanionTheory.Ar.PB
