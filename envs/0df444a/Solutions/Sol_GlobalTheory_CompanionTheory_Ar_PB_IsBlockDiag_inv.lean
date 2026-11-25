-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.PB.IsBlockDiag.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:01:46.96973+00:00
-- url     : https://prove2.me/submissions/4e55d5bd-1901-47f1-86f6-f0f78dfbdd3d

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
namespace IsBlockDiag
theorem _root_.solution {A : Matrix (Fin N) (Fin N) R} (hA : IsBlockDiag j A) (hd : IsUnit A.det) :
    IsBlockDiag j A⁻¹ := by
  letI := Matrix.invertibleOfIsUnitDet A hd
  let f : Fin N → ℕ := fun a => if (a : ℕ) < N - j then 0 else 1
  have h1 : A.BlockTriangular f := fun a b h => hA a b fun e => by
    simp only [f, e] at h; exact lt_irrefl _ h
  have h2 : A.BlockTriangular (OrderDual.toDual ∘ f) := fun a b h => hA a b fun e => by
    simp only [f, Function.comp, e] at h; exact lt_irrefl _ h
  intro a b h
  by_cases ha : (a : ℕ) < N - j
  · have hb : ¬ (b : ℕ) < N - j := fun hb => h (iff_of_true ha hb)
    exact blockTriangular_inv_of_blockTriangular h2 (show f a < f b by simp [f, ha, hb])
  · have hb : (b : ℕ) < N - j := by by_contra hb; exact h (iff_of_false ha hb)
    exact blockTriangular_inv_of_blockTriangular h1 (by simp [f, ha, hb])
end IsBlockDiag
end GlobalTheory.CompanionTheory.Ar.PB
