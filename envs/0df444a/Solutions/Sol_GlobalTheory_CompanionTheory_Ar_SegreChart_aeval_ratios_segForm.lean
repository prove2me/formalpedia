-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_ratios_segForm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:36:06.252247+00:00
-- url     : https://prove2.me/submissions/5e9c5fb7-ee10-4bd6-a6b1-8a22e1ab4e54

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_segForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.SncRes
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SegreChart
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω] [CharZero Ω] {r : ℕ}
omit [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (c : (k : K ⊕ Unit) → joinIdx ι (fun _ : Unit => Fin (r + 1)) k)
    (a : Fin (N + 1)) (hEa : ∀ k, E a k = c (Sum.inl k)) :
    aeval (fun p : Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k => joinPt y x' p / joinPt y x' ⟨p.1, c p.1⟩)
        (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)) =
      aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E a k⟩) (map (algebraMap ℤ ℚ) Gz) := by
  rw [aeval_rename, aeval_segForm, aeval_map_algebraMap]
  congr 2
  funext j
  simp only [← Finset.prod_div_distrib, hEa]
  rfl
end GlobalTheory.CompanionTheory.Ar.SegreChart
