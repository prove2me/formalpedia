-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.SegreChart.mem_mcPts_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:35:58.270573+00:00
-- url     : https://prove2.me/submissions/7999a62c-e382-4c7d-a40f-78021f597173

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_SncChartPoint
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_HomogeneousFormNonvanishingPoint
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_aeval_segForm
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_eval_map_int
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_rename_inl_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_SegreChart_evC_rename_inl

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
namespace GlobalTheory.CompanionTheory.Ar.SegreChart
theorem _root_.solution (y : (Σ k, ι k) → Ω) (x' : Fin (r + 1) → Ω) (β : MRing ι) {N : ℕ}
    (E : Fin (N + 1) ≃ ((k : K) → ι k)) (Gz : MvPolynomial (Fin (N + 1)) ℤ)
    (hβ : ∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 →
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) = 0)
    (z : (Σ k, joinIdx ι (fun _ : Unit => Fin (r + 1)) k) → ℂ) (hz : z ∈ mcPts (mCoordIdeal (joinPt y x')))
    (hb : evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) β) = 0) :
    z ∈ mcPts (Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}) := by
  have hw : (fun p => z (joinInl ι (fun _ : Unit => Fin (r + 1)) p)) ∈ mcPts (mCoordIdeal y) := by
    refine ⟨fun k => hz.1 (Sum.inl k), fun f hf => ?_⟩
    have h1 := hz.2 _ (rename_inl_mem y (fun p : (Σ _ : Unit, Fin (r + 1)) => x' p.2) hf)
    change evC _ _ = 0 at h1
    rw [evC_rename_inl] at h1
    exact h1
  rw [evC_rename_inl] at hb
  have h2 := hβ _ hw hb
  rw [eval_map_int] at h2
  refine ⟨hz.1, fun f hf => ?_⟩
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.1 hf
  have h3 : evC z (rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)) = 0 := by
    rw [evC_rename_inl, evC, eval_map_int, aeval_segForm]
    exact h2
  change eval z (map (Int.castRingHom ℂ) _) = 0
  rw [map_mul, map_mul]
  change _ * evC z _ = 0
  rw [h3, mul_zero]
end GlobalTheory.CompanionTheory.Ar.SegreChart
