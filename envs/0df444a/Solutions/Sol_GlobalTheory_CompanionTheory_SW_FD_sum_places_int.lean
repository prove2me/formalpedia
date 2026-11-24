-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FD.sum_places_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:20:15.296861+00:00
-- url     : https://prove2.me/submissions/ea63f62f-2378-4142-989e-a379ed5496ee

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.FD
theorem _root_.solution (hF : IsTotallyReal F) (ρ : InfinitePlace F → (F →+* ℝ))
    (hρ : ∀ w x, ((ρ w x : ℝ) : ℂ) = w.embedding x) (a : 𝓞 F) :
    ∃ z : ℤ, ∑ w, ρ w (a : F) = (z : ℝ) := by
  obtain ⟨z, hz⟩ : ∃ z : ℤ, algebraMap ℤ ℚ z = Algebra.trace ℚ F (a : F) :=
    IsIntegrallyClosed.isIntegral_iff.1
      (Algebra.isIntegral_trace (R := ℤ) (L := ℚ) (F := F) (RingOfIntegers.isIntegral_coe a))
  refine ⟨z, ?_⟩
  have h := trace_eq_sum_embeddings (K := ℚ) (L := F) ℂ (x := (a : F))
  rw [← (placeEquiv hF).sum_comp, ← hz] at h
  have h2 : ((z : ℝ) : ℂ) = ((∑ w, ρ w (a : F) : ℝ) : ℂ) := by
    push_cast
    simp only [hρ]
    simpa [placeEquiv] using h
  exact_mod_cast h2.symm
end GlobalTheory.CompanionTheory.SW.FD
