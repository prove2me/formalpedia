-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.KaehlerSpread.spread
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:03:16.70101+00:00
-- url     : https://prove2.me/submissions/8dd213fd-cd9e-4d2b-9001-6aeeab6de267

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_KaehlerBasisSpreadsToNeighbourhood
import Theorems.Thm_GlobalTheory_CompanionTheory_KaehlerSpread_map_diffMap_eq
import Theorems.Thm_GlobalTheory_CompanionTheory_KaehlerSpread_bijective_linearCombination_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KaehlerSpread
open KaehlerDifferential
namespace GlobalTheory.CompanionTheory.KaehlerSpread
theorem _root_.solution : ∀ (K A : Type) [Field K] [CommRing A] [Algebra K A] [Algebra.FinitePresentation K A] (P : Ideal A) [P.IsPrime] {n : ℕ} (x : Fin n → A), (LinearIndependent (Localization.AtPrime P) (fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) ∧ Submodule.span (Localization.AtPrime P) (Set.range fun i => KaehlerDifferential.D K (Localization.AtPrime P) (algebraMap A _ (x i))) = ⊤) → ∃ s ∉ P, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra K B] [IsScalarTower K A B] [IsLocalization.Away s B], LinearIndependent B (fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) ∧ Submodule.span B (Set.range fun i => KaehlerDifferential.D K B (algebraMap A B (x i))) = ⊤ := by
  intro K A _ _ _ _ P _ n x hP
  classical
  let l₁ : (Fin n →₀ A) →ₗ[A] (Fin n →₀ Localization.AtPrime P) :=
    Finsupp.mapRange.linearMap (Algebra.linearMap A (Localization.AtPrime P))
  let l₂ : Ω[A⁄K] →ₗ[A] Ω[Localization.AtPrime P⁄K] :=
    KaehlerDifferential.map K K A (Localization.AtPrime P)
  have hP' : Function.Bijective (IsLocalizedModule.map P.primeCompl l₁ l₂ (diffMap K x)) := by
    have h := (bijective_linearCombination_iff _).mpr hP
    rw [← map_diffMap_eq K x P.primeCompl (Localization.AtPrime P)] at h
    exact h
  obtain ⟨s, hs, hbij⟩ :=
    Module.FinitePresentation.exists_notMem_bijective (diffMap K x) P l₁ l₂ hP'
  refine ⟨s, hs, ?_⟩
  intro B _ _ _ _ _
  rw [← bijective_linearCombination_iff, ← map_diffMap_eq K x (Submonoid.powers s) B]
  exact (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
    (Finsupp.mapRange.linearMap (Algebra.linearMap A B)) (KaehlerDifferential.map K K A B)).mpr hbij
end GlobalTheory.CompanionTheory.KaehlerSpread
