-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.ResKCoords.stalk_to_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:33:43.04175+00:00
-- url     : https://prove2.me/submissions/9039aab5-1d71-41f0-aa56-dda0c1eab0f1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_RegularSequenceGermsRegularLocal
import Theorems.Thm_GlobalTheory_CompanionTheory_ResKCoords_rsp_of_ringEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.ResKCoords
namespace GlobalTheory.CompanionTheory.ResKCoords
theorem _root_.solution : ∀ (Y : Scheme.{0}) (U : Y.affineOpens) (y : Y) (hy : y ∈ U.1),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (m : ℕ) (f : Fin m → Γ(Y, U.1)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) m (fun i => Y.presheaf.germ U.1 y hy (f i)) →
    IsRegularLocalRing (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) ∧
    FinalTheorems.Rsp (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal) m
      (fun i => algebraMap Γ(Y, U.1) _ (f i)) ∧
    ∀ s : Γ(Y, U.1), y ∈ Y.basicOpen s ↔ s ∉ (U.2.primeIdealOf ⟨y, hy⟩).asIdeal := by
  intro Y U y hy hreg m f hr
  letI := TopCat.Presheaf.algebra_section_stalk Y.presheaf (⟨y, hy⟩ : U.1)
  haveI hloc : IsLocalization.AtPrime (Y.presheaf.stalk y) (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    U.2.isLocalization_stalk ⟨y, hy⟩
  let e : Y.presheaf.stalk y ≃+* Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal :=
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).toRingEquiv
  have he : ∀ a : Γ(Y, U.1), e (Y.presheaf.germ U.1 y hy a) = algebraMap Γ(Y, U.1) _ a := fun a =>
    (IsLocalization.algEquiv (U.2.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (Y.presheaf.stalk y)
      (Localization.AtPrime (U.2.primeIdealOf ⟨y, hy⟩).asIdeal)).commutes a
  refine ⟨IsRegularLocalRing.of_ringEquiv e, ?_, fun s => ?_⟩
  · have h := rsp_of_ringEquiv e m _ hr
    simpa only [he] using h
  · rw [Scheme.mem_basicOpen Y s y hy]
    have h := IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (U.2.primeIdealOf ⟨y, hy⟩).asIdeal s
    exact h.trans Iff.rfl
end GlobalTheory.CompanionTheory.ResKCoords
