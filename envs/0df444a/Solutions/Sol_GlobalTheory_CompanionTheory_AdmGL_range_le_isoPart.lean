-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.AdmGL.range_le_isoPart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:17:21.420293+00:00
-- url     : https://prove2.me/submissions/bc2cae1c-598d-4196-bb34-fe86cbb14ced

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDimensionalIsoPartOfSimple

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.AdmGL
variable {K : Type} [Group K] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace GlobalTheory.CompanionTheory.AdmGL
theorem _root_.solution (π : K →* (H →L[ℂ] H)) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ K W) {T : W →ₗ[ℂ] H} (hT : ∀ k w, T (ρ k w) = π k (T w)) :
    LinearMap.range T ≤ isoPart π ρ := by
  unfold isoPart
  exact le_iSup₂_of_le (f := fun (T : W →ₗ[ℂ] H) (_ : ∀ k w, T (ρ k w) = π k (T w)) => LinearMap.range T)
    T hT le_rfl
end GlobalTheory.CompanionTheory.AdmGL
