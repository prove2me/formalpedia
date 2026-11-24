-- Prove2me | solution 1 for GlobalTheory.HolHom.eq_of_forall_fderiv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:28:26.682396+00:00
-- url     : https://prove2.me/submissions/84cc9caf-7fb8-4c6a-866e-b6166d403397

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_isDerivAt0_iff
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_unique
import Theorems.Thm_GlobalTheory_HolHom_HolAt_exists_isDerivAt
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_over

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {S : Scheme.{0}} {G : Over S} {g : ℕ}
namespace GlobalTheory.HolHom
theorem _root_.solution {y : Sp ℂ ⟶ S} {e' : (Fin g → ℂ) → (Over.mk y ⟶ G)}
    (hol' : HolAt (fun z => (e' z).left) 0)
    (hdiff : ∀ v : epsPt y ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e' 0).left →
      ∃! w, IsDerivAt0 (fun z => (e' z).left) w v.left) {w w' : Fin g → ℂ}
    (h : ∀ U : G.left.Opens, ⊤ ≤ (e' 0).left ⁻¹ᵁ U → ∀ f : Γ(G.left, U),
      fderiv ℂ (fun z => valAt' (e' z).left U f) 0 w = fderiv ℂ (fun z => valAt' (e' z).left U f) 0 w') : w = w' := by
  obtain ⟨u, hu⟩ := hol'.exists_isDerivAt w
  exact (hdiff (Over.homMk u hu.over) hu.1).unique ((isDerivAt0_iff _ _ _).2 hu)
    ((isDerivAt0_iff _ _ _).2 ⟨hu.1, fun U hU f => (hu.2 U hU f).trans (h U hU f)⟩)
end GlobalTheory.HolHom
