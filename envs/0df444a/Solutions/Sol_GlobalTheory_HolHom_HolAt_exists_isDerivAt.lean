-- Prove2me | solution 1 for GlobalTheory.HolHom.HolAt.exists_isDerivAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:12.262333+00:00
-- url     : https://prove2.me/submissions/a8a4cc9d-f39e-48c6-ba06-396736aa2dd0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_valR_res
import Theorems.Thm_GlobalTheory_HolHom_valR_spMap
import Theorems.Thm_GlobalTheory_HolHom_point_ext
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_iff
import Theorems.Thm_GlobalTheory_HolHom_exists_affine
import Theorems.Thm_GlobalTheory_HolHom_le_preimage_dual_iff
import Theorems.Thm_GlobalTheory_HolHom_jetHom_res
import Theorems.Thm_GlobalTheory_AffinePointValues_appLE_specMap_fromSpec


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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {X : Scheme.{0}}
namespace GlobalTheory.HolHom
namespace HolAt
theorem _root_.solution {c : V → (Sp ℂ ⟶ X)} {z : V} (h : HolAt c z) (w : V) : ∃ v, IsDerivAt c z w v := by
  obtain ⟨P, hP, hz, -⟩ := exists_affine (c z) (U := ⊤) le_top
  let φ : Γ(X, P) ⟶ CommRingCat.of (DualNumber ℂ) := CommRingCat.ofHom (jetHom h w P hz)
  let v : Sp (DualNumber ℂ) ⟶ X := Spec.map φ ≫ hP.fromSpec
  have hvP : ⊤ ≤ v ⁻¹ᵁ P := fun p _ => hP.range_fromSpec.le ⟨_, rfl⟩
  have hval : ∀ f, valR v P f = jetHom h w P hz f := fun f => by
    rw [valR_eq _ _ hvP]
    exact congrArg (fun ψ => ψ.hom f) (AffinePointValues.appLE_specMap_fromSpec hP φ hvP)
  have h1 : spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = c z := by
    refine point_ext hP (fun p _ => hvP (x := spMap _ p) trivial) hz fun f => ?_
    rw [valR_spMap _ _ _ hvP, hval]
    simp [jetHom, valAt'_eq_valR]
  refine ⟨v, h1, fun U hU f => ?_⟩
  obtain ⟨s, hsU, hs₀⟩ := hP.exists_basicOpen_le (V := U) ⟨_, (le_preimage_iff _ U).1 hU⟩ ((le_preimage_iff _ P).1 hz)
  have hs : ⊤ ≤ c z ⁻¹ᵁ X.basicOpen s := (le_preimage_iff _ _).2 hs₀
  have hvs := (le_preimage_dual_iff h1 _).2 hs
  have := hP.isLocalization_basicOpen s
  have key : evalHom v _ hvs = jetHom h w _ hs := by
    refine IsLocalization.ringHom_ext (Submonoid.powers s) (RingHom.ext fun g => ?_)
    change evalHom v _ hvs ((X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom g) =
      jetHom h w _ hs ((X.presheaf.map (homOfLE (X.basicOpen_le s)).op).hom g)
    rw [jetHom_res h w _ hz, ← valR_eq, valR_res _ _ _ hvs, hval]
  rw [← valR_res v hsU f hvs, valR_eq _ _ hvs, key, jetHom_res h w _ hU]
  simp [jetHom]
end HolAt
end GlobalTheory.HolHom
