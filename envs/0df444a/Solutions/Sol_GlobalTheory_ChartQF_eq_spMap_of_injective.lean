-- Prove2me | solution 1 for GlobalTheory.ChartQF.eq_spMap_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:30:51.726447+00:00
-- url     : https://prove2.me/submissions/8b4f5a73-8a49-4b0c-9211-733b92bc28c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAlgebraicOfMemClosure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ChartQF
namespace GlobalTheory.ChartQF
theorem _root_.solution {F R K : Type} [CommRing F] [CommRing R] [CommRing K] (u : R →+* K)
    (hu : Function.Injective u) (σ : Sp R ⟶ Sp F) (b : F →+* R) (h : spMap u ≫ σ = spMap u ≫ spMap b) :
    σ = spMap b := by
  obtain ⟨g, rfl⟩ := Spec.map_surjective σ
  have h' : g ≫ CommRingCat.ofHom u = CommRingCat.ofHom b ≫ CommRingCat.ofHom u := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_comp]
    exact h
  show Spec.map g = Spec.map (CommRingCat.ofHom b)
  congr 1
  ext x
  apply hu
  simpa using congrArg (fun φ => φ.hom x) h'
end GlobalTheory.ChartQF
