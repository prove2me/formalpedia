-- Prove2me | solution 1 for GlobalTheory.Frames.Model.det_rel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:31:23.420057+00:00
-- url     : https://prove2.me/submissions/1d9e2aea-fa24-40a3-84dc-c6712e155678

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_UnivFrame
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_FrameRingGlRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Frames GlobalTheory.Frames.Model
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {K : Type} [Field K] {J : Type} (m : J → ℕ) (R : Type) [CommRing R] [Algebra K R]
namespace GlobalTheory.Frames.Model
theorem _root_.solution (τ : J) : (glX m R τ).det *
    Ideal.Quotient.mk (rel m R) (MvPolynomial.X (Sum.inr (Sum.inl τ))) = 1 := by
  unfold glX
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, ← map_mul, ← map_one (Ideal.Quotient.mk (rel m R)),
    Ideal.Quotient.eq]
  unfold rel
  exact Ideal.subset_span (Set.mem_union_left _ ⟨τ, rfl⟩)
end GlobalTheory.Frames.Model
