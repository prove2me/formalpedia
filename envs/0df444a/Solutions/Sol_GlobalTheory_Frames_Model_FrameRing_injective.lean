-- Prove2me | solution 1 for GlobalTheory.Frames.Model.FrameRing.injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:15.392129+00:00
-- url     : https://prove2.me/submissions/e60816b4-cfad-48a2-a875-162e5d51da05

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
variable {m R}
namespace GlobalTheory.Frames.Model
namespace FrameRing
theorem _root_.solution {A : Type} [CommRing A] [Algebra K A] {π : R →ₐ[K] A}
    {X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A} {s : Aˣ} (h : FrameRing m π X s) : Function.Injective π := by
  intro r₁ r₂ hr
  obtain ⟨k, ⟨hk, -, -⟩, -⟩ := h.2 R (AlgHom.id K R) (fun _ => 1) 1 (fun _ => by simp)
  have e₁ := AlgHom.congr_fun hk r₁
  have e₂ := AlgHom.congr_fun hk r₂
  rw [AlgHom.comp_apply, AlgHom.id_apply] at e₁ e₂
  rw [← e₁, ← e₂, hr]
end FrameRing
end GlobalTheory.Frames.Model
