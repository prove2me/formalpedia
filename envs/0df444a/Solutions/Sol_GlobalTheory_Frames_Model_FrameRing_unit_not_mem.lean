-- Prove2me | solution 1 for GlobalTheory.Frames.Model.FrameRing.unit_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:48:43.887085+00:00
-- url     : https://prove2.me/submissions/7d87f421-29b6-48d4-9021-381b75bedcbb

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
theorem _root_.solution [Nontrivial R] {A : Type} [CommRing A] [Algebra K A] {π : R →ₐ[K] A}
    {X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A} {s : Aˣ} (h : FrameRing m π X s) (r : R) : π r ≠ s := by

  intro hr
  have hε : (1 + DualNumber.eps : DualNumber R) * (1 - DualNumber.eps) = 1 := by
    rw [mul_sub, _root_.mul_one, add_mul, _root_.one_mul, DualNumber.eps_mul_eps, add_zero, add_sub_cancel_right]
  obtain ⟨k, ⟨hk1, -, hk3⟩, -⟩ := h.2 (DualNumber R) (TrivSqZeroExt.inlAlgHom K R R) (fun _ => 1)
    (Units.mkOfMulEqOne _ _ hε) (fun _ => by simp)
  have e := congrArg k hr
  rw [hk3] at e
  have e₁ := AlgHom.congr_fun hk1 r
  rw [AlgHom.comp_apply] at e₁
  rw [e₁] at e
  have e₂ := congrArg TrivSqZeroExt.snd e
  simp [Units.val_mkOfMulEqOne, DualNumber.snd_eps] at e₂
end FrameRing
end GlobalTheory.Frames.Model
