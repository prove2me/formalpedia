-- Prove2me | solution 1 for GlobalTheory.AppellHumbert.exists_real_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:59:08.954615+00:00
-- url     : https://prove2.me/submissions/b43d3dca-c0cf-4906-bdcf-b700bf552971

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertNormalFormOfLinearExponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory
open GlobalTheory.AppellHumbert
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace GlobalTheory.AppellHumbert
namespace _root_.GlobalTheory.AppellHumbert
theorem _root_.solution {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ]
    (hΛ : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) {W : Type*} [AddCommGroup W] [Module ℝ W]
    (f : Λ →+ W) : ∃ F : (Fin g → ℂ) →ₗ[ℝ] W, ∀ l : Λ, F l = f l := by
  haveI : IsZLattice ℝ Λ := ⟨hΛ⟩
  let b := Module.Free.chooseBasis ℤ Λ
  let bR := Module.Basis.ofZLatticeBasis ℝ Λ b
  refine ⟨bR.constr ℝ (fun i => f (b i)), fun l => ?_⟩
  have key : ((bR.constr ℝ (fun i => f (b i))).restrictScalars ℤ ∘ₗ Λ.subtype) =
      f.toIntLinearMap := by
    refine b.ext fun i => ?_
    show bR.constr ℝ (fun i => f (b i)) (b i : Fin g → ℂ) = f (b i)
    rw [← Module.Basis.ofZLatticeBasis_apply ℝ Λ b i, Module.Basis.constr_basis]
  exact LinearMap.congr_fun key l
end _root_.GlobalTheory.AppellHumbert
end GlobalTheory.AppellHumbert
