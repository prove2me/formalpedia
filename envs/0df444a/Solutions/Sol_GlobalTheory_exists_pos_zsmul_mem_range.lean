-- Prove2me | solution 1 for GlobalTheory.exists_pos_zsmul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T01:03:01.497704+00:00
-- url     : https://prove2.me/submissions/ee8219e9-2f70-4be6-b261-7ac0b168b7e5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsPosZsmulMemRange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
variable {X : Type} [AddCommGroup X] {Bf : X →+ X →+ ℤ} {Q : X → ℤ}
namespace GlobalTheory
theorem _root_.solution {n : ℕ} (b : Module.Basis (Fin n) ℤ X) (φ : X →+ X)
    (hφ : Function.Injective φ) (x : X) : ∃ N : ℤ, 0 < N ∧ ∃ y, φ y = N • x := by
  have : Module.Free ℤ X := Module.Free.of_basis b
  have : Module.Finite ℤ X := Module.Finite.of_basis b
  set f : X →ₗ[ℤ] X := φ.toIntLinearMap with hf
  set M := LinearMap.toMatrix b b f
  have hinj : Function.Injective f := by
    simpa [hf, AddMonoidHom.coe_toIntLinearMap] using hφ
  have hdet : M.det ≠ 0 := by
    intro h
    rw [LinearMap.det_toMatrix, LinearMap.det_eq_zero_iff_ker_ne_bot] at h
    exact h (LinearMap.ker_eq_bot.mpr hinj)
  have e : Matrix.toLin b b M = f := Matrix.toLin_toMatrix b b f
  have key : f.comp (Matrix.toLin b b M.adjugate) = M.det • LinearMap.id := by
    calc f.comp (Matrix.toLin b b M.adjugate)
        = (Matrix.toLin b b M).comp (Matrix.toLin b b M.adjugate) := by rw [e]
      _ = Matrix.toLin b b (M * M.adjugate) := (Matrix.toLin_mul b b b M M.adjugate).symm
      _ = M.det • LinearMap.id := by rw [Matrix.mul_adjugate, map_smul, Matrix.toLin_one]
  refine ⟨M.det * M.det, mul_self_pos.mpr hdet, M.det • Matrix.toLin b b M.adjugate x, ?_⟩
  have hx : f (Matrix.toLin b b M.adjugate x) = M.det • x := by
    have := congrArg (fun g => g x) key
    simpa using this
  have : φ (M.det • Matrix.toLin b b M.adjugate x) = M.det • f (Matrix.toLin b b M.adjugate x) := by
    rw [map_zsmul]; rfl
  rw [this, hx, smul_smul]
end GlobalTheory
