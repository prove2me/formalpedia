-- Prove2me | solution 1 for GlobalTheory.SelfCube.quad_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:39:16.027095+00:00
-- url     : https://prove2.me/submissions/31beae41-a342-4fb3-8666-00a2c4b6fee8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeTrivialisationOnUniformisingSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_AppellHumbertDataOfIsoCube
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
namespace GlobalTheory.SelfCube
private theorem exists_bound_of_continuous_lattice_periodic {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    [IsZLattice ℝ Λ] (h : (Fin g → ℂ) → ℝ) (hc : Continuous h)
    (hp : ∀ z, ∀ l ∈ Λ, h (z + l) = h z) : ∃ M, ∀ z, h z ≤ M := by
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Module.Free.ChooseBasisIndex ℤ Λ) ℝ (Fin g → ℂ),
      Submodule.span ℤ (Set.range b) = Λ :=
    ⟨_, (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis_span ℝ⟩
  have hK : IsCompact (closure (ZSpan.fundamentalDomain b)) :=
    (ZSpan.fundamentalDomain_isBounded b).isCompact_closure
  obtain ⟨M, hM⟩ := (hK.image hc).bddAbove
  refine ⟨M, fun z => ?_⟩
  have hfl : (ZSpan.floor b z : Fin g → ℂ) ∈ Λ := by
    exact Eq.mp (congrArg (fun S : Submodule ℤ (Fin g → ℂ) => (ZSpan.floor b z : Fin g → ℂ) ∈ S) hb)
      (ZSpan.floor b z).2
  have hz : z = ZSpan.fract b z + (ZSpan.floor b z : Fin g → ℂ) := by
    rw [ZSpan.fract_apply]; abel
  rw [hz, hp _ _ hfl]
  exact hM ⟨_, subset_closure (ZSpan.fract_mem_fundamentalDomain b z), rfl⟩
section Herm
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)
end Herm
open GlobalTheory.CubeValues
end GlobalTheory.SelfCube
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
noncomputable section
open GlobalTheory GlobalTheory.SelfCube
namespace GlobalTheory.SelfCube
theorem _root_.solution {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (ψ : (Fin g → ℂ) → ℂ) (hψ : Differentiable ℂ ψ) (h0 : ψ 0 ≠ 0)
    (q : (Fin g → ℂ) → ℝ) (hq : Continuous q) (hs : ∀ (t : ℂ) w, q (t • w) = ‖t‖ ^ 2 * q w)
    (hper : ∀ z, ∀ l ∈ Λ, ‖ψ (z + l)‖ * Real.exp (-q (z + l)) = ‖ψ z‖ * Real.exp (-q z)) (w) :
    0 ≤ q w := by
  by_contra hneg'
  have hneg := not_le.1 hneg'
  obtain ⟨M, hM⟩ := exists_bound_of_continuous_lattice_periodic Λ (fun z => ‖ψ z‖ * Real.exp (-q z))
    (hψ.continuous.norm.mul (Real.continuous_exp.comp hq.neg)) (fun z l hl => hper z l hl)
  have hM0 : 0 ≤ M := le_trans (by positivity) (hM 0)
  have hbd : ∀ t : ℂ, ‖ψ (t • w)‖ ≤ M * Real.exp (‖t‖ ^ 2 * q w) := by
    intro t
    have h1 := hM (t • w)
    simp only [hs] at h1
    have h2 : ‖ψ (t • w)‖ =
        ‖ψ (t • w)‖ * Real.exp (-(‖t‖ ^ 2 * q w)) * Real.exp (‖t‖ ^ 2 * q w) := by
      rw [_root_.mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, _root_.mul_one]
    rw [h2]
    exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
  have hdiff : Differentiable ℂ (fun t : ℂ => ψ (t • w)) :=
    hψ.comp (differentiable_id.smul_const w)
  have hb : Bornology.IsBounded (Set.range fun t : ℂ => ψ (t • w)) := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨M, ?_⟩
    rintro _ ⟨t, rfl⟩
    refine (hbd t).trans ?_
    have he : Real.exp (‖t‖ ^ 2 * q w) ≤ 1 :=
      Real.exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg.le)
    exact mul_le_of_le_one_right hM0 he
  have hc : ∀ t : ℂ, ψ (t • w) = ψ 0 := fun t => by
    have := hdiff.apply_eq_apply_of_bounded hb t 0
    simpa using this
  have hlim : Filter.Tendsto (fun r : ℝ => M * Real.exp (‖(r : ℂ)‖ ^ 2 * q w)) Filter.atTop
      (𝓝 (M * 0)) := by
    refine Filter.Tendsto.const_mul M (Real.tendsto_exp_atBot.comp ?_)
    have h1 : Filter.Tendsto (fun r : ℝ => r ^ 2 * (-q w)) Filter.atTop Filter.atTop :=
      (tendsto_pow_atTop two_ne_zero).atTop_mul_const (neg_pos.2 hneg)
    refine (Filter.tendsto_neg_atTop_atBot.comp h1).congr (fun r => ?_)
    simp only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hle : ‖ψ 0‖ ≤ M * 0 :=
    ge_of_tendsto' hlim (fun r => by rw [← hc (r : ℂ)]; exact hbd _)
  rw [mul_zero] at hle
  exact h0 (norm_le_zero_iff.1 hle)
end GlobalTheory.SelfCube
