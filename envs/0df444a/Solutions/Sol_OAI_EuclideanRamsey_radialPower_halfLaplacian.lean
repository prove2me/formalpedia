-- Prove2me | solution 1 for OAI.EuclideanRamsey.radialPower_halfLaplacian
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:51:59.271575+00:00
-- url     : https://prove2.me/submissions/542fb942-5902-443a-870a-a13b1142c1fb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/SmoothingKernel.lean:L153-L178
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.radialPower_halfLaplacian. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel

-- ---- from OAI.Combinatorics.EuclideanRamsey.SmoothingKernel ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
namespace OAI

universe uDomain

noncomputable section

open scoped TensorProduct RealInnerProductSpace

open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
namespace EuclideanRamsey

section Radial
variable {E : Type uDomain} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma radialPower_hasFDerivAt {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    HasFDerivAt (radialPower a p)
      ((2*p*(a+‖x‖^2)^(p-1)) • innerSL ℝ x) x := by
  have h := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_add a).rpow_const
    (p := p) (Or.inl (ne_of_gt (add_pos_of_pos_of_nonneg ha (sq_nonneg _))))
  change HasFDerivAt (radialPower a p) _ x at h
  apply h.congr_fderiv
  ext v
  simp only [_root_.smul_apply, smul_eq_mul]
  ring

lemma radialPower_hessian {a : ℝ} (ha : 0 < a) (p : ℝ) (x v w : E) :
    iteratedFDeriv ℝ 2 (radialPower a p) x ![v,w] =
      4*p*(p-1)*(a+‖x‖^2)^(p-2) * inner ℝ x v * inner ℝ x w +
      2*p*(a+‖x‖^2)^(p-1) * inner ℝ v w := by
  have hg : (fun y => fderiv ℝ (radialPower a p) y) =
    (fun y => (2*p*radialPower a (p-1) y) • innerSL ℝ y) :=
    funext fun (y : E) => by simpa only [radialPower] using (radialPower_hasFDerivAt ha p y).fderiv
  have hs := (radialPower_hasFDerivAt ha (p-1) x).const_smul (2*p)
  have hd := hs.smul (innerSL ℝ (E := E)).hasFDerivAt
  change HasFDerivAt (fun y => (2*p*radialPower a (p-1) y) • innerSL ℝ y) _ x at hd
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  change ((fderiv ℝ (fun y => fderiv ℝ (radialPower a p) y) x) v) w = _
  rw [hg, hd.fderiv]
  simp only [_root_.add_apply, ContinuousLinearMap.smulRight_apply,
    _root_.smul_apply,
    innerSL_apply_apply, Pi.smul_apply, smul_eq_mul, radialPower, show p-1-1 = p-2 by ring]
  change (2*p*(a+‖x‖^2)^(p-1))*inner ℝ v w +
    (2*p)*(2*(p-1)*(a+‖x‖^2)^(p-2)*inner ℝ x v)*inner ℝ x w = _
  ring

variable [FiniteDimensional ℝ E]

lemma radialPower_halfLaplacian {a : ℝ} (ha : 0 < a) (p : ℝ) (x : E) :
    halfLaplacian (radialPower a p) x =
      p * (a+‖x‖^2)^(p-2) *
        ((Module.finrank ℝ E : ℝ)*a + (Module.finrank ℝ E + 2*p-2)*‖x‖^2) := by
  classical
  let e := stdOrthonormalBasis ℝ E
  have hsum : (∑ i, inner ℝ x (e i) * inner ℝ x (e i)) = ‖x‖^2 := by
    simpa only [real_inner_comm (e _), real_inner_self_eq_norm_sq] using
      e.sum_inner_mul_inner x x
  unfold halfLaplacian
  simp_rw [radialPower_hessian ha]
  simp only [(stdOrthonormalBasis ℝ E).inner_eq_ite, ite_eq_left, mul_one, Finset.sum_add_distrib]
  have hsum' : (∑ i, 4*p*(p-1)*(a+‖x‖^2)^(p-2)*inner ℝ x (e i)*inner ℝ x (e i)) =
      4*p*(p-1)*(a+‖x‖^2)^(p-2)*‖x‖^2 := by
    rw [← hsum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change (1/2 : ℝ) * ((∑ i, 4*p*(p-1)*(a+‖x‖^2)^(p-2)*inner ℝ x (e i)*inner ℝ x (e i)) +
    ∑ _ : Fin (Module.finrank ℝ E), 2*p*(a+‖x‖^2)^(p-1)) = _
  rw [hsum']
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hpow : (a+‖x‖^2)^(p-1) = (a+‖x‖^2)^(p-2)*(a+‖x‖^2) := by
    rw [show p-1 = (p-2)+1 by ring, Real.rpow_add (by positivity), Real.rpow_one]
  rw [hpow]
  ring

section Integration
variable [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

end Integration

end Radial

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial


theorem solution.{uDomain} : type_of% @_root_.OAI.EuclideanRamsey.radialPower_halfLaplacian.{uDomain} := @_root_.OAI.EuclideanRamsey.radialPower_halfLaplacian.{uDomain}
