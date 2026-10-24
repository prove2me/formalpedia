-- Prove2me | solution 1 for OAI.PinchedHartogs.BaseConstruction.analytic_jet_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T16:04:03.549498+00:00
-- url     : https://prove2.me/submissions/6451f399-f7ae-4ba0-a051-99473c019691

import Mathlib
import Definitions.Def_OAIQWPH000

section
-- module Solutions.OAIQW_PinchedHartogs.BaseCauchyJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uKahler8342_1 uKahler8342_2 uKahler8392_1 uKahler8392_2

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open Set Filter Topology MeasureTheory
open scoped ContDiff ComplexOrder
noncomputable section

open Set Filter Topology
namespace PinchedHartogs.BaseConstruction

lemma cauchyJetConstant_pos (n : ℕ) : 0 < cauchyJetConstant n := by
  induction n with
  | zero => norm_num [cauchyJetConstant]
  | succ n ih => simp only [cauchyJetConstant]; positivity

lemma analytic_jet_bound_oai {E : Type uKahler8342_1} {F : Type uKahler8342_2} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {c : E} {R r A : ℝ} (hRr : r < R) (hr : 0 ≤ r) (hA : 0 ≤ A)
    (hf : AnalyticOnNhd ℂ f (Metric.ball c R))
    (hb : ∀ x ∈ Metric.ball c R, ‖f x‖ ≤ A) (n : ℕ) :
    ∀ x ∈ Metric.ball c r, ‖iteratedFDeriv ℂ n f x‖ ≤ cauchyJetConstant n*A/(R-r)^n := by
  induction n generalizing r with
  | zero =>
    intro x hx
    simpa only [norm_iteratedFDeriv_zero,cauchyJetConstant,pow_zero,div_one,one_mul] using
      hb x (Metric.ball_subset_ball hRr.le hx)
  | succ n ih =>
    intro x hx
    let s : ℝ := (R+r)/2
    let ρ : ℝ := (R-r)/2
    have hρ : 0 < ρ := by dsimp [ρ]; linarith
    have hrs : r < s := by dsimp [s]; linarith
    have hsR : s < R := by dsimp [s]; linarith
    have hs0 : 0 ≤ s := hr.trans hrs.le
    let B : ℝ := cauchyJetConstant n*A/(R-s)^n
    have hB : 0 ≤ B := div_nonneg (mul_nonneg (cauchyJetConstant_pos n).le hA) (pow_nonneg (by linarith) _)
    have hsub : Metric.ball x ρ ⊆ Metric.ball c s := by
      intro z hz
      have hdist := dist_triangle z x c
      have hz' : dist z x < ρ := hz
      have hx' : dist x c < r := hx
      change dist z c < s
      dsimp [ρ,s] at *
      linarith
    have hg : AnalyticOnNhd ℂ (iteratedFDeriv ℂ n f) (Metric.ball c R) := hf.iteratedFDeriv n
    have hb' : ∀ y ∈ Metric.ball c s, ‖iteratedFDeriv ℂ n f y‖ ≤ B := ih hsR hs0
    have hx' : x ∈ Metric.ball c s := Metric.ball_subset_ball hrs.le hx
    have hmaps : MapsTo (iteratedFDeriv ℂ n f) (Metric.ball x ρ)
        (Metric.closedBall (iteratedFDeriv ℂ n f x) (2*B)) := by
      intro z hz
      change dist (iteratedFDeriv ℂ n f z) (iteratedFDeriv ℂ n f x) ≤ 2*B
      rw [dist_eq_norm]
      exact (norm_sub_le _ _).trans (by linarith [hb' z (hsub hz),hb' x hx'])
    have hder := Complex.norm_fderiv_le_div_of_mapsTo_ball
      ((hg.mono (hsub.trans (Metric.ball_subset_ball hsR.le))).differentiableOn) hmaps hρ
    rw [norm_fderiv_iteratedFDeriv] at hder
    apply hder.trans_eq
    dsimp [B,ρ,s]
    rw [cauchyJetConstant,pow_succ]
    have hd : R-r ≠ 0 := by linarith
    have he : R-(R+r)/2=(R-r)/2 := by ring
    rw [he,div_pow]
    field_simp
    ring

end PinchedHartogs.BaseConstruction

end

end OAI
end

theorem solution.{uKahler8342_1, uKahler8342_2} : type_of% @OAI.PinchedHartogs.BaseConstruction.analytic_jet_bound_oai.{uKahler8342_1, uKahler8342_2} := @OAI.PinchedHartogs.BaseConstruction.analytic_jet_bound_oai.{uKahler8342_1, uKahler8342_2}
