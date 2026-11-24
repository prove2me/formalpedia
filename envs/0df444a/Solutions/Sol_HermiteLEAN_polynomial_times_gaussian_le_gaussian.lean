-- Prove2me | solution 1 for HermiteLEAN.polynomial_times_gaussian_le_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T02:01:54.840418+00:00
-- url     : https://prove2.me/submissions/b35b24b5-bf73-4260-9ac9-4dd560d855eb

module
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_Definitions
public import Definitions.Def_LeanPool_PhaseRetrieval_DimdPoly_Internal_Hermite_MissingMathlib

set_option autoImplicit true
@[expose] public section
public section
open Complex MeasureTheory Real Finset Filter
open scoped BigOperators ComplexConjugate Topology
noncomputable section
open HermiteLEAN
namespace HermiteLEAN
theorem _root_.solution
    {a : ℝ}
    (ha : 0 < a)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x : ℝ, 0 ≤ x →
        (1 + x ^ k) * Real.exp (-a * x ^ 2)
          ≤ C * Real.exp (-(a / 2) * x ^ 2) := by
  let g : ℝ → ℝ := fun x => (1 + x ^ k) * Real.exp (-(a / 2) * x ^ 2)
  have hsq : Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hexp : Tendsto (fun x : ℝ => Real.exp (-(a / 2) * x ^ 2)) Filter.atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (hsq.const_mul_atTop_of_neg (by linarith only [ha]))
  have hpoly : Tendsto (fun x : ℝ => x ^ k * Real.exp (-(a / 2) * x ^ 2)) Filter.atTop (𝓝 0) := by
    refine Tendsto.congr' ?_
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero ((k : ℝ) / 2) (a / 2) (by positivity)).comp
        hsq)
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    change ((x ^ 2 : ℝ) ^ ((k : ℝ) / 2)) * Real.exp (-(a / 2) * (x ^ 2)) =
      x ^ k * Real.exp (-(a / 2) * x ^ 2)
    rw [show x ^ k = x ^ ((k : ℝ)) by rw [Real.rpow_natCast]]
    congr 1
    calc
      ((x ^ 2 : ℝ) ^ ((k : ℝ) / 2)) = x ^ ((((2 : ℕ) : ℝ)) * ((k : ℝ) / 2)) := by
        rw [← Real.rpow_natCast_mul hx 2 ((k : ℝ) / 2)]
      _ = x ^ ((k : ℝ)) := by
        congr 2
        ring
  have hgtendsto : Tendsto g Filter.atTop (𝓝 0) := by simpa [g, add_mul] using hexp.add hpoly
  have hsmall : ∀ᶠ x : ℝ in Filter.atTop, g x < 1 := (tendsto_order.1 hgtendsto).2 1 zero_lt_one
  rcases Filter.eventually_atTop.1 hsmall with ⟨R, hR⟩
  have hcont : Continuous g := by
    dsimp [g]
    exact (continuous_const.add <| continuous_id.pow k).mul <|
      Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2))
  have hcompactIcc : IsCompact (Set.Icc 0 R) := isCompact_Icc
  obtain ⟨C0, hC0⟩ := hcompactIcc.exists_bound_of_continuousOn (hcont.continuousOn)
  let C : ℝ := |C0| + 1
  refine ⟨C, by positivity, ?_⟩
  intro x hx
  have hbound_g : g x ≤ C := by
    by_cases hxr : x ≤ R
    · have hcompact : g x ≤ C0 := by
        simpa [Real.norm_eq_abs, g, abs_of_nonneg (by positivity : 0 ≤ 1 + x ^ k)] using
          hC0 x ⟨hx, hxr⟩
      simp only [C]
      linarith only [hcompact, le_abs_self C0]
    · simp only [C]
      linarith only [hR, hxr, hR x (le_of_not_ge hxr), abs_nonneg C0]
  have hsplit :
      Real.exp (-a * x ^ 2) =
        Real.exp (-(a / 2) * x ^ 2) * Real.exp (-(a / 2) * x ^ 2) := by
    rw [← Real.exp_add]
    ring_nf
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hbound_g (Real.exp_pos _).le
end HermiteLEAN
