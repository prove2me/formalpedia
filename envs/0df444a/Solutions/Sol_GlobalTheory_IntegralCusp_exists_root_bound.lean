-- Prove2me | solution 1 for GlobalTheory.IntegralCusp.exists_root_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:12:51.573178+00:00
-- url     : https://prove2.me/submissions/395ce14d-ce60-422c-8fb1-65cd2562aae8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_CuspStatementPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_BddOfMemHolSub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
noncomputable section
namespace GlobalTheory
namespace IntegralCusp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in
private theorem norm_eval_le_of_isHomogeneous' {N d : ℕ} {p : MvPolynomial (Fin N) ℂ}
    (hp : p.IsHomogeneous d) (w : Fin N → ℂ) :
    ‖MvPolynomial.eval w p‖ ≤ (∑ s ∈ p.support, ‖p.coeff s‖) * ‖w‖ ^ d := by
  rw [MvPolynomial.eval_eq', Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s hs => ?_)
  rw [norm_mul, norm_prod]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have hdeg : ∑ j, s j = d := by
    have := hp (MvPolynomial.mem_support_iff.mp hs)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  calc ∏ j, ‖w j ^ s j‖ ≤ ∏ j, ‖w‖ ^ s j := by
        refine Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => ?_)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm w j) _
    _ = ‖w‖ ^ d := by rw [Finset.prod_pow_eq_pow_sum, hdeg]
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {H : Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
end IntegralCusp
end GlobalTheory
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
noncomputable section
open GlobalTheory
open GlobalTheory.IntegralCusp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
namespace GlobalTheory.IntegralCusp
namespace _root_.GlobalTheory.IntegralCusp
theorem _root_.solution (N k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) ℂ)
    (hc : ∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Fin N → ℂ) (g : ℂ),
      g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i = 0 →
        ‖g‖ ≤ C * ‖w‖ ^ k := by
  classical
  set A : ℕ → ℝ := fun i => ∑ s ∈ (cf i).support, ‖(cf i).coeff s‖ with hA
  have hA0 : ∀ i, 0 ≤ A i := fun i => Finset.sum_nonneg fun _ _ => norm_nonneg _
  set B : ℝ := 1 + ∑ i ∈ Finset.range m, A i with hBdef
  have hB1 : 1 ≤ B := le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hA0 i)
  have hB0 : 0 < B := by linarith
  refine ⟨B, hB0.le, fun w g hg => ?_⟩
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero]; positivity
  have hroot : g ^ m = -∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
    have h1 : g * (g ^ m + ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i) = 0 := by
      have hs : ∑ i ∈ Finset.range m, (g * MvPolynomial.eval w (cf i)) * g ^ i =
          g * ∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
      rw [mul_add, ← hs]
      exact hg
    exact eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h1).resolve_left hg0)
  set x := ‖g‖ with hx
  set t := ‖w‖ ^ k with ht
  have hx0 : 0 < x := norm_pos_iff.mpr hg0
  have ht0 : 0 ≤ t := by positivity
  by_contra hlt
  push_neg at hlt
  have htx : t ≤ x / B := by rw [le_div_iff₀ hB0]; linarith
  have hterm : ∀ i ∈ Finset.range m,
      ‖MvPolynomial.eval w (cf i) * g ^ i‖ ≤ A i * (x ^ m / B) := by
    intro i hi
    have him : i < m := Finset.mem_range.mp hi
    rw [norm_mul, norm_pow]
    have hci := norm_eval_le_of_isHomogeneous' (hc i him) w
    have hpow : ‖w‖ ^ ((m - i) * k) = t ^ (m - i) := by rw [ht, ← pow_mul, mul_comm]
    have hkey : t ^ (m - i) * x ^ i ≤ x ^ m / B := by
      have h1 : t ^ (m - i) ≤ (x / B) ^ (m - i) := pow_le_pow_left₀ ht0 htx _
      have h2 : B ≤ B ^ (m - i) := le_self_pow₀ hB1 (by omega)
      calc t ^ (m - i) * x ^ i ≤ (x / B) ^ (m - i) * x ^ i := by gcongr
        _ = x ^ m / B ^ (m - i) := by
          rw [div_pow, div_mul_eq_mul_div, ← pow_add, Nat.sub_add_cancel him.le]
        _ ≤ x ^ m / B := div_le_div_of_nonneg_left (by positivity) hB0 h2
    calc ‖MvPolynomial.eval w (cf i)‖ * x ^ i ≤ A i * t ^ (m - i) * x ^ i := by
          gcongr
          rw [← hpow]
          exact hci
      _ = A i * (t ^ (m - i) * x ^ i) := by ring
      _ ≤ A i * (x ^ m / B) := mul_le_mul_of_nonneg_left hkey (hA0 i)
  have hbound : x ^ m ≤ (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by
    calc x ^ m = ‖g ^ m‖ := by rw [norm_pow]
      _ = ‖∑ i ∈ Finset.range m, MvPolynomial.eval w (cf i) * g ^ i‖ := by rw [hroot, norm_neg]
      _ ≤ ∑ i ∈ Finset.range m, ‖MvPolynomial.eval w (cf i) * g ^ i‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range m, A i * (x ^ m / B) := Finset.sum_le_sum hterm
      _ = (∑ i ∈ Finset.range m, A i) * (x ^ m / B) := by rw [Finset.sum_mul]
  have hS : ∑ i ∈ Finset.range m, A i = B - 1 := by rw [hBdef]; ring
  have hxm : 0 < x ^ m / B := by positivity
  have hBx : B * (x ^ m / B) = x ^ m := by field_simp
  rw [hS, sub_mul, _root_.one_mul, hBx] at hbound
  linarith
end _root_.GlobalTheory.IntegralCusp
end GlobalTheory.IntegralCusp
