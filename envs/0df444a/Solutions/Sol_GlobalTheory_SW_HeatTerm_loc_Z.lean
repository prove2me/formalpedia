-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.loc_Z
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:42:43.913823+00:00
-- url     : https://prove2.me/submissions/7e5317b4-460d-4cd3-8966-8a0b760a977f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero
import Theorems.Thm_GlobalTheory_SW_HeatTerm_det_one_add
import Theorems.Thm_GlobalTheory_SW_HeatTerm_inv_one_add
import Theorems.Thm_GlobalTheory_SW_HeatTerm_quad_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution {n N : ℕ} (C D Z : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (h : (C * Z + D).det ≠ 0) (a b : Fin N) :
    HasDerivAt (fun s : ℂ => loc C D (Z + Matrix.single a b s) z z')
      ((-(n : ℂ) * ((C * Z + D)⁻¹ * C) b a + 2 * Real.pi * I *
        ∑ k, (z' k ᵥ* ((C * Z + D)⁻¹ * C)) a * (((C * Z + D)⁻¹ * C) *ᵥ z k) b) *
        loc C D Z z z') 0 := by
  set M := C * Z + D with hM
  set S := M⁻¹ * C with hS
  have hu : IsUnit M.det := Ne.isUnit h
  have hfac : ∀ s, C * (Z + Matrix.single a b s) + D = M * (1 + S * Matrix.single a b s) := by
    intro s
    rw [Matrix.mul_add M, mul_one, hS, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hu, one_mul, hM, Matrix.mul_add]
    abel
  set q := ∑ k, z' k ⬝ᵥ S *ᵥ z k with hq
  set r := ∑ k, (z' k ᵥ* S) a * (S *ᵥ z k) b with hr
  set c := S b a with hc
  have hl : HasDerivAt (fun s : ℂ => 1 + s * c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).mul_const c).const_add 1
  have hev : ∀ᶠ s in 𝓝 (0 : ℂ), 1 + s * c ≠ 0 :=
    hl.continuousAt.eventually_ne (by simp)
  have heq : (fun s : ℂ => loc C D (Z + Matrix.single a b s) z z') =ᶠ[𝓝 0]
      fun s => ((M.det * (1 + s * c)) ^ n *
        cexp (2 * Real.pi * I * (q - s / (1 + s * c) * r)))⁻¹ := by
    filter_upwards [hev] with s hs
    rw [loc, hfac, Matrix.det_mul, det_one_add, Matrix.mul_inv_rev, inv_one_add _ _ _ _ hs,
      Matrix.mul_assoc, ← hS, sub_mul, one_mul, Matrix.smul_mul]
    simp only [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul,
      quad_single, Finset.sum_sub_distrib, smul_eq_mul, ← Finset.mul_sum]
    rfl
  refine HasDerivAt.congr_of_eventuallyEq ?_ heq
  have h1 := (hl.const_mul M.det).fun_pow n
  have h2 := (((((hasDerivAt_id (0 : ℂ)).fun_div hl (by simp)).mul_const r).const_sub q).const_mul
    (2 * Real.pi * I)).cexp
  have h3 := (h1.fun_mul h2).fun_inv (by simp [h])
  refine HasDerivAt.congr_deriv h3 ?_
  have he := Complex.exp_ne_zero (2 * Real.pi * I * q)
  rw [loc, ← hM, ← hS, ← hq]
  simp only [id, zero_mul, add_zero, mul_one, zero_div, sub_zero, one_mul, one_pow, div_one]
  rcases n with _ | n
  · simp
    field_simp
  · simp only [Nat.add_sub_cancel]
    field_simp
    ring
end GlobalTheory.SW.HeatTerm
