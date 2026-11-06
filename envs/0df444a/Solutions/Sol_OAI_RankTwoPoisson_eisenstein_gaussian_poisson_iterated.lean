-- Prove2me | solution 1 for OAI.RankTwoPoisson.eisenstein_gaussian_poisson_iterated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:28:02.068327+00:00
-- url     : https://prove2.me/submissions/9e999fcb-ba37-43df-8e14-a83ba96fdc60

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_RankTwoPoisson_eis_gauss_summable
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk


section
namespace OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT ConcreteBreveE
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace PowerExtraction
end PowerExtraction
namespace ActualEisensteinCubic
open EisensteinEmbedding ConcreteTraceCRT Complex
end ActualEisensteinCubic
namespace GaussianAbelPartition
open ConcreteTraceCRT ConcreteBreveE ActualEisensteinCubic
end GaussianAbelPartition
namespace ActualEisensteinCubic
end ActualEisensteinCubic
namespace GaussianFiberEquiv
open ActualEisensteinCubic
end GaussianFiberEquiv
namespace RankTwoPoisson
open Real
private theorem gauss_int_summable {a : ℂ} (ha : 0 < a.re) :
    Summable (fun n : ℤ => Complex.exp (-((Real.pi : ℂ) * a) * (n : ℂ) ^ 2)) := by
  have hpa : 0 < ((Real.pi : ℂ) * a).re := by
    simpa using mul_pos Real.pi_pos ha
  exact summable_of_isBigO (Real.summable_abs_int_rpow (show (1 : ℝ) < 2 by norm_num))
    ((isLittleO_exp_neg_mul_sq_cocompact hpa (-2)).isBigO.comp_tendsto
      Int.tendsto_coe_cofinite)
private theorem cg_summable {a : ℂ} (ha : 0 < a.re) : Summable (cg a) :=
  gauss_int_summable ha
private theorem phase_norm (k n : ℤ) : ‖phase k n‖ = 1 := by
  simp [phase, Complex.norm_exp, Complex.mul_re]
private theorem g1_summable {t : ℝ} (ht : 0 < t) : Summable (g1 t) := by
  have htinv : 0 < t⁻¹ := inv_pos.mpr ht
  have ht3 : 0 < 3 * t / 4 := by positivity
  have h1 := (cg_summable (a := ((t⁻¹ : ℝ) : ℂ)) (by simpa using htinv)).norm
  have h2 := (cg_summable (a := (((3 * t) / 4 : ℝ) : ℂ)) (by simpa using ht3)).norm
  have hmaj : Summable (fun z : ℤ × ℤ =>
      ‖cg ((t⁻¹ : ℝ) : ℂ) z.1‖ * ‖cg (((3 * t) / 4 : ℝ) : ℂ) z.2‖) :=
    h1.mul_of_nonneg h2 (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  refine hmaj.of_norm_bounded ?_
  intro z
  simp [g1,  phase_norm]
private theorem eisGauss_split (t : ℝ) (m n : ℤ) :
    eisGauss t (m, n) =
      Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
        Complex.exp (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
          2 * (Real.pi : ℂ) * (((t : ℂ) * (n : ℂ)) / 2) * (m : ℂ)) := by
  dsimp [eisGauss, eisQ]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
private theorem eis_exponent_identity {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    (-(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2) +
      (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * ((t : ℂ) * (n : ℂ) / 2)) ^ 2) =
      (-(Real.pi : ℂ) * (((t⁻¹ : ℝ) : ℂ)) * (k : ℂ) ^ 2) +
        (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2) +
        (((-Real.pi * (k : ℝ) * (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ht
  push_cast
  field_simp [ht0]
  ring_nf
  simp [Complex.I_sq]
  ring
private theorem first_transform_term {t : ℝ} (ht : 0 < t) (k n : ℤ) :
    Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) *
      Complex.exp (-(Real.pi : ℂ) / (t : ℂ) *
        ((k : ℂ) + Complex.I * (((t : ℂ) * (n : ℂ)) / 2)) ^ 2) =
      g1 t (k, n) := by
  have hn : ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ) =
      -(Real.pi : ℂ) * (t : ℂ) * (n : ℂ) ^ 2 := by
    push_cast
    ring
  rw [hn, ← Complex.exp_add, eis_exponent_identity ht k n]
  simp only [Complex.exp_add]
  dsimp [g1, cg, phase]
  push_cast
  ring_nf
private theorem first_poisson_slice {t : ℝ} (ht : 0 < t) (n : ℤ) :
    (∑' m : ℤ, eisGauss t (m, n)) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
  have htc : 0 < (t : ℂ).re := by simpa using ht
  let C : ℂ := Complex.exp ((-Real.pi * t * (n : ℝ) ^ 2 : ℝ) : ℂ)
  let B : ℂ := ((t : ℂ) * (n : ℂ)) / 2
  let F : ℤ → ℂ := fun m => Complex.exp
    (-(Real.pi : ℂ) * (t : ℂ) * (m : ℂ) ^ 2 +
      2 * (Real.pi : ℂ) * B * (m : ℂ))
  let H : ℤ → ℂ := fun k => Complex.exp
    (-(Real.pi : ℂ) / (t : ℂ) * ((k : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    exact eisGauss_split t m n
  have hpoisson : (∑' m : ℤ, F m) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k := by
    exact Complex.tsum_exp_neg_quadratic htc B
  calc
    (∑' m : ℤ, eisGauss t (m, n)) = C * ∑' m : ℤ, F m := hsplit
    _ = C * ((1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, H k) := by rw [hpoisson]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * (C * ∑' k : ℤ, H k) := by ring
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) * ∑' k : ℤ, g1 t (k, n) := by
      congr 1
      rw [← tsum_mul_left]
      apply tsum_congr
      intro k
      exact first_transform_term ht k n
private theorem second_transform_term (t : ℝ) (k n : ℤ) :
    cg ((((3 * t) / 4 : ℝ) : ℂ)) n * phase k n =
      Complex.exp (-(Real.pi : ℂ) * ((((3 * t) / 4 : ℝ) : ℂ)) * (n : ℂ) ^ 2 +
        2 * (Real.pi : ℂ) * (-(Complex.I * (k : ℂ)) / 2) * (n : ℂ)) := by
  dsimp [cg, phase]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring
private theorem second_poisson_slice {t : ℝ} (ht : 0 < t) (k : ℤ) :
    (∑' n : ℤ, g1 t (k, n)) =
      (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' l : ℤ, dualTerm t (k, l) := by
  have ht3 : 0 < 3 * t / 4 := by positivity
  have ht3c : 0 < (((3 * t) / 4 : ℝ) : ℂ).re := by simpa using ht3
  let A : ℂ := (((3 * t) / 4 : ℝ) : ℂ)
  let B : ℂ := -(Complex.I * (k : ℂ)) / 2
  let C : ℂ := cg ((t⁻¹ : ℝ) : ℂ) k
  let F : ℤ → ℂ := fun n => Complex.exp
    (-(Real.pi : ℂ) * A * (n : ℂ) ^ 2 + 2 * (Real.pi : ℂ) * B * (n : ℂ))
  let H : ℤ → ℂ := fun l => Complex.exp
    (-(Real.pi : ℂ) / A * ((l : ℂ) + Complex.I * B) ^ 2)
  have hsplit : (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    calc
      g1 t (k, n) = C * (cg A n * phase k n) := by
        dsimp [g1, C, A]
        ring
      _ = C * F n := by rw [second_transform_term t k n]
  have hpoisson : (∑' n : ℤ, F n) =
      (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l :=
    Complex.tsum_exp_neg_quadratic ht3c B
  have hterm (l : ℤ) : C * H l = dualTerm t (k,l) := by
    have hb : Complex.I * B = (k : ℂ) / 2 := by
      dsimp [B]
      field_simp
      ring_nf
      simp [Complex.I_sq]
    dsimp [H, dualTerm, C, A]
    rw [hb]
  calc
    (∑' n : ℤ, g1 t (k,n)) = C * ∑' n : ℤ, F n := hsplit
    _ = C * ((1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, H l) := by rw [hpoisson]
    _ = (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) := by ring
    _ = (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' l : ℤ, dualTerm t (k,l) := by
      change (1 / A ^ (1 / 2 : ℂ)) * (C * ∑' l : ℤ, H l) =
        (1 / A ^ (1 / 2 : ℂ)) * ∑' l : ℤ, dualTerm t (k,l)
      congr 1
      rw [← tsum_mul_left]
      exact tsum_congr hterm
end RankTwoPoisson
end
end OAI
end

set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.RankTwoPoisson
open Real
namespace OAI.RankTwoPoisson
theorem _root_.solution {t : ℝ} (ht : 0 < t) :
    (∑' z : ℤ × ℤ, eisGauss t z) =
      (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
        (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
        ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
  have hE := eis_gauss_summable ht
  have hG := g1_summable ht
  have hEcomm :
      (∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n)) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) :=
    (show Summable (Function.uncurry (fun m n : ℤ => eisGauss t (m,n))) from hE).tsum_comm
  have hGcomm :
      (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) =
        ∑' k : ℤ, ∑' n : ℤ, g1 t (k,n) :=
    (show Summable (Function.uncurry (fun k n : ℤ => g1 t (k,n))) from hG).tsum_comm
  calc
    (∑' z : ℤ × ℤ, eisGauss t z) =
        ∑' m : ℤ, ∑' n : ℤ, eisGauss t (m,n) := hE.tsum_prod
    _ = ∑' n : ℤ, ∑' m : ℤ, eisGauss t (m,n) := hEcomm.symm
    _ = ∑' n : ℤ, (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, g1 t (k,n) := by
      apply tsum_congr
      intro n
      exact first_poisson_slice ht n
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' n : ℤ, ∑' k : ℤ, g1 t (k,n)) := tsum_mul_left
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, ∑' n : ℤ, g1 t (k,n)) := by
      rw [hGcomm]
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (∑' k : ℤ, (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
            ∑' l : ℤ, dualTerm t (k,l)) := by
      congr 1
      apply tsum_congr
      intro k
      exact second_poisson_slice ht k
    _ = (1 / (t : ℂ) ^ (1 / 2 : ℂ)) *
          (1 / ((((3 * t) / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) *
          ∑' k : ℤ, ∑' l : ℤ, dualTerm t (k,l) := by
      rw [tsum_mul_left]
      ring
end OAI.RankTwoPoisson
