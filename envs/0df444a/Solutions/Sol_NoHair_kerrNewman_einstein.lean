-- Prove2me | solution 1 for NoHair.kerrNewman_einstein
-- status  : ACCEPTED   (prove)
-- author  : @SamenHossain
-- created : 2026-10-13T08:39:15.124051+00:00
-- url     : https://prove2.me/submissions/97674bbe-11ba-4363-afd6-335aa1742695

import Mathlib
import Definitions.Def_NoHair_kerrNewman
import Definitions.Def_NoHair_KerrNewmanEinstein_Base
import Definitions.Def_NoHair_KerrNewmanEinstein_Atoms
import Theorems.Thm_NoHair_KNE_thm_christoffel
import Theorems.Thm_NoHair_KNE_thm_div_one
import Theorems.Thm_NoHair_KNE_thm_div_two
import Theorems.Thm_NoHair_KNE_thm_div_three
import Theorems.Thm_NoHair_KNE_thm_ricci_a
import Theorems.Thm_NoHair_KNE_thm_ricci_b
import Theorems.Thm_NoHair_KNE_thm_ricci_c
import Theorems.Thm_NoHair_KNE_thm_maxwell

/-!
# Kerr–Newman satisfies the Einstein equation

Assembly of the Einstein equation from the closed-form facts proved in the platform theorems
`NoHair.KNE.thm_christoffel`, `thm_div_one/two/three`, `thm_ricci_a/b/c` and `thm_maxwell`
(statements over the definition block `NoHair_KerrNewmanEinstein_Base`). Here: the trace of the
Christoffel symbols vanishes, so its derivative does; the Ricci tensor and the scalar curvature at a
point with `r > 0`; and `maxwellSource` in closed form.
-/

set_option autoImplicit false
set_option linter.all false

open scoped BigOperators
open NoHair

namespace NoHair.KNE

theorem Gam_symm (a m e R K1 K2 K3 W : ℝ) (i j k : Fin 4) : Gam a m e R K1 K2 K3 W i j k = Gam a m e R K1 K2 K3 W i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> rfl

theorem dDivT_symm (a m e R K1 K2 K3 W : ℝ) (i j k : Fin 4) : dDivT a m e R K1 K2 K3 W i j k = dDivT a m e R K1 K2 K3 W i k j := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp only [dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]

theorem RicA_symm (a m e R K1 K2 K3 W : ℝ) (i j : Fin 4) : RicA a m e R K1 K2 K3 W i j = RicA a m e R K1 K2 K3 W j i := by
  fin_cases i <;> fin_cases j <;> rfl

theorem RicS_symm (a m e R K1 K2 K3 W : ℝ) (σ ν : Fin 4) : RicS a m e R K1 K2 K3 W σ ν = RicS a m e R K1 K2 K3 W ν σ := by
  unfold RicS
  congr 1
  · exact Finset.sum_congr rfl (fun ρ _ => dDivT_symm a m e R K1 K2 K3 W ρ ν σ)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
    rw [Gam_symm a m e R K1 K2 K3 W p σ q, Gam_symm a m e R K1 K2 K3 W q p ν]
    ring

theorem trGam_0 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 0 = 0 := by
  simp only [Gam, G000, G101, G202, G303, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-2 * R ^ (3 : ℕ) * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 3 * R ^ (2 : ℕ) * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) + 2 * R * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) - R * W ^ (3 : ℕ) * e ^ (4 : ℕ) - K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem trGam_1 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 1 = 0 := by
  simp only [Gam, G001, G111, G212, G313, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-3 * R ^ (4 : ℕ) * K1 * W ^ (3 : ℕ) * m - 2 * R ^ (3 : ℕ) * K1 * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * K1 * W ^ (3 : ℕ) * e ^ (2 : ℕ) + R ^ (3 : ℕ) * K2 * W ^ (3 : ℕ) * a * m + R ^ (2 : ℕ) * K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m + 3 * R ^ (2 : ℕ) * K1 * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) - R ^ (2 : ℕ) * K2 * W ^ (3 : ℕ) * a * e ^ (2 : ℕ) + 2 * R * K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) - R * K1 * W ^ (3 : ℕ) * e ^ (4 : ℕ) - 3 * R * K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * m - K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) + K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem trGam_2 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 2 = 0 := by
  simp only [Gam, G002, G112, G222, G323, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-3 * R ^ (4 : ℕ) * K2 * W ^ (3 : ℕ) * m - R ^ (3 : ℕ) * K1 * W ^ (3 : ℕ) * a * m - 2 * R ^ (3 : ℕ) * K2 * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * K2 * W ^ (3 : ℕ) * e ^ (2 : ℕ) + R ^ (2 : ℕ) * K1 * W ^ (3 : ℕ) * a * e ^ (2 : ℕ) + R ^ (2 : ℕ) * K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m + 3 * R ^ (2 : ℕ) * K2 * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) + 3 * R * K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * m + 2 * R * K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) - R * K2 * W ^ (3 : ℕ) * e ^ (4 : ℕ) - K1 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (3 : ℕ) * e ^ (2 : ℕ) - K2 * K3 ^ (2 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem trGam_3 (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ 3 = 0 := by
  simp only [Gam, G003, G113, G223, G333, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((-3 * R ^ (4 : ℕ) * K3 * W ^ (3 : ℕ) * m - 2 * R ^ (3 : ℕ) * K3 * W ^ (3 : ℕ) * m ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * K3 * W ^ (3 : ℕ) * e ^ (2 : ℕ) + R ^ (2 : ℕ) * K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m - 3 * R ^ (2 : ℕ) * K3 * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m + 3 * R ^ (2 : ℕ) * K3 * W ^ (3 : ℕ) * m * e ^ (2 : ℕ) + 2 * R * K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m ^ (2 : ℕ) + 2 * R * K3 * W ^ (3 : ℕ) * a ^ (2 : ℕ) * e ^ (2 : ℕ) - R * K3 * W ^ (3 : ℕ) * e ^ (4 : ℕ) + K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (4 : ℕ) * m - K3 ^ (3 : ℕ) * W ^ (3 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ))) * hrel + (0) * hW

theorem scal_zero (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ σ, ∑ ν, ginvA a m e R K1 K2 K3 W σ ν * RicA a m e R K1 K2 K3 W σ ν = 0 := by
  simp only [ginvA, RicA, Ks, fA, etaT, Ric00, Ric01, Ric02, Ric03, Ric11, Ric12, Ric13, Ric22, Ric23, Ric33, Matrix.cons_val, Fin.sum_univ_four]
  linear_combination ((4 * R ^ (3 : ℕ) * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (2 : ℕ) + 4 * R ^ (3 : ℕ) * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (2 : ℕ) + 2 * R ^ (3 : ℕ) * W ^ (4 : ℕ) * m * e ^ (2 : ℕ) - 8 * R ^ (2 : ℕ) * K1 * K2 * W ^ (4 : ℕ) * a * m * e ^ (2 : ℕ) + 4 * R ^ (2 : ℕ) * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * m ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (2 : ℕ) * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (4 : ℕ) + 4 * R ^ (2 : ℕ) * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * m ^ (2 : ℕ) * e ^ (2 : ℕ) - 2 * R ^ (2 : ℕ) * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (4 : ℕ) - 4 * R ^ (2 : ℕ) * W ^ (4 : ℕ) * m ^ (2 : ℕ) * e ^ (2 : ℕ) - R ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (4 : ℕ) + 4 * R * K1 * K2 * W ^ (4 : ℕ) * a * e ^ (4 : ℕ) - 4 * R * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) - 4 * R * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (4 : ℕ) + 2 * R * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) - 4 * R * K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * m * e ^ (4 : ℕ) + 4 * R * W ^ (4 : ℕ) * a ^ (2 : ℕ) * m * e ^ (2 : ℕ) + 4 * R * W ^ (4 : ℕ) * m * e ^ (4 : ℕ) + 2 * K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (4 : ℕ) + K2 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (6 : ℕ) - K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (4 : ℕ) + K3 ^ (2 : ℕ) * W ^ (4 : ℕ) * e ^ (6 : ℕ) - 2 * W ^ (4 : ℕ) * a ^ (2 : ℕ) * e ^ (4 : ℕ) - W ^ (4 : ℕ) * e ^ (6 : ℕ))) * hrel + (0) * hW

theorem trGam (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (σ : Fin 4) :
    ∑ ρ, Gam a m e R K1 K2 K3 W ρ ρ σ = 0 := by
  fin_cases σ
  · exact trGam_0 a m e R K1 K2 K3 W hrel hW
  · exact trGam_1 a m e R K1 K2 K3 W hrel hW
  · exact trGam_2 a m e R K1 K2 K3 W hrel hW
  · exact trGam_3 a m e R K1 K2 K3 W hrel hW

theorem ricS (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    RicS a m e R K1 K2 K3 W μ ν = RicA a m e R K1 K2 K3 W μ ν := by
  fin_cases μ <;> fin_cases ν
  · exact (thm_ricci_a a m e R K1 K2 K3 W hrel hW).1
  · exact (thm_ricci_a a m e R K1 K2 K3 W hrel hW).2.1
  · exact (thm_ricci_a a m e R K1 K2 K3 W hrel hW).2.2.1
  · exact (thm_ricci_a a m e R K1 K2 K3 W hrel hW).2.2.2
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_a a m e R K1 K2 K3 W hrel hW).2.1
  · exact (thm_ricci_b a m e R K1 K2 K3 W hrel hW).1
  · exact (thm_ricci_b a m e R K1 K2 K3 W hrel hW).2
  · exact (thm_ricci_c a m e R K1 K2 K3 W hrel hW).1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_a a m e R K1 K2 K3 W hrel hW).2.2.1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_b a m e R K1 K2 K3 W hrel hW).2
  · exact (thm_ricci_c a m e R K1 K2 K3 W hrel hW).2.1
  · exact (thm_ricci_c a m e R K1 K2 K3 W hrel hW).2.2.1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_a a m e R K1 K2 K3 W hrel hW).2.2.2
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_c a m e R K1 K2 K3 W hrel hW).1
  · rw [RicS_symm, RicA_symm]; exact (thm_ricci_c a m e R K1 K2 K3 W hrel hW).2.2.1
  · exact (thm_ricci_c a m e R K1 K2 K3 W hrel hW).2.2.2

theorem fS (a e R K1 K2 K3 W : ℝ) (m : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    FS a e R K1 K2 K3 W μ ν = FA a e R K1 K2 K3 W μ ν := (thm_maxwell a m e R K1 K2 K3 W hrel hW).1 μ ν

theorem fU (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (α β : Fin 4) :
    ∑ μ, ∑ ν, ginvA a m e R K1 K2 K3 W α μ * ginvA a m e R K1 K2 K3 W β ν * FA a e R K1 K2 K3 W μ ν = FupA a m e R K1 K2 K3 W α β :=
  (thm_maxwell a m e R K1 K2 K3 W hrel hW).2.1 α β

theorem fF (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) :
    ∑ α, ∑ β, FA a e R K1 K2 K3 W α β * FupA a m e R K1 K2 K3 W α β = FFA a m e R K1 K2 K3 W := (thm_maxwell a m e R K1 K2 K3 W hrel hW).2.2.1

theorem tS (a m e R K1 K2 K3 W : ℝ) (hrel : K1 ^ 2 + K2 ^ 2 + K3 ^ 2 = 1) (hW : W * (R ^ 2 + a ^ 2 * K3 ^ 2) = 1) (μ ν : Fin 4) :
    TS a m e R K1 K2 K3 W μ ν = RicA a m e R K1 K2 K3 W μ ν := (thm_maxwell a m e R K1 K2 K3 W hrel hW).2.2.2 μ ν

theorem cp_div (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (ρ ν σ : Fin 4) :
    coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) ρ ν σ) ρ y = dDivT a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) ρ ν σ := by
  fin_cases ρ
  · fin_cases ν <;> fin_cases σ <;> simp only [dDivT, Matrix.cons_val, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
      exact cp_time a (fun R K1 K2 K3 => Gam a m e R K1 K2 K3 (1 / (R ^ 2 + a ^ 2 * K3 ^ 2)) 0 _ _) y
  · exact (thm_div_one m a e y hy).2.2 ν σ
  · exact (thm_div_two m a e y hy).2 ν σ
  · exact (thm_div_three m a e y hy).2 ν σ

theorem diff_tr (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (ρ σ : Fin 4) :
    DifferentiableAt ℝ (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3) (Wf a w) ρ ρ σ) y := by
  fin_cases ρ
  · exact (thm_div_one m a e y hy).1 σ
  · exact (thm_div_one m a e y hy).2.1 σ
  · exact (thm_div_two m a e y hy).1 σ
  · exact (thm_div_three m a e y hy).1 σ

/-! ## Curvature at the point `y` -/

theorem isOpen_U (a : ℝ) : IsOpen {z : E4 | 0 < ksRadius a z} :=
  isOpen_lt continuous_const (continuous_ksRadius a)

theorem cp_chr (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (i j k c : Fin 4) :
    coordPartial (fun z => christoffel (kerrNewmanMetric m a e) z i j k) c y
      = coordPartial (fun w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2)
          (ksNull a w 3) (Wf a w) i j k) c y := by
  unfold coordPartial
  rw [Filter.EventuallyEq.fderiv_eq]
  filter_upwards [(isOpen_U a).mem_nhds hy] with z hz
  exact thm_christoffel m a e z hz i j k

theorem trace_cp_zero (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (σ ν : Fin 4) :
    ∑ ρ, coordPartial (fun z => christoffel (kerrNewmanMetric m a e) z ρ ρ σ) ν y = 0 := by
  simp only [cp_chr m a e y hy]
  have hsum : (fun w => ∑ ρ, Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2)
      (ksNull a w 3) (Wf a w) ρ ρ σ) =ᶠ[nhds y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_U a).mem_nhds hy] with z hz
    exact trGam a m e _ _ _ _ _ (ks_rel a z hz) (ks_W a z hz) σ
  have h1 := fderiv_fun_sum (𝕜 := ℝ) (u := Finset.univ) (x := y)
    (A := fun ρ w => Gam a m e (ksRadius a w) (ksNull a w 1) (ksNull a w 2) (ksNull a w 3)
      (Wf a w) ρ ρ σ)
    (fun ρ _ => diff_tr m a e y hy ρ σ)
  unfold coordPartial
  rw [← ContinuousLinearMap.sum_apply, ← h1, hsum.fderiv_eq]
  simp

theorem ricci_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (σ ν : Fin 4) :
    ricci (kerrNewmanMetric m a e) y σ ν
      = RicA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) σ ν := by
  have hrel := ks_rel a y hy
  have hW := ks_W a y hy
  unfold ricci riemann
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, trace_cp_zero m a e y hy σ ν]
  simp only [cp_chr m a e y hy, cp_div m a e y hy, thm_christoffel m a e y hy, Finset.sum_sub_distrib]
  have htr : ∑ ρ, ∑ l, Gam a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) ρ ρ l
      * Gam a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) l ν σ = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul, trGam a m e _ _ _ _ _ hrel hW, zero_mul, Finset.sum_const_zero]
  rw [htr, ← ricS a m e _ _ _ _ _ hrel hW σ ν]
  unfold RicS
  ring

theorem scal_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    scalarCurvature (kerrNewmanMetric m a e) y = 0 := by
  unfold scalarCurvature
  simp only [invMetric_eq m a e y hy, Matrix.of_apply, ricci_eq m a e y hy]
  exact scal_zero a m e _ _ _ _ _ (ks_rel a y hy) (ks_W a y hy)

theorem einstein_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = RicA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  unfold einsteinTensor
  rw [scal_eq m a e y hy, ricci_eq m a e y hy]
  ring

/-! ## The Maxwell side at `y` -/

theorem pot_eq (a e : ℝ) (z : E4) (hz : 0 < ksRadius a z) :
    e * ksRadius a z ^ 3 / (ksRadius a z ^ 4 + a ^ 2 * z 3 ^ 2) = HA a e (ksRadius a z) (Wf a z) := by
  rw [ks_x3 a z hz]
  unfold HA Wf
  have hR : ksRadius a z ≠ 0 := hz.ne'
  have hS : ksRadius a z ^ 2 + a ^ 2 * ksNull a z 3 ^ 2 ≠ 0 := by positivity
  have hD : ksRadius a z ^ 4 + a ^ 2 * (ksRadius a z * ksNull a z 3) ^ 2 ≠ 0 := by positivity
  field_simp
  try ring

theorem field_closed (a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    kerrNewmanField a e y μ ν
      = FA a e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  have hH := hasCP_H a e y hy
  have hA : ∀ β, HasCP (fun w => kerrNewmanPotential a e w β) y
      (fun k => dHA a e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) k
          * ksNull a y β
        + e * ksRadius a y ^ 3 / (ksRadius a y ^ 4 + a ^ 2 * y 3 ^ 2)
          * dKt a (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) β k) :=
    fun β => hH.mul (hasCP_K a y hy β)
  show coordPartial (fun w => kerrNewmanPotential a e w ν) μ y
    - coordPartial (fun w => kerrNewmanPotential a e w μ) ν y = _
  rw [(hA ν).eq μ, (hA μ).eq ν, pot_eq a e y hy,
    ← fS a e _ _ _ _ _ 0 (ks_rel a y hy) (ks_W a y hy) μ ν]
  simp only [FS, Kv, ← ksNull_eq_Kv a y]

theorem metric_closed (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    kerrNewmanMetric m a e y μ ν
      = gA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  show minkowski μ ν + ksProfile m a e y * ksNull a y μ * ksNull a y ν = _
  rw [profile_eq m a e y hy, minkowski_eq]
  simp only [gA, Kv, ← ksNull_eq_Kv a y]

theorem maxwell_eq (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) (μ ν : Fin 4) :
    maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν
      = RicA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) μ ν := by
  have hrel := ks_rel a y hy
  have hW := ks_W a y hy
  have hraise : ∀ α β, raiseBoth (kerrNewmanMetric m a e) (kerrNewmanField a e) y α β
      = FupA a m e (ksRadius a y) (ksNull a y 1) (ksNull a y 2) (ksNull a y 3) (Wf a y) α β := by
    intro α β
    unfold raiseBoth
    simp only [invMetric_eq m a e y hy, Matrix.of_apply, field_closed a e y hy]
    exact fU a m e _ _ _ _ _ hrel hW α β
  unfold maxwellSource
  simp only [hraise, invMetric_eq m a e y hy, Matrix.of_apply, field_closed a e y hy,
    metric_closed m a e y hy]
  rw [fF a m e _ _ _ _ _ hrel hW, ← tS a m e _ _ _ _ _ hrel hW μ ν]
  rfl


end NoHair.KNE

open NoHair in
theorem solution (m a e : ℝ) (y : E4) (hy : 0 < ksRadius a y) :
    ∀ μ ν, einsteinTensor (kerrNewmanMetric m a e) y μ ν
      = maxwellSource (kerrNewmanMetric m a e) (kerrNewmanField a e) y μ ν := by
  intro μ ν
  rw [NoHair.KNE.einstein_eq m a e y hy, NoHair.KNE.maxwell_eq m a e y hy]
