-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.exists_polynomial_mul_analyticAt_off_lattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:23:12.534878+00:00
-- url     : https://prove2.me/submissions/db5c02ea-8915-4ba5-b3de-679c7053ef09

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational
import Theorems.Thm_GroundTheory_Global_Elliptic_analyticAt_eval
import Theorems.Thm_GroundTheory_Global_Elliptic_isPeriodic_weierstrassP
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_eq_of_mk_eq
import Theorems.Thm_GroundTheory_Global_Elliptic_IsPeriodic_sub
import Theorems.Thm_GroundTheory_Global_Elliptic_Torus_mk_eq_mk_iff
import Theorems.Thm_GroundTheory_Global_Elliptic_finite_image_singularSet


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {f : ℂ → ℂ} (hf : Meromorphic f)
    (hp : IsPeriodic L f) :
    ∃ Q : ℂ[X], Q ≠ 0 ∧ ∀ z ∉ L.lattice, AnalyticAt ℂ (fun w ↦ Q.eval (℘[L] w) * f w) z := by
  classical
  have hT := finite_image_singularSet L hf hp
  let rep : Torus L → ℂ := Function.surjInv (Torus.mk_surjective L)
  have hrep : ∀ t, Torus.mk L (rep t) = t := Function.surjInv_eq _
  let n : Torus L → ℕ := fun t ↦ (hf (rep t)).choose
  have hn : ∀ t, AnalyticAt ℂ (fun z ↦ (z - rep t) ^ n t • f z) (rep t) := fun t ↦
    (hf (rep t)).choose_spec
  let N := hT.toFinset.sup n
  refine ⟨∏ t ∈ hT.toFinset, (X - C (℘[L] (rep t))) ^ N, ?_, fun z hz ↦ ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun t _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have h℘ : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
  by_cases hfz : AnalyticAt ℂ f z
  · exact (analyticAt_eval h℘ _).mul hfz
  have ht : Torus.mk L z ∈ hT.toFinset := hT.mem_toFinset.2 ⟨z, hfz, rfl⟩
  have hza : z - rep (Torus.mk L z) ∈ L.lattice := (Torus.mk_eq_mk_iff L).1 (hrep _).symm
  have h℘a : ℘[L] (rep (Torus.mk L z)) = ℘[L] z :=
    isPeriodic_weierstrassP.eq_of_mk_eq (hrep _)
  have hφ : AnalyticAt ℂ (fun w ↦ ℘[L] w - ℘[L] z) z := h℘.sub analyticAt_const
  have hdφ : AnalyticAt ℂ (dslope (fun w ↦ ℘[L] w - ℘[L] z) z) z := by
    obtain ⟨p, hp'⟩ := hφ
    exact ⟨_, hp'.has_fpower_series_dslope_fslope⟩
  have hφeq : ∀ w, ℘[L] w - ℘[L] z = (w - z) * dslope (fun w ↦ ℘[L] w - ℘[L] z) z w := by
    intro w
    have := sub_smul_dslope_of_zero (f := fun w ↦ ℘[L] w - ℘[L] z) (sub_self _) w
    simp only [smul_eq_mul] at this
    exact this.symm
  have hnN : n (Torus.mk L z) ≤ N := Finset.le_sup ht
  have h1 : AnalyticAt ℂ (fun w ↦ (w - z) ^ n (Torus.mk L z) * f w) z := by
    set a := rep (Torus.mk L z)
    have hF : AnalyticAt ℂ (fun u ↦ (u - a) ^ n (Torus.mk L z) • f u) (z - (z - a)) := by
      rw [sub_sub_cancel]; exact hn _
    have := hF.comp (f := fun w ↦ w - (z - a)) (by fun_prop)
    refine this.congr (Eventually.of_forall fun w ↦ ?_)
    simp only [Function.comp_apply, smul_eq_mul]
    rw [show w - (z - a) - a = w - z by ring, hp.sub w hza]
  have hfN : AnalyticAt ℂ (fun w ↦ (w - z) ^ N * f w) z := by
    have e : (fun w ↦ (w - z) ^ N * f w) =
        fun w ↦ (w - z) ^ (N - n (Torus.mk L z)) * ((w - z) ^ n (Torus.mk L z) * f w) := by
      funext w; rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnN]
    rw [e]
    fun_prop
  generalize dslope (fun w ↦ ℘[L] w - ℘[L] z) z = D at hdφ hφeq
  refine (((hdφ.pow N).mul (analyticAt_eval h℘
    (∏ s ∈ hT.toFinset.erase (Torus.mk L z), (X - C (℘[L] (rep s))) ^ N))).mul hfN).congr
    (Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [← Finset.mul_prod_erase hT.toFinset (fun s ↦ (X - C (℘[L] (rep s))) ^ N) ht]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, h℘a]
  rw [hφeq w, mul_pow]
  ring
end GroundTheory.Global.Elliptic
