-- Prove2me | solution 1 for HunterPDE.Sobolev.HasWeakDeriv.convolution_testFunction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T23:35:53.65405+00:00
-- url     : https://prove2.me/submissions/62f883bd-6fd1-4e08-9dab-e34d4c287486

import Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_comp_sub
import Theorems.Thm_HunterPDE_Sobolev_iteratedPartial_convolution_testFunction
import Theorems.Thm_HunterPDE_Sobolev_hasWeakDeriv_of_contDiff
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.Unique

open MeasureTheory ContinuousLinearMap HunterPDE.Sobolev
open scoped Convolution ContDiff
set_option autoImplicit false

theorem solution {n : ℕ}
    {α : Fin n → ℕ} {f d : EuclideanSpace ℝ (Fin n) → ℝ}
    (hd : HasWeakDeriv Set.univ α f d)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hρ : IsTestFunction Set.univ ρ) :
    HasWeakDeriv Set.univ α (ρ ⋆[lsmul ℝ ℝ, volume] f)
      (ρ ⋆[lsmul ℝ ℝ, volume] d) := by
  have hf : LocallyIntegrable f := locallyIntegrableOn_univ.mp hd.1
  have heq : (ρ ⋆[lsmul ℝ ℝ, volume] d) =
      (iteratedPartial α ρ ⋆[lsmul ℝ ℝ, volume] f) := by
    funext x
    have ht : IsTestFunction Set.univ (fun y => ρ (x-y)) := by
      refine ⟨hρ.1.comp (contDiff_const.sub contDiff_id), ?_, Set.subset_univ _⟩
      simpa only [Function.comp_def, Homeomorph.trans_apply,
        Homeomorph.coe_addLeft, Homeomorph.coe_neg, sub_eq_add_neg] using
        hρ.2.1.comp_homeomorph
          ((Homeomorph.neg (EuclideanSpace ℝ (Fin n))).trans (Homeomorph.addLeft x))
    have hw := hd.2.2 (fun y => ρ (x-y)) ht
    simp only [Measure.restrict_univ] at hw
    rw [HunterPDE.Sobolev.iteratedPartial_comp_sub α hρ.1 x] at hw
    have hs : (-1 : ℝ)^(∑ i, α i) * (-1 : ℝ)^(∑ i, α i) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      simp
    simp_rw [mul_left_comm (f _) ((-1 : ℝ)^(∑ i, α i))] at hw
    rw [integral_const_mul, ← mul_assoc, hs, one_mul] at hw
    rw [convolution_lsmul_swap, convolution_lsmul_swap]
    simp only [smul_eq_mul]
    simpa only [mul_comm] using hw
  have hc : ContDiff ℝ ∞ (ρ ⋆[lsmul ℝ ℝ, volume] f) :=
    hρ.2.1.contDiff_convolution_left (lsmul ℝ ℝ) hρ.1 hf
  rw [← HunterPDE.Sobolev.iteratedPartial_convolution_testFunction α hρ hf] at heq
  rw [heq]
  exact HunterPDE.Sobolev.hasWeakDeriv_of_contDiff _ hc α
