-- Prove2me | solution 1 for NumberField.TateGlobal.exists_ideleNorm_eq_and_snd_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/3f098183-2022-572e-9954-d494e213302b

import Mathlib
import Definitions.Def_NumberField_TateGlobalZeta
import Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
p2m_attr_erase "instance" "instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.TateGlobal IsDedekindDomain

noncomputable section

namespace RS11DIL

variable (K : Type) [Field K] [NumberField K]

private def archIdele (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) : (AdeleRing (𝓞 K) K)ˣ where
  val := ((fun w => ((t w : (w.Completion)ˣ) : w.Completion)), 1)
  inv := ((fun w => (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion)), 1)
  val_inv := by
    refine Prod.ext ?_ ?_
    · funext w
      change ((t w : (w.Completion)ˣ) : w.Completion) * (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.mul_inv _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1
  inv_val := by
    refine Prod.ext ?_ ?_
    · funext w
      change (((t w)⁻¹ : (w.Completion)ˣ) : w.Completion) * ((t w : (w.Completion)ˣ) : w.Completion) = 1
      exact Units.inv_mul _
    · change (1 : FiniteAdeleRing (𝓞 K) K) * 1 = 1
      exact one_mul 1

private theorem archIdele_fst (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) (w : InfinitePlace K) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).1 w = t w := rfl

private theorem archIdele_snd (t : ∀ w : InfinitePlace K, (w.Completion)ˣ) :
    ((archIdele K t : (AdeleRing (𝓞 K) K))).2 = 1 := rfl

private theorem exists_arch_norm_eq (r : ℝ) (hr : 0 < r) :
    ∃ t : ∀ w : InfinitePlace K, (w.Completion)ˣ, ∀ w, ‖((t w : (w.Completion)ˣ) : w.Completion)‖ = r := by
  have key : ∀ w : InfinitePlace K, ∃ u : (w.Completion)ˣ, ‖(u : w.Completion)‖ = r := by
    intro w
    by_cases hw : w.IsReal
    · let e := InfinitePlace.Completion.isometryEquivRealOfIsReal hw
      have hnorm : ‖e.symm r‖ = r := by
        have h1 : ‖e.symm r‖ = dist (e.symm r) (e.symm 0) := by
          rw [show e.symm 0 = 0 from map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm, dist_zero_right]
        rw [h1, e.symm.dist_eq, Real.dist_eq, sub_zero, abs_of_pos hr]
      have hne : e.symm r ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; exact hr.ne' hnorm.symm
      exact ⟨Units.mk0 _ hne, hnorm⟩
    · have hw' : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      let e := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw'
      have hnorm : ‖e.symm (r : ℂ)‖ = r := by
        have h1 : ‖e.symm (r : ℂ)‖ = dist (e.symm r) (e.symm 0) := by
          rw [show e.symm 0 = 0 from map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw').symm, dist_zero_right]
        rw [h1, e.symm.dist_eq, dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      have hne : e.symm (r : ℂ) ≠ 0 := fun h => by rw [h, norm_zero] at hnorm; exact hr.ne' hnorm.symm
      exact ⟨Units.mk0 _ hne, hnorm⟩
  choose t ht using key
  exact ⟨t, ht⟩

end RS11DIL

end

theorem solution
    (K : Type) [Field K] [NumberField K] (r : ℝ) (hr : 0 < r) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧ ideleNorm K z = r := by
  set d : ℕ := Module.finrank ℚ K with hd
  have hdpos : 0 < d := Module.finrank_pos
  have hdpos' : 0 < (d : ℝ) := by exact_mod_cast hdpos
  set ρ : ℝ := r ^ (1 / (d : ℝ)) with hρ
  have hρpos : 0 < ρ := Real.rpow_pos_of_pos hr _
  obtain ⟨t, ht⟩ := RS11DIL.exists_arch_norm_eq K ρ hρpos
  refine ⟨RS11DIL.archIdele K t, RS11DIL.archIdele_snd K t, ?_⟩
  rw [NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K _ (RS11DIL.archIdele_snd K t)]
  simp_rw [RS11DIL.archIdele_fst, ht]
  rw [Finset.prod_pow_eq_pow_sum, InfinitePlace.sum_mult_eq, ← hd, hρ, ← Real.rpow_natCast,
    ← Real.rpow_mul hr.le, one_div_mul_cancel hdpos'.ne', Real.rpow_one]

end S_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one
end P2MW
export P2MW.S_NumberField_TateGlobal_exists_ideleNorm_eq_and_snd_eq_one (solution)
