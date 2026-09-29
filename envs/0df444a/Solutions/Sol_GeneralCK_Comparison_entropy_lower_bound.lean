-- Prove2me | solution 1 for GeneralCK.Comparison.entropy_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:22:38.344821+00:00
-- url     : https://prove2.me/submissions/f8157f91-d7ae-4de6-bb43-8f37968f8d99

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_Comparison_antitone_ode_comparison
import Theorems.Thm_GeneralCK_H_pos
import Theorems.Thm_GeneralCK_H_strictMonoOn
import Theorems.Thm_GeneralCK_entropyInverse_H_lower
import Theorems.Thm_GeneralCK_eta_antitoneOn

open scoped BigOperators
namespace GeneralCK
open scoped BigOperators















theorem log_two_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)



@[simp] theorem H_half : H (1 / 2) = 1 := by
  have h : Real.log 2 ≠ 0 := ne_of_gt log_two_pos
  simpa [H, one_div] using div_self h





theorem H_le_one (p : ℝ) : H p ≤ 1 := by
  rw [H, div_le_one log_two_pos]
  exact Real.binEntropy_le_log_two

theorem H_continuous : Continuous H :=
  Real.binEntropy_continuous.div_const _

end GeneralCK

namespace GeneralCK.Comparison
open Set







theorem noiseParameter_mem {eps t : ℝ} (he : 0 < eps) (he' : eps < 1 / 2)
    (ht : 0 ≤ t) : noiseParameter eps t ∈ Ioo 0 (1 / 2) := by
  have hp := Real.exp_pos (-2 * t)
  have hle : Real.exp (-2 * t) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hm : 0 < 1 - 2 * eps := by linarith
  have hmul : Real.exp (-2 * t) * (1 - 2 * eps) ≤ 1 - 2 * eps :=
    mul_le_of_le_one_left hm.le hle
  have hmulpos := mul_pos hp hm
  dsimp [noiseParameter]
  constructor <;> linarith

@[simp] theorem noiseParameter_zero (eps : ℝ) : noiseParameter eps 0 = eps := by
  simp [noiseParameter]

theorem hasDerivAt_noiseParameter (eps t : ℝ) :
    HasDerivAt (noiseParameter eps) (1 - 2 * noiseParameter eps t) t := by
  have hd := (((hasDerivAt_id t).const_mul (-2)).exp.mul_const (1 - 2 * eps)).const_sub 1
  convert! hd.div_const 2 using 1
  simp only [noiseParameter, id_eq]
  ring

theorem hasDerivAt_H {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt H (J p) p := by
  have hl : Real.log ((1 - p) / p) = Real.log (1 - p) - Real.log p :=
    Real.log_div (by linarith) (ne_of_gt hp)
  simpa [H, J, hl] using!
    (Real.hasDerivAt_binEntropy (ne_of_gt hp) (by linarith)).div_const (Real.log 2)

theorem eta_H {p : ℝ} (hp : 0 < p) (hp' : p < 1 / 2) :
    eta (H p) = (1 - 2 * p) * J p := by
  have hlt : H p < 1 := by
    rw [← H_half]
    exact H_strictMonoOn ⟨hp.le, hp'.le⟩ ⟨by norm_num, le_rfl⟩ hp'
  simp [eta, ne_of_lt hlt, entropyInverse_H_lower hp.le hp'.le]

theorem hasDerivAt_entropy_trajectory {eps t : ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (ht : 0 ≤ t) :
    HasDerivAt (fun s => H (noiseParameter eps s))
      (eta (H (noiseParameter eps t))) t := by
  have hp := noiseParameter_mem he he' ht
  rw [eta_H hp.1 hp.2]
  convert! (hasDerivAt_H hp.1 (by linarith [hp.2])).comp t
    (hasDerivAt_noiseParameter eps t) using 1
  ring



end GeneralCK.Comparison
namespace GeneralCK.Comparison
end GeneralCK.Comparison

open GeneralCK GeneralCK.Comparison in
open Set in
theorem solution {eps T : ℝ} {delta delta' : ℝ → ℝ}
    (he : 0 < eps) (he' : eps < 1 / 2) (hT : 0 ≤ T)
    (hc : ContinuousOn delta (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt delta (delta' t) (Ici t) t)
    (hrange : ∀ t ∈ Ico 0 T, delta t ∈ Ioc 0 1)
    (hprod : ∀ t ∈ Ico 0 T, eta (delta t) ≤ delta' t)
    (h0 : H eps ≤ delta 0) : H (noiseParameter eps T) ≤ delta T := by
  apply antitone_ode_comparison hT eta_antitoneOn
    (u := fun t => H (noiseParameter eps t))
    (u' := fun t => eta (H (noiseParameter eps t)))
    (v' := delta')
  · exact H_continuous.comp_continuousOn (fun t _ =>
      (hasDerivAt_noiseParameter eps t).continuousAt.continuousWithinAt)
  · exact hc
  · intro t ht
    exact (hasDerivAt_entropy_trajectory he he' ht.1).hasDerivWithinAt
  · exact hd
  · intro t ht
    have hp := noiseParameter_mem he he' ht.1
    exact ⟨H_pos hp.1 (by linarith [hp.2]), H_le_one _⟩
  · exact hrange
  · intro _ _
    exact le_rfl
  · exact hprod
  · simpa using h0
