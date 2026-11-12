-- Prove2me | solution 1 for OAI.InvariantIsing.finiteMagneticFunctional_real_profile
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T05:17:12.090218+00:00
-- url     : https://prove2.me/submissions/3b101103-57e2-422a-842f-97adf84aac45
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.Fin.InsertNth
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Definitions.Def_InvariantIsing
import Definitions.Def_OAIQ258001
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticFunctional_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteMagneticVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_finiteVariational_ne_top_bot
import Theorems.Thm_OAI_InvariantIsing_magneticVariational_inward_mono

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticInwardApproximation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational approximation toward zero improves the constrained entropy.
This avoids a height-dependent continuity estimate for the magnetic profile. -/
noncomputable section
open Set
open scoped BigOperators
namespace InvariantIsing

lemma exists_inward_rat_close {x δ : ℝ} (hx : |x| < 1) (hδ : 0 < δ) :
    ∃ q : ℚ, |(q:ℝ)| ≤ |x| ∧ |(q:ℝ)| < 1 ∧ |x-(q:ℝ)| < δ := by
  by_cases hz : x=0
  · subst x
    exact ⟨0,by simp,by norm_num,by simpa using hδ⟩
  have hp : 0 < |x| := abs_pos.mpr hz
  have hi : max 0 (|x|-δ) < |x| := max_lt hp (by linarith)
  obtain ⟨q,hq,hqx⟩ := exists_rat_btwn hi
  have hq0 : 0 < (q:ℝ) := (le_max_left _ _).trans_lt hq
  have hqd : |x|-(q:ℝ)<δ := by have := (le_max_right _ _).trans_lt hq; linarith
  by_cases hxp : 0 ≤ x
  · refine ⟨q,?_,?_,?_⟩
    · rw [abs_of_pos hq0]
      exact hqx.le
    · rw [abs_of_pos hq0]; exact hqx.trans hx
    · rw [abs_of_nonneg (by rw [abs_of_nonneg hxp] at hqx; linarith)]
      rwa [abs_of_nonneg hxp] at hqd
  · refine ⟨-q,?_,?_,?_⟩
    · simpa only [Rat.cast_neg,abs_neg,abs_of_pos hq0] using hqx.le
    · simpa only [Rat.cast_neg,abs_neg,abs_of_pos hq0] using hqx.trans hx
    · rw [Rat.cast_neg,abs_of_nonpos (by rw [abs_of_neg (lt_of_not_ge hxp)] at hqx; linarith)]
      rw [abs_of_neg (lt_of_not_ge hxp)] at hqd
      linarith

end InvariantIsing

end

end OAI
end

section
-- module Solutions.OAIQ258_II.InvariantIsing_Magnetic_MagneticRealProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rational supremum also dominates every real interior profile.
Approximation toward zero only increases its constrained entropy. -/
noncomputable section
open scoped BigOperators
namespace InvariantIsing

lemma finiteMagneticFunctional_real_profile_oai {A ι : Type*} [Fintype A] [Fintype ι]
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a=1)
    (γ b mag : A → ℝ) (hγ : ∀ a, 0 ≤ γ a) (hγsum : ∑ a, γ a=1)
    (hmag : ∀ a, |mag a| < 1) :
    (∑ a, γ a*b a*mag a)+
      (magneticVariationalFunctional (finiteR ρ eig hρ hsum) γ mag).toReal ≤
      (finiteMagneticFunctional (finiteR ρ eig hρ hsum) γ b).toReal := by
  classical
  let R := finiteR ρ eig hρ hsum
  let V := fun s => (magneticVariationalFunctional R γ s).toReal
  let F := (finiteMagneticFunctional R γ b).toReal
  let C := ∑ a, γ a* |b a|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun a _ => mul_nonneg (hγ a) (abs_nonneg _))
  have hv := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ mag hγ hγsum
    (fun a => (hmag a).le)
  have hr := finiteVariational_ne_top_bot ρ eig hρ hsum
  have hf := finiteMagneticFunctional_ne_top_bot R γ b hγ hγsum hr.1 hr.2
  by_contra hnot
  let gap := (∑ a, γ a*b a*mag a)+V mag-F
  have hgap : 0 < gap := sub_pos.mpr (lt_of_not_ge hnot)
  let δ := gap/(2*(C+1))
  have hδ : 0 < δ := div_pos hgap (by positivity)
  choose q hqabs hq hclose using fun a => exists_inward_rat_close (hmag a) hδ
  let qm : RationalMagnetization A := ⟨q,hq⟩
  have hqv := finiteMagneticVariational_ne_top_bot ρ eig hρ hsum γ
    (fun a => (q a : ℝ)) hγ hγsum (fun a => (hq a).le)
  have hmono := magneticVariational_inward_mono R γ (fun a => (q a : ℝ)) mag hγ hmag hqabs
  rw [← EReal.coe_toReal hv.1 hv.2,← EReal.coe_toReal hqv.1 hqv.2] at hmono
  have hV : V mag ≤ V (fun a => (q a : ℝ)) := EReal.coe_le_coe_iff.mp hmono
  have hsup := le_iSup (fun t : RationalMagnetization A =>
    ((∑ a, γ a*b a*(t.val a : ℝ) : ℝ) : EReal)+
      magneticVariationalFunctional R γ (fun a => (t.val a : ℝ))) qm
  change ((∑ a, γ a*b a*(q a : ℝ) : ℝ) : EReal)+
    magneticVariationalFunctional R γ (fun a => (q a : ℝ)) ≤ finiteMagneticFunctional R γ b at hsup
  rw [← EReal.coe_toReal hqv.1 hqv.2,← EReal.coe_add,← EReal.coe_toReal hf.1 hf.2] at hsup
  have hsup' : (∑ a, γ a*b a*(q a : ℝ))+V (fun a => (q a : ℝ)) ≤ F :=
    EReal.coe_le_coe_iff.mp hsup
  have hdiff : (∑ a, γ a*b a*mag a)-(∑ a, γ a*b a*(q a : ℝ)) ≤ C*δ := by
    rw [← Finset.sum_sub_distrib,show C*δ=∑ a, γ a* |b a| * δ by rw [Finset.sum_mul]]
    apply Finset.sum_le_sum
    intro a _
    calc
      _ = γ a*b a*(mag a-(q a : ℝ)) := by ring
      _ ≤ |γ a*b a*(mag a-(q a : ℝ))| := le_abs_self _
      _ = γ a* |b a| * |mag a-(q a : ℝ)| := by rw [abs_mul,abs_mul,abs_of_nonneg (hγ a)]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hclose a).le (mul_nonneg (hγ a) (abs_nonneg _))
  have hδeq : δ*(2*(C+1))=gap := div_mul_cancel₀ _ (by positivity)
  have hsmall : C*δ<gap := by nlinarith
  dsimp only [gap] at hsmall
  linarith

end InvariantIsing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.InvariantIsing.finiteMagneticFunctional_real_profile_oai.{u_1, u_2} := @OAI.InvariantIsing.finiteMagneticFunctional_real_profile_oai.{u_1, u_2}
