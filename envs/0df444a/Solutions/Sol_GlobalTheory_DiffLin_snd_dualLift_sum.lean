-- Prove2me | solution 1 for GlobalTheory.DiffLin.snd_dualLift_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:22:08.463657+00:00
-- url     : https://prove2.me/submissions/48ef7a82-689f-4fb5-87a2-8044b2bd4770

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsDiffSumSmulOfIsLieComb
import Theorems.Thm_GlobalTheory_DiffLin_fst_dualLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.DiffLin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.DiffLin
theorem _root_.solution {k : ℕ} (c : Fin k → R) (t : Fin k → Fin n → R) (y : JetR R (Fin n) 1) :
    (dualLift (∑ i, c i • t i) y).snd = ∑ i, c i * (dualLift (t i) y).snd := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (MvPolynomial.C a))).snd = 0 := fun s => by
      have := (dualLift s).commutes a
      exact (congrArg TrivSqZeroExt.snd this).trans rfl
    simp only [h, mul_zero, Finset.sum_const_zero]
  | add p q hp hq =>
    simp only [map_add, TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    have h : ∀ s : Fin n → R,
        (dualLift s (Ideal.Quotient.mk _ (p * MvPolynomial.X j))).snd =
          jetAug R (Fin n) 1 (Ideal.Quotient.mk _ p) * s j := fun s => by
      rw [map_mul, map_mul, dualLift_zR, DualNumber.snd_mul, fst_dualLift]
      simp
    simp only [h, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.DiffLin
