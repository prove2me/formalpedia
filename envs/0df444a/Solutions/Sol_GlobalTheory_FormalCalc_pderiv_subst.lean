-- Prove2me | solution 1 for GlobalTheory.FormalCalc.pderiv_subst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:31:38.313193+00:00
-- url     : https://prove2.me/submissions/b747ba96-a1c9-42dd-ab0b-f4783998c015

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NatCastMulCoeffOfPderivEq
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_zero__b9c8f67e64a1
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_C__c5547c7a475b
import Theorems.Thm_GlobalTheory_FormalCalc_continuous_pderiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FormalCalc
open MvPowerSeries Finsupp
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
open MvPowerSeries.WithPiTopology
namespace GlobalTheory.FormalCalc
theorem _root_.solution [Fintype σ] {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (f : MvPowerSeries σ R) (j : τ) :
    pderiv S j (subst a f) = ∑ i, subst a (pderiv R i f) * pderiv S j (a i) := by
  classical
  letI : UniformSpace R := ⊥
  letI : UniformSpace S := ⊥
  have hc := continuous_subst (R := R) ha
  refine congr_fun (DenseRange.equalizer (denseRange_toMvPowerSeries (σ := σ) (R := R))
    (g := fun f => pderiv S j (subst a f))
    (h := fun f => ∑ i, subst a (pderiv R i f) * pderiv S j (a i))
    ((continuous_pderiv j).comp hc)
    (continuous_finset_sum _ fun i _ => (hc.comp (continuous_pderiv i)).mul continuous_const)
    ?_) f
  funext p
  simp only [Function.comp_apply]
  induction p using MvPolynomial.induction_on with
  | C r =>
    simp [MvPolynomial.coe_C, pderiv_C, subst_C' ha, subst_zero' ha]
  | add p q hp hq =>
    simp only [MvPolynomial.coe_add, subst_add ha, map_add, hp, hq, add_mul,
      Finset.sum_add_distrib]
  | mul_X p n hp =>
    simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, subst_mul ha, Derivation.leibniz, hp,
      smul_eq_mul, subst_add ha, subst_X ha, add_mul, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · rw [Finset.sum_eq_single n]
      · simp [subst_one' ha]
      · intro b _ hb
        simp [pderiv_X_of_ne (Ne.symm hb), subst_zero' ha]
      · simp
    · exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory.FormalCalc
