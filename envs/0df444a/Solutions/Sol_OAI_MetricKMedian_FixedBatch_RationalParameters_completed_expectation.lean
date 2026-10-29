-- Prove2me | solution 1 for OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T08:46:20.887297+00:00
-- url     : https://prove2.me/submissions/413aa6d9-91a6-4ee1-8cab-85518b803739

import Mathlib
import Definitions.Def_OAIQ035K044
import Definitions.Def_OAIQ035K045
import Definitions.Def_OAIQ035K047
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_completion
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_drift
import Theorems.Thm_OAI_MetricKMedian_RationalPhysicalKernel_histories_survival

section
-- module Solutions.OAIQ035_KM.KMedian_Process_PhysicalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential

open Analytic

variable {I : Type*}

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

theorem point_cost_le {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) {i : I} (hi : i ∈ S) : g * d i ≤ cost g d S := by
  exact Finset.single_le_sum (fun j hj => mul_nonneg hg (hd j hj)) hi

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Probability_FiniteProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedian.FiniteLaw
open Finset
variable {Ω : Type*} [Fintype Ω]

 theorem decay_exp {h : ℝ} (hh : h ≤ 2) (n : ℕ) :
    (1-h/2)^n ≤ Real.exp (-(n:ℝ)*h/2) := by
  have hbase : 1-h/2 ≤ Real.exp (-h/2) := by
    simpa only [sub_eq_add_neg, neg_div, add_comm] using Real.add_one_le_exp (-h/2)
  have hp := pow_le_pow_left₀ (show (0:ℝ) ≤ 1-h/2 by linarith only [hh]) hbase n
  calc
    _ ≤ (Real.exp (-h/2))^n := hp
    _ = _ := by rw [← Real.exp_nat_mul]; congr 1; ring

end MetricKMedian.FiniteLaw

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalHistoryCompletion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                 
section
namespace MetricKMedian.RationalPhysicalKernel
open Finset PhysicalPotential CopyState Completion.Rational
variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j Δ : ℕ}

theorem histories_completed_expectation (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (g β p φ : ℚ) (P : ℕ → ℚ) (hp : 0 ≤ p) (hφ : 0 ≤ φ) (hupper : (1+φ)*p ≤ 1)
    (A : Finset (Copy (F := F) Δ)) (B : Fin j → Finset (Copy (F := F) Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty) (T : ℕ)
    {h ζ : ℝ} (hprob : (p:ℝ)=2*h*(g:ℝ))
    (hg : 0 < (g:ℝ)) (hg1 : (g:ℝ)≤1) (hunit : (g:ℝ)*(Δ:ℝ)=1)
    (hP : ∀ t<T, 0<(P t:ℝ)) (hP1 : ∀ t<T, (P t:ℝ)≤1/2)
    (hA : 1 ≤ mass (g:ℝ) A) (hh0 : 0 ≤ h) (hh1 : h≤1) (hφ1 : (φ:ℝ)≤1)
    (hsmall : (16*((Δ^2+Δ:ℕ):ℝ)+10)*h ≤ savingsFraction (g:ℝ))
    (hsurv : (2*h*(g:ℝ))*(2*((Δ^2:ℕ):ℝ)+8*(Δ:ℝ)) ≤ 1)
    (hζ0 : 0 ≤ ζ) (hζ1 : ζ<1/4)
    (he : ∀ t<T, |(P t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*h))|≤ζ)
    (hBA : ∀ c, B c⊆A) (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1≤R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    (histories d₀ g β p φ P hp hφ hupper A T).expectation
      (fun z => (score d (completed d R B hB g β z):ℝ)) ≤
    ∑ c, ((1+2/Real.exp 1)*PhysicalPotential.cost (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (B c)+
      (T:ℝ)*(h*((g:ℝ)+12*ζ)*PhysicalPotential.cost (g:ℝ) (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (B c)+
        FixedBatch.batchConstant Δ*h*((φ:ℝ)+h)*(R c:ℝ))+5*(R c:ℝ)*(1-h/2)^T) := by
  let μ := histories d₀ g β p φ P hp hφ hupper A T
  let x := fun t : ℕ => Real.exp (-(t:ℝ)*h)
  let L := fun c z => replay g β x (fun (_ : Unit) f => dist (client c) (location f)) (fun _ => B c) z ()
  let V := fun c z => potential (x T) (g:ℝ)
    (fun i : Copy (F := F) Δ => dist (client c) (location i.1)) (L c z)
    (GroupCap.cap (R c:ℝ) (fun f => dist (client c) (location f)) (integral Δ z.1.1))
  have hc : μ.expectation (fun z => (score d (completed d R B hB g β z):ℝ)) ≤
      μ.expectation (fun z => ∑ c, (V c z+5*(R c:ℝ)*mass (g:ℝ) (L c z))) := by
    apply μ.realIndex.expect_mono
    intro a
    exact (histories_completion d₀ d location client hd₀ hd g β p φ P hp hφ hupper A B R hB T x
      hg hunit hP hP1 hA hBA hR hm hdR a).2.2
  apply hc.trans
  rw [SparseIntegerLaw.expectation,FiniteLaw.expect_sum]
  apply sum_le_sum
  intro c _
  rw [FiniteLaw.expect_add,FiniteLaw.expect_mul]
  have hv := histories_drift d₀ location (client c) hd₀ g β p φ P hp hφ hupper A (B c) T
    hprob hg hg1 hunit hP hP1 hA hh0 hh1 hφ1 hsmall hζ0 hζ1 he (hBA c) (hm c)
    (R := (R c:ℝ)) (by exact_mod_cast hR c) (fun i hi => by rw [hd]; exact_mod_cast hdR c i hi) (by
      obtain ⟨i,hi,hiR⟩ := hatt c
      refine ⟨i,hi,?_⟩
      rw [hd]
      exact_mod_cast hiR)
  have hs := histories_survival d₀ location hd₀ g β p φ P hp hφ hupper A (B c) T x
    (fun f => dist (client c) (location f)) hprob hg hunit hP hP1 hh0 hh1 hφ1 hA hsurv (hBA c)
  rw [hm c,mul_one] at hs
  exact add_le_add hv (mul_le_mul_of_nonneg_left hs (by exact_mod_cast mul_nonneg (by norm_num : (0:ℚ)≤5) (hR c)))

end MetricKMedian.RationalPhysicalKernel
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_RationalParameterizedHistory
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


                                                    
section
namespace MetricKMedian.FixedBatch.RationalParameters
open Finset PhysicalPotential CopyState RationalPhysicalKernel Completion.Rational
variable {τ : ℝ} (q : RationalParameters τ)

theorem taperAt_le (t : ℕ) : (q.taperAt t:ℝ) ≤ 1/2 := by
  unfold taperAt
  split_ifs with ht
  · exact q.taper_le _
  · norm_num

theorem taperAt_error (t : ℕ) (ht : t<q.T) :
    |(q.taperAt t:ℝ)-Analytic.P (Real.exp (-(t:ℝ)*(q.h:ℝ)))| ≤ (q.ζ:ℝ) := by
  simpa only [taperAt,dite_eq_left ht] using q.taper_error ⟨t,ht⟩

variable {F X : Type} [LinearOrder F] [Fintype F] [PseudoMetricSpace X] {j : ℕ}

theorem completed_expectation_oai (d₀ : F → F → ℚ) (d : Fin j → F → ℚ)
    (location : F → X) (client : Fin j → X)
    (hd₀ : ∀ f a, dist (location f) (location a)=(d₀ f a:ℝ))
    (hd : ∀ c f, dist (client c) (location f)=(d c f:ℝ))
    (A : Finset (Copy (F := F) q.Δ)) (B : Fin j → Finset (Copy (F := F) q.Δ))
    (R : Fin j → ℚ) (hB : ∀ c, (B c).Nonempty)
    (hA : 1 ≤ mass (q.g:ℝ) A) (hBA : ∀ c, B c ⊆ A)
    (hR : ∀ c, 0 ≤ R c) (hm : ∀ c, mass (q.g:ℝ) (B c)=1)
    (hdR : ∀ c i, i∈B c → d c i.1 ≤ R c) (hatt : ∀ c, ∃ i∈B c, R c=d c i.1) :
    (q.tree d₀ A).expectation (fun z => (score d (completed d R B hB q.g q.β z):ℝ)) ≤
      (1+2/Real.exp 1+τ)*(∑ c, PhysicalPotential.cost (q.g:ℝ)
        (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)) := by
  have hE := histories_completed_expectation d₀ d location client hd₀ hd q.g q.β q.probabilityQ
    q.φ q.taperAt q.probabilityQ_pos.le (by exact_mod_cast q.φpos.le) q.probabilityQ_le A B R hB
    q.T (by simp [probabilityQ]) q.gpos q.gle q.unit
    (fun t _ => q.taperAt_pos t) (fun t _ => q.taperAt_le t) hA q.hpos.le q.hle q.φle q.small
    q.survival q.ζpos.le q.ζle q.taperAt_error hBA hR hm hdR hatt
  apply hE.trans
  rw [mul_sum]
  apply sum_le_sum
  intro c _
  let v := PhysicalPotential.cost (q.g:ℝ)
    (fun i : Copy (F := F) q.Δ => dist (client c) (location i.1)) (B c)
  have hv : 0 ≤ v := cost_nonneg q.gpos.le (fun _ _ => dist_nonneg)
  have hr : (R c:ℝ) ≤ (q.Δ:ℝ)*v := by
    obtain ⟨i,hi,he⟩ := hatt c
    have hp := point_cost_le q.gpos.le (fun (i' : Copy (F := F) q.Δ) _ =>
      (dist_nonneg : 0 ≤ dist (client c) (location i'.1))) hi
    rw [hd,← he] at hp
    have hmul := mul_le_mul_of_nonneg_left hp (show (0:ℝ) ≤ q.Δ by positivity)
    have hu : (q.Δ:ℝ)*(q.g:ℝ)=1 := by rw [mul_comm]; exact q.unit
    simpa only [← mul_assoc,hu,one_mul] using hmul
  have hdec := FiniteLaw.decay_exp (show (q.h:ℝ) ≤ 2 by linarith only [q.hle]) q.T
  have hpow := mul_le_mul_of_nonneg_left hdec
    (show 0 ≤ 5*(R c:ℝ) by exact_mod_cast mul_nonneg (by norm_num : (0:ℚ) ≤ 5) (hR c))
  have hrad := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ 5*Real.exp (-(q.T:ℝ)*(q.h:ℝ)/2) by positivity)
  have hC : 0 ≤ batchConstant q.Δ := by unfold batchConstant; positivity
  have hh := q.hpos.le
  have hφ := q.φpos.le
  have hbatch := mul_le_mul_of_nonneg_left hr
    (show 0 ≤ (q.T:ℝ)*batchConstant q.Δ*(q.h:ℝ)*((q.φ:ℝ)+(q.h:ℝ)) by positivity)
  have herr := mul_le_mul_of_nonneg_right q.error hv
  change (1+2/Real.exp 1)*v+(q.T:ℝ)*((q.h:ℝ)*((q.g:ℝ)+12*(q.ζ:ℝ))*v+
    batchConstant q.Δ*(q.h:ℝ)*((q.φ:ℝ)+(q.h:ℝ))*(R c:ℝ))+
      5*(R c:ℝ)*(1-(q.h:ℝ)/2)^q.T ≤ (1+2/Real.exp 1+τ)*v
  nlinarith only [hpow,hrad,hbatch,herr]

end MetricKMedian.FixedBatch.RationalParameters
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_oai := @OAI.MetricKMedian.FixedBatch.RationalParameters.completed_expectation_oai
