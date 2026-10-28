-- Prove2me | solution 1 for OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s35
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T11:20:16.060723+00:00
-- url     : https://prove2.me/submissions/00181a70-ce86-410d-a00b-164e997ff7e2

import Mathlib
import Definitions.Def_OAIQ035K021
import Definitions.Def_OAIQ035K039
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_le_half_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_P_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_Analytic_m_nonneg_s35
import Theorems.Thm_OAI_MetricKMedian_FixedBatch_charge_bound_s35
import Theorems.Thm_OAI_MetricKMedian_SparseEnumeratedBatch_relevant_generator_estimate_s35

section
-- module Solutions.OAIQ035_KM.KMedian_Analysis_Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section

namespace MetricKMedian.Analytic

theorem A_le_one_add (x : ℝ) : A x ≤ 1 + x := by
  have hi : IntervalIntegrable (fun t : ℝ => 1 - Real.exp (-t * x))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hi' : IntervalIntegrable (fun t : ℝ => t * x) MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    fun_prop
  have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
    (a := (0 : ℝ)) (b := 1) (by norm_num) hi hi' (fun t _ => by
      have he := Real.add_one_le_exp (-t * x)
      nlinarith)
  rw [intervalIntegral.integral_mul_const] at h
  norm_num at h
  unfold A
  simp only [neg_mul]
  linarith

theorem A_le_two {x : ℝ} (hx : x ≤ 1) : A x ≤ 2 := by
  linarith [A_le_one_add x]

end MetricKMedian.Analytic


end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_MomentAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.Analytic

open MeasureTheory Set Filter
open scoped Topology Filter Interval

theorem coefficient_eq (x y : ℝ) : coefficient x y = 1+m x+B x*y := by
  unfold coefficient m B
  ring

theorem coefficient_ge_one {x y : ℝ} (hy : 0 ≤ y) : 1 ≤ coefficient x y := by
  rw [coefficient_eq]
  have hm := m_nonneg_s35 x
  have hB : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s35 x)
  nlinarith only [hm, mul_nonneg hB hy]

end MetricKMedian.Analytic
end
end

end OAI
end

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

theorem mass_nonneg {g : ℝ} (hg : 0 ≤ g) (S : Finset I) : 0 ≤ mass g S := by
  exact mul_nonneg hg (Nat.cast_nonneg _)

theorem cost_nonneg {g : ℝ} {d : I → ℝ} {S : Finset I} (hg : 0 ≤ g)
    (hd : ∀ i ∈ S, 0 ≤ d i) : 0 ≤ cost g d S := by
  exact Finset.sum_nonneg (fun i hi => mul_nonneg hg (hd i hi))

theorem mass_mono {g : ℝ} {S T : Finset I} (hg : 0 ≤ g) (hST : S ⊆ T) :
    mass g S ≤ mass g T := by
  apply mul_le_mul_of_nonneg_left _ hg
  exact_mod_cast Finset.card_le_card hST

theorem mass_sdiff [DecidableEq I] (g : ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    mass g (S \ T) = mass g S - mass g T := by
  unfold mass
  rw [Finset.card_sdiff_of_subset hTS, Nat.cast_sub (Finset.card_le_card hTS)]
  ring

theorem cost_sdiff [DecidableEq I] (g : ℝ) (d : I → ℝ) {S T : Finset I} (hTS : T ⊆ S) :
    cost g d (S \ T) = cost g d S - cost g d T := by
  exact Finset.sum_sdiff_eq_sub hTS

theorem B_nonneg (x : ℝ) : 0 ≤ B x := mul_nonneg (by norm_num) (P_nonneg_s35 x)

theorem removal_identity [DecidableEq I] (x g : ℝ) (d : I → ℝ) {S E : Finset I}
    (hES : E ⊆ S) (b b' : ℝ) :
    potential x g d (S \ E) b' - potential x g d S b =
      mass g E * b' - (1 + m x + B x * mass g S) * cost g d E -
      B x * mass g E * (cost g d S - cost g d E) +
      (1 - mass g S) * (b' - b) := by
  simp only [potential, mass_sdiff g hES, cost_sdiff g d hES]
  ring

theorem external_update_le [DecidableEq I] {x g b b' : ℝ} {d : I → ℝ} {S E : Finset I}
    (hES : E ⊆ S) (hy : mass g S ≤ 1) (hb : b' ≤ b) :
    potential x g d (S \ E) b' - potential x g d S b ≤
      mass g E * b' - (1 + m x + B x * mass g S) * cost g d E -
      B x * mass g E * (cost g d S - cost g d E) := by
  rw [removal_identity x g d hES b b']
  exact add_le_of_nonpos_right (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hy) (sub_nonpos.mpr hb))

theorem retained_subset (a dh : ℝ) (d : I → ℝ) (T : Finset I) : retained a dh d T ⊆ T :=
  Finset.filter_subset _ _

theorem retained_hinge_identity (a dh g : ℝ) (d : I → ℝ) (T : Finset I) :
    a * cost g d (retained a dh d T) + (1 - mass g (retained a dh d T)) * dh =
      dh - ∑ i ∈ T, g * max (dh - a * d i) 0 := by
  have hsum : (∑ i ∈ T, g * max (dh - a * d i) 0) =
      mass g (retained a dh d T) * dh - a * cost g d (retained a dh d T) := by
    rw [show (∑ i ∈ T, g * max (dh - a * d i) 0) =
        ∑ i ∈ retained a dh d T, g * (dh - a * d i) by
      rw [retained, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · rw [max_eq_left (sub_nonneg.mpr h.le)]
      · rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt h)), mul_zero]]
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
      cost, mass, ← Finset.mul_sum]
    ring
  rw [hsum]
  ring

theorem internal_update_le {x g b' dh : ℝ} {d : I → ℝ} {S T : Finset I}
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) (hTS : T ⊆ S)
    (hy : mass g S ≤ 1) (hb : b' ≤ dh) :
    let a := 1 + m x + B x * mass g S
    potential x g d (retained a dh d T) b' ≤
      dh - ∑ i ∈ T, g * max (dh - a * d i) 0 := by
  dsimp only
  let a := 1 + m x + B x * mass g S
  let U := retained a dh d T
  have hUS : U ⊆ S := (retained_subset a dh d T).trans hTS
  have hmass : mass g U ≤ mass g S := mass_mono hg hUS
  have hcost : 0 ≤ cost g d U := cost_nonneg hg (fun i hi => hd i (hUS hi))
  have hcoeff : 1 + m x + B x * mass g U ≤ a := by
    dsimp [a]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hmass (B_nonneg x)) _
  have hcap := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr (hmass.trans hy))
  have hc := mul_le_mul_of_nonneg_right hcoeff hcost
  have hbound : potential x g d U b' ≤ a * cost g d U + (1 - mass g U) * dh :=
    add_le_add hc hcap
  exact hbound.trans_eq (retained_hinge_identity a dh g d T)

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_FixedBatchTransition
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic

variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem mem_relevant (D : Actions I E) (S : Finset I) (e : E) :
    e ∈ relevant D S ↔ (e ∈ D.ordinary ∧ D.source e ∈ S) ∨ (S ∩ D.erase e).Nonempty := by
  simp only [relevant, mem_filter, mem_univ, true_and]

omit [Fintype E] in
 theorem physical_subset (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A ⊆ S := sdiff_subset

 theorem nextAlive_subset (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) : nextAlive D x g d S A ⊆ S := by
  unfold nextAlive
  split_ifs
  · exact (retained_subset _ _ _ _).trans (physical_subset D S A)
  · exact physical_subset D S A

theorem physical_restrict (D : Actions I E) (S : Finset I) (A : Finset E) :
    physical D S A = physical D S (A ∩ relevant D S) := by
  ext i
  simp only [physical, mem_sdiff, mem_biUnion]
  constructor
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    exact hnot ⟨e, (mem_inter.mp he).1, hie⟩
  · rintro ⟨hi, hnot⟩
    refine ⟨hi, ?_⟩
    rintro ⟨e, he, hie⟩
    have hrel : e ∈ relevant D S := (mem_relevant D S e).mpr (Or.inr ⟨i, mem_inter.mpr ⟨hi, hie⟩⟩)
    exact hnot ⟨e, mem_inter.mpr ⟨he, hrel⟩, hie⟩

 theorem nextAlive_zero (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (ha : A ∩ relevant D S=∅) :
    nextAlive D x g d S A=S := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_empty]
  simp only [nextAlive, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, biUnion_empty, sdiff_empty]

 theorem nextAlive_one_external (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (e : E) (ha : A ∩ relevant D S={e})
    (he : ¬(e ∈ D.ordinary ∧ D.source e ∈ S)) :
    nextAlive D x g d S A=S \ D.erase e := by
  have hi : internal D S A=∅ := by simp only [internal, ha, filter_singleton, he, ite_false]
  simp only [nextAlive, hi, Finset.not_nonempty_empty, dite_false]
  rw [physical_restrict, ha]
  simp only [physical, singleton_biUnion]

 theorem nextAlive_one_internal (D : Actions I E) (x g : ℝ) (d : I → ℝ)
    (S : Finset I) (A : Finset E) (e : E) (ha : A ∩ relevant D S={e})
    (he : e ∈ D.ordinary ∧ D.source e ∈ S) :
    nextAlive D x g d S A=
      retained (coefficient x (mass g S)) (d (D.source e)) d (S \ D.erase e) := by
  have hi : internal D S A={e} := by simp [internal, ha, he]
  have hne : (internal D S A).Nonempty := by rw [hi]; exact singleton_nonempty _
  rw [nextAlive, dite_eq_left hne]
  have hchoose : hne.choose=e := by simpa only [hi, mem_singleton] using hne.choose_spec
  rw [hchoose, physical_restrict, ha]
  simp only [physical, singleton_biUnion]

omit [Fintype E] in
 theorem nextCap_le_force (D : Actions I E) (d : I → ℝ) (bForce : ℝ) (A : Finset E) :
    nextCap D d bForce A ≤ bForce := (fold_min_le _).mpr (Or.inl le_rfl)

omit [Fintype E] in
 theorem nextCap_nonneg (D : Actions I E) (d : I → ℝ) {bForce : ℝ} (A : Finset E)
    (hb : 0 ≤ bForce) (hd : ∀ e ∈ A ∩ D.ordinary, 0 ≤ d (D.source e)) :
    0 ≤ nextCap D d bForce A := (le_fold_min _).mpr ⟨hb, hd⟩

omit [Fintype E] in
 theorem nextCap_le_selected (D : Actions I E) (d : I → ℝ) {bForce : ℝ} (A : Finset E)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e))
    {e : E} (he : e ∈ A) : nextCap D d bForce A ≤ d (D.source e) := by
  by_cases ho : e ∈ D.ordinary
  · exact (fold_min_le _).mpr (Or.inr ⟨e, mem_inter.mpr ⟨he, ho⟩, le_rfl⟩)
  · exact (nextCap_le_force D d bForce A).trans (hheavy e ho)

 theorem frozen_zero (D : Actions I E) {x g b bForce : ℝ} (d : I → ℝ)
    (S : Finset I) (A : Finset E) (hy : mass g S ≤ 1) (hb : bForce ≤ b)
    (ha : A ∩ relevant D S=∅) :
    potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b ≤ 0 := by
  rw [nextAlive_zero D x g d S A ha]
  have hcap := (nextCap_le_force D d bForce A).trans hb
  have hm := mul_le_mul_of_nonneg_left hcap (sub_nonneg.mpr hy)
  unfold potential
  linarith only [hm]

theorem frozen_one (D : Actions I E) {x g b bForce : ℝ} (d : I → ℝ)
    (S : Finset I) (A : Finset E) (e : E)
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, 0 ≤ d i) (hy : mass g S ≤ 1) (hb : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e))
    (ha : A ∩ relevant D S={e}) :
    potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b ≤
      charge D x g b d S e := by
  have heA : e ∈ A := inter_subset_left (show e ∈ A ∩ relevant D S by rw [ha]; exact mem_singleton_self _)
  have hcap := nextCap_le_selected D d A hheavy heA
  by_cases he : e ∈ D.ordinary ∧ D.source e ∈ S
  · rw [charge, ite_eq_left he, nextAlive_one_internal D x g d S A e ha he]
    have hc := internal_update_le (x := x) hg hd (sdiff_subset : S \ D.erase e ⊆ S) hy hcap
    rw [← coefficient_eq] at hc
    linarith only [hc]
  · rw [charge, ite_eq_right he, nextAlive_one_external D x g d S A e ha he]
    have hsub : S ∩ D.erase e ⊆ S := inter_subset_left
    have h := external_update_le (x := x) (g := g) (d := d) hsub hy
      ((nextCap_le_force D d bForce A).trans hb)
    have hsd : S \ (S ∩ D.erase e)=S \ D.erase e := by ext i; simp only [mem_sdiff, mem_inter]; tauto
    rw [hsd, ← coefficient_eq] at h
    have hm := mul_le_mul_of_nonneg_left (le_min ((nextCap_le_force D d bForce A).trans hb) hcap)
      (mass_nonneg hg (S ∩ D.erase e))
    linarith only [h, hm]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Geometry_PotentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.PhysicalPotential
open Analytic Finset

variable {I : Type*}

theorem B_le_one {x : ℝ} (hx : 0 ≤ x) : B x ≤ 1 := by
  have h := P_le_half_s35 hx
  unfold B
  linarith only [h]

theorem m_le_one {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : m x ≤ 1 := by
  have hA := A_le_two hx1
  have hBx := mul_nonneg (B_nonneg x) hx0
  unfold m
  unfold B at hBx
  linarith only [hA, hBx]

theorem coefficient_bounds {x y : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1) : 1 ≤ coefficient x y ∧ coefficient x y ≤ 3 := by
  refine ⟨coefficient_ge_one hy0, ?_⟩
  rw [coefficient_eq]
  have hm := m_le_one hx0 hx1
  have hB := (mul_le_of_le_one_left hy0 (B_le_one hx0)).trans hy1
  linarith only [hm, hB]

theorem cost_le_mass_mul {g R : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hd : ∀ i ∈ S, d i ≤ R) : cost g d S ≤ mass g S*R := by
  have h := sum_le_sum (fun i (hi : i ∈ S) => mul_le_mul_of_nonneg_left (hd i hi) hg)
  simpa only [cost, mass, sum_const, nsmul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using h

theorem cost_le_radius {g R : ℝ} {d : I → ℝ} {S : Finset I}
    (hg : 0 ≤ g) (hR : 0 ≤ R) (hd : ∀ i ∈ S, d i ≤ R) (hy : mass g S ≤ 1) :
    cost g d S ≤ R := by
  exact (cost_le_mass_mul hg hd).trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hy hR)

theorem potential_bounds {x g R b : ℝ} {d : I → ℝ} {S : Finset I}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i ∈ S, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R) :
    0 ≤ potential x g d S b ∧ potential x g d S b ≤ 8*R := by
  have hy0 := mass_nonneg hg S
  have hV0 := cost_nonneg hg hd0
  have hVR := cost_le_radius hg hR hdR hy
  have ha := coefficient_bounds hx0 hx1 hy0 hy
  have hcap0 := mul_nonneg (sub_nonneg.mpr hy) hb0
  have hcap := mul_le_mul_of_nonneg_right (show 1-mass g S ≤ 1 by linarith only [hy0]) hb0
  have hc := mul_le_mul ha.2 hVR hV0 (by norm_num : (0:ℝ) ≤ 3)
  rw [potential, ← coefficient_eq]
  constructor
  · exact add_nonneg (mul_nonneg (by linarith only [ha.1]) hV0) hcap0
  · nlinarith only [hc, hcap, hbR]

end MetricKMedian.PhysicalPotential
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Process_FrozenBatchBound
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.FixedBatch
open Finset PhysicalPotential Analytic
variable {I E : Type*} [DecidableEq I] [DecidableEq E] [Fintype E]

 theorem frozen_change_bound (D : Actions I E) {x g R b bForce : ℝ} (d : I → ℝ)
    (S : Finset I) (A : Finset E)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b) :
    potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b ≤ 8*R := by
  have hsub := nextAlive_subset D x g d S A
  have hnew := potential_bounds hx0 hx1 hg hR (fun i _ => hd0 i)
    (fun i hi => hdR i (hsub hi)) ((mass_mono hg hsub).trans hy)
    (nextCap_nonneg D d A hbf0 (fun e _ => hd0 _))
    ((nextCap_le_force D d bForce A).trans (hbf.trans hbR))
  have hold := potential_bounds hx0 hx1 hg hR (fun i _ => hd0 i) hdR hy hb0 hbR
  linarith only [hnew.2, hold.1]

end MetricKMedian.FixedBatch
end
end

end OAI
end

section
-- module Solutions.OAIQ035_KM.KMedian_Sparse_SparseEnumeratedFrozen
attribute [-instance] _root_.OAI.MetricKMedian.FixedBatch.instDecidableEqHeavyAction _root_.OAI.MetricKMedian.FixedBatch.instFintypeHeavyAction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
namespace MetricKMedian.SparseEnumeratedFixedBatch
open Finset PhysicalPotential Analytic FixedBatch
variable {I E : Type} [DecidableEq I] [DecidableEq E] [Fintype E] {n : ℕ}

theorem expected_frozen_bound_s35_oai (enum : Fin n ≃ E) (D : Actions I E) (Z : Finset E) (C : E → Finset E)
    (p : ℚ) (q : E → ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (hq0 : ∀ e, 0 ≤ q e ∧ q e ≤ 1)
    {φ Q : ℝ} {N : ℕ} (hφ : 0 ≤ φ) (hQ : 0 ≤ Q)
    (hpQ : (p:ℝ) ≤ Q) (hqQ : ∀ e, (q e:ℝ) ≤ Q)
    (hq : ∀ e, (p:ℝ) ≤ q e ∧ (q e:ℝ) ≤ (1+φ)*p)
    (hC : ∀ e, (C e).card ≤ N) (hself : ∀ e, e ∉ C e)
    {x g R b bForce : ℝ} (d : I → ℝ) (S : Finset I)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hg : 0 ≤ g) (hR : 0 ≤ R)
    (hd0 : ∀ i, 0 ≤ d i) (hdR : ∀ i ∈ S, d i ≤ R)
    (hy : mass g S ≤ 1) (hb0 : 0 ≤ b) (hbR : b ≤ 5*R)
    (hbf0 : 0 ≤ bForce) (hbf : bForce ≤ b)
    (hheavy : ∀ e, e ∉ D.ordinary → bForce ≤ d (D.source e)) :
    (SparseEnumeratedBatch.law enum Z C p q hp hq0).real.expect
      (fun A => potential x g d (nextAlive D x g d S A) (nextCap D d bForce A)-potential x g d S b) ≤
      ((p:ℝ)/2)*(∑ e ∈ relevant D S, charge D x g b d S e)+
        ((relevant D S).card:ℝ)*(8*R)*((N:ℝ)*(p:ℝ)^2/2+φ*(p:ℝ)/2)+
        2*(8*R)*((univ : Finset (relevant D S)).offDiag.card:ℝ)*Q^2 := by
  apply SparseEnumeratedBatch.relevant_generator_estimate_s35 enum Z (relevant D S) C p q
    (charge D x g b d S) hp hq0 hφ (by positivity) hQ hpQ hqQ hq hC hself
  · exact fun e _ => charge_bound_s35 D d S hx0 hx1 hg hR hd0 hdR hy hb0 hbR e
  · exact fun A => frozen_change_bound D d S A hx0 hx1 hg hR hd0 hdR hy hb0 hbR hbf0 hbf
  · exact fun A ha => frozen_zero D d S A hy hbf ha
  · exact fun A e ha => frozen_one D d S A e hg (fun i _ => hd0 i) hy hbf hheavy ha

end MetricKMedian.SparseEnumeratedFixedBatch
end
end

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s35_oai := @OAI.MetricKMedian.SparseEnumeratedFixedBatch.expected_frozen_bound_s35_oai
