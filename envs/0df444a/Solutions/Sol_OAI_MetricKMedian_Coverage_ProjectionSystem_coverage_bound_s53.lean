-- Prove2me | solution 1 for OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound_s53
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T07:07:45.655473+00:00
-- url     : https://prove2.me/submissions/467f0553-ba24-4a0b-a754-586fa63ece2f

import Mathlib
import Definitions.Def_OAIQ053K001
import Definitions.Def_OAIQ053K006

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Partition
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionSystem.mem_covered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Partitions
open Finset

variable {A B : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

theorem avoid_card (H : A → Finset B) :
    (avoid H).card = ∏ a, (Fintype.card B - (H a).card) := by
  have h := Fintype.card_congr (avoidEquiv H)
  rw [Fintype.card_pi] at h
  have hb (a : A) : Fintype.card {b : B // b ∉ H a} = Fintype.card B - (H a).card := by
    rw [Fintype.card_subtype_compl]
    simp
  simp only [hb] at h
  rw [Fintype.card_subtype] at h
  exact h

theorem hit_add_avoid (H : A → Finset B) :
    (hit H).card+(avoid H).card = Fintype.card B ^ Fintype.card A := by
  have hm : avoid H = (hit H)ᶜ := by
    ext w
    simp
  rw [hm,Finset.card_compl]
  have hn : (hit H).card ≤ Fintype.card (A → B) := Finset.card_le_univ _
  rw [Fintype.card_fun] at hn ⊢
  omega

theorem functional_avoid_card (H : A → Finset B) (h : ∀ a, (H a).card ≤ 1) :
    (avoid H).card = (Fintype.card B-1)^(active H).card *
      (Fintype.card B)^(Fintype.card A-(active H).card) := by
  rw [avoid_card]
  have hc (a : A) : Fintype.card B-(H a).card =
      if a ∈ active H then Fintype.card B-1 else Fintype.card B := by
    split_ifs with ha
    · have hp := Finset.card_pos.mpr ((mem_active H a).mp ha)
      have he : (H a).card = 1 := by have hh := h a; omega
      rw [he]
    · have hz : (H a).card = 0 := by
        exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp
          (fun hn => ha ((mem_active H a).mpr hn)))
      rw [hz,Nat.sub_zero]
  simp only [hc]
  have ht : univ.filter (fun a => a ∈ active H) = active H := by ext a; simp
  have hf : univ.filter (fun a => a ∉ active H) = (active H)ᶜ := by ext a; simp
  rw [Finset.prod_ite,ht,hf,Finset.prod_const,Finset.prod_const,Finset.card_compl]

theorem functional_hit_real (H : A → Finset B) (hB : 0 < Fintype.card B)
    (h : ∀ a, (H a).card ≤ 1) :
    ((hit H).card : ℝ) = (Fintype.card B : ℝ)^Fintype.card A *
      (1-(1-1/(Fintype.card B : ℝ))^(active H).card) := by
  have hh := hit_add_avoid H
  have hav := functional_avoid_card H h
  have hq : (active H).card ≤ Fintype.card A := Finset.card_le_univ _
  have hd : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hB
  have hscalar : (Fintype.card B:ℝ)*(1-1/(Fintype.card B:ℝ)) = Fintype.card B-1 := by
    field_simp
  have heq : (Fintype.card B:ℝ)^Fintype.card A *
      (1-1/(Fintype.card B:ℝ))^(active H).card =
      (Fintype.card B-1:ℝ)^(active H).card *
        (Fintype.card B:ℝ)^(Fintype.card A-(active H).card) := by
    rw [← hscalar,mul_pow]
    calc
      _ = (Fintype.card B:ℝ)^((active H).card+(Fintype.card A-(active H).card))*
          (1-1/(Fintype.card B:ℝ))^(active H).card := by rw [Nat.add_sub_of_le hq]
      _ = _ := by rw [pow_add]; ring
  have hr : ((hit H).card:ℝ) + ((avoid H).card:ℝ) =
      (Fintype.card B:ℝ)^Fintype.card A := by exact_mod_cast hh
  have hv : ((avoid H).card:ℝ) =
      (Fintype.card B-1:ℝ)^(active H).card *
        (Fintype.card B:ℝ)^(Fintype.card A-(active H).card) := by
    rw [hav]
    push_cast
    rw [Nat.cast_sub (by omega : 1 ≤ Fintype.card B)]
    norm_num
  rw [← heq] at hv
  nlinarith

end MetricKMedian.Coverage.Partitions

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_PartitionAverage
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionSystem.mem_covered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage.Partitions
open Finset

theorem pow_tangent (t : ℝ) (ht : 0 < t) (D q : ℕ) :
    t^D + ((q:ℝ)-D)*(t^D*Real.log t) ≤ t^q := by
  have h := mul_le_mul_of_nonneg_right
    (Real.add_one_le_exp (((q:ℝ)-D)*Real.log t)) (pow_nonneg ht.le D)
  have he : Real.exp (((q:ℝ)-D)*Real.log t)*t^D = t^q := by
    calc
      _ = Real.exp (((q:ℝ)-D)*Real.log t) * Real.exp ((D:ℝ)*Real.log t) := by
        rw [Real.exp_nat_mul,Real.exp_log ht]
      _ = Real.exp ((q:ℝ)*Real.log t) := by rw [← Real.exp_add]; congr 1; ring
      _ = _ := by rw [Real.exp_nat_mul,Real.exp_log ht]
  rw [he] at h
  nlinarith

theorem sum_pow_ge {V : Type} [Fintype V] (q : V → ℕ) (D : ℕ)
    (hq : ∑ v, q v ≤ D*Fintype.card V)
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    (Fintype.card V:ℝ)*t^D ≤ ∑ v, t^(q v) := by
  have hc : t^D*Real.log t ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.le D) (Real.log_nonpos ht.le ht1)
  have hqr : (∑ v, (q v:ℝ)) - (Fintype.card V:ℝ)*D ≤ 0 := by
    have h := (show (∑ v, (q v:ℝ)) ≤ (D:ℝ)*Fintype.card V by exact_mod_cast hq)
    nlinarith
  have hprod := mul_nonneg_of_nonpos_of_nonpos hqr hc
  have hsum := Finset.sum_le_sum (s := (univ : Finset V))
    (fun v _ => pow_tangent t ht D (q v))
  have he : (∑ v, (t^D+((q v:ℝ)-D)*(t^D*Real.log t))) =
      (Fintype.card V:ℝ)*t^D+
        ((∑ v, (q v:ℝ))-(Fintype.card V:ℝ)*D)*(t^D*Real.log t) := by
    rw [sum_add_distrib, ← sum_mul, sum_sub_distrib]
    simp only [sum_const, card_univ, nsmul_eq_mul]
  rw [he] at hsum
  linarith

theorem total_hit_bound {V A B : Type} [Fintype V] [Fintype A] [Fintype B]
    [DecidableEq V] [DecidableEq A] [DecidableEq B]
    (H : V → A → Finset B) (bad : Finset V)
    (hB : 1 < Fintype.card B)
    (hgood : ∀ v, v ∉ bad → ∀ a, (H v a).card ≤ 1)
    (hbudget : ∑ v, (active (H v)).card ≤ Fintype.card B * Fintype.card V) :
    (∑ v, ((hit (H v)).card:ℝ)) ≤
      (Fintype.card B:ℝ)^Fintype.card A *
        ((Fintype.card V:ℝ)*(1-(1-1/(Fintype.card B:ℝ))^Fintype.card B)+bad.card) := by
  let t : ℝ := 1-1/(Fintype.card B:ℝ)
  let M : ℝ := (Fintype.card B:ℝ)^Fintype.card A
  have hB1 : (1:ℝ) < Fintype.card B := by exact_mod_cast hB
  have hB0 : (0:ℝ) < Fintype.card B := by linarith
  have ht : 0 < t := by
    dsimp [t]
    exact sub_pos.mpr ((div_lt_one hB0).mpr hB1)
  have ht1 : t ≤ 1 := by dsimp [t]; have := one_div_nonneg.mpr hB0.le; linarith
  have hM : 0 ≤ M := pow_nonneg hB0.le _
  have hpoint (v : V) : ((hit (H v)).card:ℝ) ≤
      M*(1-t^(active (H v)).card)+(if v ∈ bad then M else 0) := by
    by_cases hv : v ∈ bad
    · rw [ite_eq_left hv]
      have hh : ((hit (H v)).card:ℝ) ≤ M := by
        have hcard := Finset.card_le_univ (hit (H v))
        rw [Fintype.card_fun] at hcard
        dsimp [M]
        exact_mod_cast hcard
      have hp : 0 ≤ M*(1-t^(active (H v)).card) :=
        mul_nonneg hM (sub_nonneg.mpr (pow_le_one₀ ht.le ht1))
      linarith
    · rw [ite_eq_right hv,add_zero]
      exact le_of_eq (functional_hit_real (H v) (by omega) (hgood v hv))
  have hsum := Finset.sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  have he : (∑ v, (M*(1-t^(active (H v)).card)+(if v ∈ bad then M else 0))) =
      M*((Fintype.card V:ℝ)-∑ v, t^(active (H v)).card)+(bad.card:ℝ)*M := by
    rw [sum_add_distrib,← mul_sum]
    simp only [sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one,
      Finset.sum_ite_mem_eq,Finset.sum_const]
  rw [he] at hsum
  have hpow := sum_pow_ge (fun v => (active (H v)).card) (Fintype.card B) hbudget ht ht1
  have hmul := mul_le_mul_of_nonneg_left (sub_le_sub_left hpow (Fintype.card V:ℝ)) hM
  change (∑ v, ((hit (H v)).card:ℝ)) ≤ M*((Fintype.card V:ℝ)*(1-t^Fintype.card B)+bad.card)
  nlinarith

end MetricKMedian.Coverage.Partitions

end Inline_PCPInherited

end OAI
end

section
-- module Solutions.OAIQ053_KM.KMedian_Hardness_Projection
attribute [-simp] _root_.OAI.MetricKMedian.Coverage.ProjectionInput.incident_equiv _root_.OAI.MetricKMedian.Coverage.ProjectionSystem.mem_agreement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section Inline_PCPInherited

namespace MetricKMedian.Coverage
open Finset

namespace ProjectionSystem
variable {U V I A B : Type} [Fintype U] [Fintype V] [Fintype I]
  [Fintype A] [Fintype B] [DecidableEq U] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B]
variable (G : ProjectionSystem U V I A B)

theorem labels_sum (S : Finset (U × A)) : ∑ u, (labels S u).card = S.card := by
  simp only [labels, card_eq_sum_ones, sum_filter]
  rw [← Fintype.sum_prod_type (fun p : U × A => if p ∈ S then (1 : ℕ) else 0)]
  simp

omit [Fintype U] in
theorem covered_card (S : Finset (U × A)) :
    (G.covered S).card = ∑ v, (Partitions.hit (G.parts S v)).card := by
  conv_lhs => rw [card_eq_sum_ones]
  rw [← sum_ite_mem_eq]
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro v _
  simp only [G.mem_covered, sum_boole, filter_mem_eq_inter, univ_inter, Nat.cast_id]

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem regular_sum {d : ℕ} (hreg : G.LeftRegular d) (f : U → ℕ) :
    (∑ v, ∑ i, f (G.neighbor v i)) = d * ∑ u, f u := by
  rw [← Fintype.sum_prod_type (fun p : V × I => f (G.neighbor p.1 p.2))]
  have he (p : V × I) : f (G.neighbor p.1 p.2) =
      ∑ u, if G.neighbor p.1 p.2 = u then f u else 0 := by simp
  simp_rw [he]
  rw [sum_comm, mul_sum]
  apply sum_congr rfl
  intro u _
  rw [← sum_filter]
  simp only [sum_const, nsmul_eq_mul, hreg u, Nat.cast_id]

omit [Fintype A] [Fintype B] [DecidableEq V] [DecidableEq I]
  [DecidableEq A] [DecidableEq B] in
theorem regular_degrees {d : ℕ} (hreg : G.LeftRegular d) :
    d * Fintype.card U = Fintype.card I * Fintype.card V := by
  have hh := G.regular_sum hreg (fun _ => 1)
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one, Nat.cast_id] at hh
  simpa only [mul_comm] using hh.symm

omit [Fintype U] [Fintype V] [DecidableEq V] [DecidableEq I] in
theorem active_le (S : Finset (U × A)) (v : V) :
    (Partitions.active (G.parts S v)).card ≤ ∑ i, (labels S (G.neighbor v i)).card := by
  let T : Finset (I × A) := univ.filter (fun p => (G.neighbor v p.1,p.2) ∈ S)
  have he : Partitions.active (G.parts S v) = T.image (fun p => G.project v p.1 p.2) := by
    ext b
    simp only [Partitions.mem_active, Finset.Nonempty, G.mem_parts, T,
      mem_image, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨i,a,ha,hb⟩
      exact ⟨(i,a),ha,hb⟩
    · rintro ⟨⟨i,a⟩,ha,hb⟩
      exact ⟨i,a,ha,hb⟩
  have hc : T.card = ∑ i, (labels S (G.neighbor v i)).card := by
    simp only [T, labels, card_eq_sum_ones, sum_filter]
    rw [Fintype.sum_prod_type]
  rw [he, ← hc]
  exact card_image_le

omit [DecidableEq V] [DecidableEq I] in
theorem active_budget {d : ℕ} (hreg : G.LeftRegular d)
    (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) :
    ∑ v, (Partitions.active (G.parts S v)).card ≤ Fintype.card I * Fintype.card V := by
  calc
    _ ≤ ∑ v, ∑ i, (labels S (G.neighbor v i)).card :=
      sum_le_sum (fun v _ => G.active_le S v)
    _ = d * S.card := by rw [G.regular_sum hreg (fun u => (labels S u).card), labels_sum]
    _ ≤ d * Fintype.card U := Nat.mul_le_mul_left d hS
    _ = _ := G.regular_degrees hreg

omit [Fintype U] [DecidableEq V] [DecidableEq I] in
theorem good_functional (S : Finset (U × A)) {v : V} (hv : v ∉ G.bad S) :
    ∀ b, (G.parts S v b).card ≤ 1 := by
  simpa only [bad,mem_filter,mem_univ,true_and,not_exists,not_lt] using hv

theorem coverage_bound_s53_oai {d : ℕ} (hreg : G.LeftRegular d)
    (hI : 1 < Fintype.card I) (S : Finset (U × A)) (hS : S.card ≤ Fintype.card U) :
    ((G.covered S).card:ℝ) ≤ (Fintype.card I:ℝ)^Fintype.card B *
      ((Fintype.card V:ℝ)*(1-(1-1/(Fintype.card I:ℝ))^Fintype.card I)+(G.bad S).card) := by
  rw [G.covered_card, Nat.cast_sum]
  exact Partitions.total_hit_bound (G.parts S) (G.bad S) hI
    (fun _ hv => G.good_functional S hv) (G.active_budget hreg S hS)

end ProjectionSystem
end MetricKMedian.Coverage

end Inline_PCPInherited

end OAI
end

theorem solution : type_of% @OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound_s53_oai := @OAI.MetricKMedian.Coverage.ProjectionSystem.coverage_bound_s53_oai
