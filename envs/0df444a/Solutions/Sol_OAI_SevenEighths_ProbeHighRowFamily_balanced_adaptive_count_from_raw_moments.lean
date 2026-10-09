-- Prove2me | solution 1 for OAI.SevenEighths.ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T03:59:48.749652+00:00
-- url     : https://prove2.me/submissions/cb65bd89-b97a-458e-aef3-f40366e89b22

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_HeckeSevenEighths
import Definitions.Def_OAIHecke78B027
import Theorems.Thm_OAI_SevenEighths_HeckeDetectorRawFiber_Fiber_inverse_marked_count
import Theorems.Thm_OAI_SevenEighths_HeckeDetectorRawFiber_Fiber_plain_marked_count
import Theorems.Thm_OAI_SevenEighths_HeckeDetectorRawFiber_Fiber_plain_unmarked_count
import Theorems.Thm_OAI_SevenEighths_HeckeInverseAmplification_no_slot_rowwise_endpoint

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Endpoint
namespace OAI

namespace SevenEighths.Endpoint

noncomputable section

theorem denominator_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ denominator y ∧ denominator y ≤ 3 := by
  dsimp [denominator]
  constructor <;> linarith

theorem primeWeight_bounds {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    7 / 9 ≤ primeWeight y ∧ primeWeight y ≤ 2 := by
  have hs := sq_nonneg y
  have ht := mul_nonneg hy0 (sub_nonneg.mpr hy1)
  dsimp [primeWeight]
  constructor <;> nlinarith

theorem balanceDenominator_bounds {δ y : ℝ}
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    35 / 54 ≤ balanceDenominator δ y ∧ balanceDenominator δ y ≤ 5 / 2 := by
  obtain ⟨hd0, hd1⟩ := denominator_bounds hy0 hy1
  obtain ⟨hp0, hp1⟩ := primeWeight_bounds hy0 hy1
  have ha : 0 ≤ 5 / 6 - δ := sub_nonneg.mpr hδ1
  have hl1 := mul_le_mul_of_nonneg_left hd0 ha
  have hl2 := mul_le_mul_of_nonneg_left hp0 hδ0
  have hu1 := mul_le_mul_of_nonneg_left hd1 ha
  have hu2 := mul_le_mul_of_nonneg_left (le_trans hp1 (by norm_num : (2 : ℝ) ≤ 3)) hδ0
  dsimp [balanceDenominator]
  constructor <;> nlinarith

end

end SevenEighths.Endpoint

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.Dyadic
namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set
namespace SevenEighths.HeckeDyadic
open HeckeFamily

theorem norm_pos (I : NonzeroIdeal) : 0 < norm I := by
  unfold norm
  exact_mod_cast Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)

end SevenEighths.HeckeDyadic

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorDyadicActual
namespace OAI

noncomputable section

open scoped Classical ContDiff
open Set
namespace SevenEighths.HeckeDetectorDyadicActual
open HeckeFamily HeckeDyadic HeckeDetectorDyadicProfiles HeckeDetectorProfiles

lemma inverse_profile_smooth (Dstar D : ℝ) :
    ContDiff ℝ ∞ (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D) := by
  unfold HeckeDetectorDyadicBridge.inverseProfile
  have hv : ContDiff ℝ ∞ (fun x : ℝ => cutoff (D*x/Dstar)) := (cutoff.smooth ⊤).comp (by fun_prop)
  exact hv.mul positiveAnnular_smooth

lemma inverse_profile_support (Dstar D : ℝ) :
    Function.support (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular Dstar D)⊆Icc (1/4) (9/4) := by
  intro x hx
  exact positiveAnnular_support ((mul_ne_zero_iff.mp hx).2)

end SevenEighths.HeckeDetectorDyadicActual

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCount
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRowCount
open HeckeFamily HeckeDyadic

lemma card_of_energy {α : Type*} (rows : Finset α) (F : α→ℂ)
    (U p b C : ℝ) (hU : 0<U)
    (hspike : ∀ u∈rows, U^p≤‖F u‖^2)
    (henergy : ∑ u∈rows, ‖F u‖^2≤C*U^b) :
    (rows.card : ℝ)≤C*U^(b-p) := by
  have hs : (rows.card : ℝ)*U^p≤C*U^b := by
    calc
      _ = ∑ u∈rows, U^p := by simp
      _ ≤ ∑ u∈rows, ‖F u‖^2 := Finset.sum_le_sum hspike
      _ ≤ _ := henergy
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hU p)).mp
  calc
    _ ≤ C*U^b := hs
    _ = (C*U^(b-p))*U^p := by rw [mul_assoc,←Real.rpow_add hU]; congr 2; ring

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountCrossing
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

lemma denominator_lower {x : ℝ} (hx : x≤1/2) : 37/18≤denominator x := by
  unfold denominator
  linarith

theorem crossing_bounds {x t : ℝ} (hx : 0≤x) (hx' : x≤1/2)
    (ht : 1≤t) (ht' : t≤3/2) :
    23/37≤ crossing x t ∧ crossing x t≤1 ∧
      1/3≤t-crossing x t ∧ t-crossing x t≤1/2 := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤2-8*x/9 := by linarith
  have hpt := mul_le_mul_of_nonneg_left ht hp
  have hpt' := mul_le_mul_of_nonneg_left ht' hp
  have hm : 0≤1-x := by linarith
  have hmt := mul_le_mul_of_nonneg_left ht hm
  have hmt' := mul_le_mul_of_nonneg_left ht' hm
  have he : t-crossing x t=((1-x)*t+5*x/9)/denominator x := by
    unfold crossing
    apply (eq_div_iff hd.ne').mpr
    rw [sub_mul,div_mul_cancel₀ _ hd.ne']
    unfold denominator
    ring
  refine ⟨(le_div_iff₀ hd).mpr ?_,(div_le_iff₀ hd).mpr ?_,?_,?_⟩
  · unfold denominator
    nlinarith
  · unfold denominator
    nlinarith
  · rw [he]
    apply (le_div_iff₀ hd).mpr
    unfold denominator
    nlinarith
  · rw [he]
    apply (div_le_iff₀ hd).mpr
    unfold denominator
    nlinarith

lemma inverse_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    inverseExponent δ x (crossing x t)=shortExponent δ x t := by
  unfold inverseExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

lemma plain_at_crossing (δ x t : ℝ) (hd : denominator x≠0) :
    plainExponent δ x t (crossing x t)=shortExponent δ x t := by
  unfold plainExponent crossing shortExponent primeWeight
  field_simp
  unfold denominator
  ring

theorem selected_short_bound {δ x t r : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2) :
    (r≤ crossing x t → plainExponent δ x t r≤ shortExponent δ x t) ∧
      (crossing x t≤ r → inverseExponent δ x r≤ shortExponent δ x t) := by
  have hd : denominator x≠0 := ne_of_gt (lt_of_lt_of_le (by norm_num) (denominator_lower hx'))
  constructor
  · intro hr
    rw [←plain_at_crossing δ x t hd]
    unfold plainExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤2-8*x/9 by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]
  · intro hr
    rw [←inverse_at_crossing δ x t hd]
    unfold inverseExponent
    have hh := mul_le_mul_of_nonneg_left hr (show 0≤1-x by linarith)
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hh)]

lemma short_ge_base {δ x t : ℝ} (hδ : 0≤δ) (_hx : 0≤x) (hx' : x≤1/2)
    (ht : t≤3/2) : 1-δ≤ shortExponent δ x t := by
  have hd : 0<denominator x := lt_of_lt_of_le (by norm_num) (denominator_lower hx')
  have hp : 0≤primeWeight x := mul_nonneg (by linarith) (by linarith)
  unfold shortExponent
  exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (mul_nonneg hδ hp) hd.le) (by linarith))

theorem capacity_loss {q m Δ γ : ℝ} (_hq : 0≤q) (hq' : q≤1/2)
    (hm : 1/3-γ≤ m) (hm' : m≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hγ : 0≤γ) :
    2*q*(1-2*m)*(2/9-1/(9/2+12*Δ))≤Δ/4+2*γ := by
  have hd : 0<9/2+12*Δ := by linarith
  have hden : (16 : ℝ)≤(9/2)*(9/2+12*Δ) := by nlinarith
  have hqmul : q*(1-2*m)≤(1/2)*(1/3+2*γ) :=
    mul_le_mul hq' (by linarith) (by linarith) (by norm_num)
  have hn := mul_le_mul_of_nonneg_right hqmul (show 0≤24*Δ by positivity)
  have hg := mul_le_mul_of_nonneg_left hΔ' (show 0≤24*γ by positivity)
  have he : 2*q*(1-2*m)*(2/9-1/(9/2+12*Δ)) =
      24*q*(1-2*m)*Δ/((9/2)*(9/2+12*Δ)) := by field_simp; ring
  rw [he]
  apply (div_le_iff₀ (show 0<(9/2)*(9/2+12*Δ) by positivity)).mpr
  have hb := mul_le_mul_of_nonneg_left hden (show 0≤Δ/4+2*γ by positivity)
  nlinarith

theorem plain_capacity_comparison {δ x Δ t r m γ : ℝ}
    (hδ : 0≤δ) (hδ' : δ≤1) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hm : 1/3-γ≤ m) (hm' : m≤1/2)
    (hγ : 0≤γ) (hlength : t-r-γ≤ m) :
    1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)≤plainExponent δ x t r+Δ/4+4*γ := by
  have hq : 0≤δ*x := mul_nonneg hδ hx
  have hq' : δ*x≤1/2 := (mul_le_mul hδ' hx' hx (by norm_num)).trans_eq (by ring)
  have hloss := capacity_loss hq hq' hm hm' hΔ hΔ' hγ
  have hc : 0≤δ*(2-8*x/9) := mul_nonneg hδ (by linarith)
  have hc' : δ*(2-8*x/9)≤2 := by
    have hh := mul_le_mul_of_nonneg_right hδ' (show 0≤2-8*x/9 by linarith)
    nlinarith
  have hlinear := mul_le_mul_of_nonneg_left (show t-r-m≤γ by linarith) hc
  have herror := mul_le_mul_of_nonneg_right hc' hγ
  have hid : (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9))-plainExponent δ x t r =
      δ*(2-8*x/9)*(t-r-m) := by unfold plainExponent; ring
  have hid' : 1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ) =
      (1-2*δ*m-2*(δ*x)*(1-2*m)*(2/9)) +
      2*(δ*x)*(1-2*m)*(2/9-1/(9/2+12*Δ)) := by ring
  rw [hid']
  linarith

lemma inverse_zero_capacity {δ r ν : ℝ} (hδ : 0≤δ)
    (hcap : (1-r)/2≤ν) : 1-δ*r≤1-δ+2*δ*ν := by
  have hh := mul_le_mul_of_nonneg_left hcap hδ
  nlinarith

lemma plain_zero_capacity {δ m κ ν : ℝ} (hδ : 0≤δ) (hκ : 0<κ)
    (hκ' : κ≤1) (hν : 0≤ν) (hcap : (1-2*m)/(6*κ)≤ν) :
    1-2*δ*m≤1-δ+6*δ*ν := by
  have hh := (div_le_iff₀ (show 0<6*κ by positivity)).mp hcap
  have hk := mul_le_mul_of_nonneg_right hκ' hν
  have hm : 1-2*m≤6*ν := by nlinarith
  have hh' := mul_le_mul_of_nonneg_left hm hδ
  nlinarith

lemma long_count_bound {δ r t γ : ℝ} (hδ : δ≤5/6) (_hγ : 0≤γ)
    (hr : r≤t+γ) :
    1-5/6+(5/6-δ)*r≤longExponent δ t+(5/6-δ)*γ := by
  have hh := mul_le_mul_of_nonneg_left hr (show 0≤5/6-δ by linarith)
  unfold longExponent
  nlinarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountOptimization
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

theorem count_bound_of_source_branches (B C U δ x Δ t r m ε ν γ : ℝ)
    (hC : 0≤C) (hU : 1≤U) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (ht : 1≤t) (ht' : t≤3/2) (hν : 0≤ν) (hγ : 0≤γ)
    (hleft : t-r-γ≤ m) (hright : r≤t+γ)
    (hI0 : B≤C*U^(max 1 ((1+5*r)/6)-δ*r+ε))
    (hP0 : B≤C*U^(1-2*δ*m+ε))
    (hI : 23/37≤ r → r<1 → ν<(1-r)/2 → B≤C*U^(inverseExponent δ x r+ε))
    (hP : r≤ crossing x t → m<1/2 → ν<(1-2*m)/(9/2+12*Δ) →
      B≤C*U^(1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+ε)) :
    B≤C*U^(max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ) := by
  let target := max (shortExponent δ x t) (longExponent δ t)+Δ/4+ε+6*ν+5*γ
  have hshort : shortExponent δ x t≤ max (shortExponent δ x t) (longExponent δ t) := le_max_left _ _
  have hlong : longExponent δ t≤ max (shortExponent δ x t) (longExponent δ t) := le_max_right _ _
  have hbase := short_ge_base hδ hx hx' ht'
  have hcross := crossing_bounds hx hx' ht ht'
  have hchoose := selected_short_bound (t:=t) (r:=r) hδ hx hx'
  have promote (p : ℝ) (hp : B≤C*U^p) (hpt : p≤target) : B≤C*U^target :=
    hp.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU hpt) hC)
  by_cases hr1 : 1≤ r
  · have hmax : max 1 ((1+5*r)/6)=(1+5*r)/6 := max_eq_right (by linarith)
    rw [hmax] at hI0
    apply promote _ hI0
    have hl := long_count_bound hδ' hγ hright
    dsimp [target]
    have hcγ : (5/6-δ)*γ≤γ := by nlinarith [mul_nonneg hδ hγ]
    nlinarith
  have hr1' : r<1 := lt_of_not_ge hr1
  have hmax : max 1 ((1+5*r)/6)=1 := max_eq_left (by linarith)
  rw [hmax] at hI0
  by_cases hrc : crossing x t≤ r
  · by_cases hcap : (1-r)/2≤ν
    · apply promote _ hI0
      have hz := inverse_zero_capacity hδ hcap
      have hv : 2*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
      dsimp [target]
      linarith
    · apply promote _ (hI (hcross.1.trans hrc) hr1' (lt_of_not_ge hcap))
      have hs := hchoose.2 hrc
      dsimp [target]
      linarith
  have hrc' : r≤ crossing x t := (lt_of_not_ge hrc).le
  by_cases hm : 1/2≤ m
  · apply promote _ hP0
    have hm' := mul_le_mul_of_nonneg_left hm hδ
    dsimp [target]
    linarith
  have hm' : m<1/2 := lt_of_not_ge hm
  by_cases hcap : (1-2*m)/(9/2+12*Δ)≤ν
  · apply promote _ hP0
    have hk0 : 0<3/4+2*Δ := by linarith
    have hk1 : 3/4+2*Δ≤1 := by linarith
    have hz := plain_zero_capacity hδ hk0 hk1 hν
      (show (1-2*m)/(6*(3/4+2*Δ))≤ν by convert (preTransparency := .instances) hcap using 1; ring)
    have hv : 6*δ*ν≤6*ν := by nlinarith [mul_nonneg (sub_nonneg.mpr hδ') hν]
    dsimp [target]
    linarith
  · apply promote _ (hP hrc' hm' (lt_of_not_ge hcap))
    have hmm : 1/3-γ≤ m := by linarith [hcross.2.2.1]
    have hp := plain_capacity_comparison hδ (show δ≤1 by linarith) hx hx' hΔ hΔ'
      hmm hm'.le hγ hleft
    have hs := hchoose.1 hrc'
    dsimp [target]
    linarith

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorRowCount

lemma denominator_endpoint (x : ℝ) : denominator x=Endpoint.denominator (1/2-x) := by
  unfold denominator Endpoint.denominator
  ring

lemma primeWeight_endpoint (x : ℝ) : primeWeight x=Endpoint.primeWeight (1/2-x) := by
  unfold primeWeight Endpoint.primeWeight
  ring

theorem balanced_cutoff_bounds {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    1≤Endpoint.balancedCutoff δ (1/2-x) ∧ Endpoint.balancedCutoff δ (1/2-x)≤3/2 := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hd := Endpoint.denominator_bounds hy hy'
  have hp := Endpoint.primeWeight_bounds hy hy'
  have hJ := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
  have hJp : 0<Endpoint.balanceDenominator δ (1/2-x) := by linarith [hJ.1]
  unfold Endpoint.balancedCutoff
  constructor
  · exact le_add_of_nonneg_right (div_nonneg (mul_nonneg hδ (by linarith [hp.1])) (by positivity))
  · have hnum : δ*Endpoint.primeWeight (1/2-x)≤Endpoint.balanceDenominator δ (1/2-x) := by
      unfold Endpoint.balanceDenominator
      have hh := mul_nonneg (sub_nonneg.mpr hδ') (show 0≤Endpoint.denominator (1/2-x) by linarith [hd.1])
      linarith
    have hh : δ*Endpoint.primeWeight (1/2-x)/(2*Endpoint.balanceDenominator δ (1/2-x))≤1/2 :=
      (div_le_iff₀ (by positivity)).mpr (by linarith)
    linarith

theorem balanced_count_identity {δ x : ℝ} (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) :
    max (shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x)))
        (longExponent δ (Endpoint.balancedCutoff δ (1/2-x))) =
      Endpoint.balancedRowCount δ (1/2-x) := by
  have hy : 0≤1/2-x := by linarith
  have hy' : 1/2-x≤1/2 := by linarith
  have hDb : 0<Endpoint.denominator (1/2-x) := by
    have hh := Endpoint.denominator_bounds hy hy'
    linarith [hh.1]
  have hJb : 0<Endpoint.balanceDenominator δ (1/2-x) := by
    have hh := Endpoint.balanceDenominator_bounds hδ hδ' hy hy'
    linarith [hh.1]
  have hl : longExponent δ (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold longExponent Endpoint.balancedRowCount
    ring
  have hs : shortExponent δ x (Endpoint.balancedCutoff δ (1/2-x))=
      Endpoint.balancedRowCount δ (1/2-x) := by
    unfold shortExponent
    rw [denominator_endpoint,primeWeight_endpoint]
    unfold Endpoint.balancedRowCount Endpoint.balancedCutoff
    generalize hDd : Endpoint.denominator (1/2-x) = D at *
    generalize hPd : Endpoint.primeWeight (1/2-x) = P at *
    generalize hJd : Endpoint.balanceDenominator δ (1/2-x) = J at *
    have hJdef : J=(5/6-δ)*D+δ*P := by
      rw [←hJd, Endpoint.balanceDenominator, hDd, hPd]
    have hD : D ≠ 0 := hDb.ne'
    have hJ : J ≠ 0 := hJb.ne'
    field_simp [hD,hJ]
    rw [hJdef]
    ring
  rw [hl,hs,max_self]

end SevenEighths.HeckeDetectorRowCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessRows
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorWitnessRows
open HeckeFamily HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem Witness.frequency_bound {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) :
    |w.frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T := by
  have hnu : |w.nu|≤allowance := by simpa only [Real.norm_eq_abs] using w.nu_bound
  have hh := abs_sub_le (2*Real.pi*w.nu) 0 w.zero.im
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,
    abs_of_pos (show 0<2*Real.pi by positivity)] at hh
  exact hh.trans (add_le_add (mul_le_mul_of_nonneg_left hnu (by positivity)) w.zero_height)

theorem Witness.real_part_upper {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) : w.zero.re≤1 := by
  by_contra hn
  exact LFunction_ne_zero_of_one_lt_re (χ w.label) (lt_of_not_ge hn) w.zero_eq

theorem Witness.left_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.r=Real.logb U ((2 : ℝ)^w.left.val) := by
  rw [←w.left_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem Witness.right_exponent {ι : Type*} {χ : ι→Character} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (w : Witness χ U a ε tstar T allowance i) (hU : 1<U) :
    w.m=Real.logb U ((2 : ℝ)^w.right.val) := by
  rw [←w.right_scale,Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

end SevenEighths.HeckeDetectorWitnessRows

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorSupportedWitness
open HeckeFamily HeckeDetectorWitnessRows

theorem fiber_lengths {Row Label : Type*} (rows : Finset Row) (hne : rows.Nonempty)
    (χ : Row→Label→Character) (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (J K : Fin (dyadicLength U))
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    tstar-r-ε≤ m ∧ r≤tstar+ε ∧ m≤1/2+75*ε ∧ tstar-1/2-76*ε≤ r ∧ 0≤ m := by
  obtain ⟨u,hu⟩ := hne
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by
    rw [(w u).toWitness.left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by
    rw [(w u).toWitness.right_exponent hU,hK u hu]
  exact hr ▸ hm ▸ ⟨(w u).product_length_lower,(w u).inverse_length_upper,
    (w u).plain_length_upper,(w u).inverse_length_lower,(w u).plain_length_lower⟩

end SevenEighths.HeckeDetectorSupportedWitness

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorAdaptiveCutoff
namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.HeckeDetectorAdaptiveCutoff
open HeckeFamily HeckeDetectorSupportedWitness HeckeDetectorRowCount

theorem cutoff_bounds (δ q : ℝ) (hδ : 0≤δ) : 1≤ cutoff δ q ∧ cutoff δ q≤3/2 := by
  unfold cutoff
  split_ifs with hd
  · exact balanced_cutoff_bounds hδ hd (le_min (by norm_num) (le_max_left _ _)) (min_le_left _ _)
  · norm_num

theorem cutoff_eq_balanced (δ q : ℝ) (hδ : 0<δ) (hd : δ≤5/6)
    (hq : 0≤q) (hq' : q≤δ/2) :
    cutoff δ q=Endpoint.balancedCutoff δ (1/2-q/δ) := by
  have hx : 0≤q/δ := div_nonneg hq hδ.le
  have hx' : q/δ≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  simp only [cutoff,if_pos hd,max_eq_right hx,min_eq_right hx']

end SevenEighths.HeckeDetectorAdaptiveCutoff

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorBranchBudget
namespace OAI

noncomputable section
namespace SevenEighths.HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem no_slot_inverse_loss (r δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : 0≤ mesh) (hν : 0≤ν) :
    max 1 ((1+5*r)/6)-δ*r+2*ε+εm≤
      max 1 ((1+5*r)/6)-δ*r+commonLoss ε εm mesh ν := by
  unfold commonLoss
  linarith

theorem no_slot_plain_loss (m δ ε εm mesh ν : ℝ)
    (hε : 0≤ε) (hm : m≤1/2+75*ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    max 1 (2*m)-2*δ*m+4*ε+εm≤1-2*δ*m+commonLoss ε εm mesh ν := by
  have hx : max 1 (2*m)≤1+150*ε := max_le (by linarith) (by linarith)
  unfold commonLoss
  linarith

theorem inverse_marked_loss (r δ x ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    1-δ*r-2*(δ*x)*((1-r)/2-ν)+2*ε+δ*mesh+εm≤
      inverseExponent δ x r+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold inverseExponent commonLoss
  nlinarith

theorem plain_marked_loss (m δ x Δ ε εm mesh ν : ℝ)
    (hδ : 0≤δ) (hδ1 : δ≤1) (_hx : 0≤x) (hx1 : x≤1/2)
    (hε : 0≤ε) (hmesh : 0≤ mesh) (hν : 0≤ν) :
    1-2*δ*m-2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)+4*ε+δ*mesh+εm≤
      1-2*δ*m-2*(δ*x)*(1-2*m)/(9/2+12*Δ)+commonLoss ε εm mesh ν := by
  have hq : 2*(δ*x)≤1 := by nlinarith only [mul_nonneg hδ (sub_nonneg.mpr hx1), hδ1]
  have hm := mul_le_mul_of_nonneg_right hδ1 hmesh
  have hn := mul_le_mul_of_nonneg_right hq hν
  unfold commonLoss
  have heq : 2*(δ*x)*((1-2*m)/(9/2+12*Δ)-ν)=
      2*(δ*x)*(1-2*m)/(9/2+12*Δ)-2*(δ*x)*ν := by ring
  rw [heq]
  linarith

theorem inverse_requested_capacity (r ν : ℝ) (hr : 23/37≤ r) (_hr1 : r<1)
    (hν : 0<ν) (hνcap : ν<(1-r)/2) :
    0≤(1-r)/2-ν ∧ (1-r)/2-ν≤7/37 ∧
      r+2*((1-r)/2-ν)<1 ∧ 2*r+8*((1-r)/2-ν)<3 := by
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem plain_requested_capacity (Δ x t r m ε ν : ℝ)
    (hΔ : 0≤Δ) (hx : 0≤x) (hx1 : x≤1/2) (ht : 1≤t) (ht1 : t≤3/2)
    (hr : r≤ crossing x t) (hleft : t-r-ε≤ m) (hε : ε≤1/12)
    (hν : 0≤ν) (hνcap : ν<(1-2*m)/(9/2+12*Δ)) :
    0≤(1-2*m)/(9/2+12*Δ)-ν ∧ (1-2*m)/(9/2+12*Δ)-ν≤7/37 ∧
      2*m+6*(3/4+2*Δ)*((1-2*m)/(9/2+12*Δ)-ν)≤1 := by
  have hcross := crossing_bounds hx hx1 ht ht1
  have hm : 1/4≤ m := by linarith [hcross.2.2.1]
  have hd : 0<9/2+12*Δ := by linarith
  have hc : (1-2*m)/(9/2+12*Δ)≤7/37 := (div_le_iff₀ hd).mpr (by nlinarith)
  refine ⟨by linarith,by linarith,?_⟩
  have heq : 6*(3/4+2*Δ)=9/2+12*Δ := by ring
  rw [heq,mul_sub,mul_div_cancel₀ _ hd.ne']
  nlinarith [mul_nonneg hd.le hν]

end SevenEighths.HeckeDetectorBranchBudget

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationConjugation
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate ContDiff
open Complex
namespace SevenEighths.HeckeInverseAmplification
open HeckeFamily HeckeDyadic

theorem coefficient_inverse_conj (χ : Character) (inv : Bool) (J : Ideal O) :
    coefficient χ.inverse inv J=conj (coefficient χ inv J) := by
  cases inv <;> simp [coefficient,idealCoeff_inverse_conj]

theorem conj_positive_cpow (x : ℝ) (hx : 0<x) (z : ℂ) :
    conj ((x : ℂ)^z)=(x : ℂ)^(conj z) := by
  have hh := Complex.cpow_conj (x : ℂ) z
    (by rw [Complex.arg_ofReal_of_nonneg hx.le]; exact Real.pi_ne_zero.symm)
  simpa only [conj_ofReal] using hh.symm

theorem conj_shift (σ freq : ℝ) : conj (_root_.OAI.SevenEighths.HeckeDyadic.shift σ freq)=_root_.OAI.SevenEighths.HeckeDyadic.shift σ (-freq) := by
  simp only [HeckeDyadic.shift,map_sub,map_mul,conj_ofReal,conj_I,ofReal_neg]
  ring

theorem conj_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    conj (polynomial χ inv W D σ freq)=
      polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq) := by
  unfold polynomial
  rw [map_mul,conj_tsum,conj_positive_cpow D hD]
  have hhalf : conj (-(1/2 : ℂ))= -(1/2 : ℂ) := by
    simp only [map_neg,map_div₀,map_one,map_ofNat]
  rw [hhalf]
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,map_mul,←coefficient_inverse_conj]
  rw [conj_positive_cpow _ (div_pos (norm_pos J) hD),map_neg,conj_shift]

theorem polynomial_inverse_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ.inverse inv (fun x => conj (W x)) D σ (-freq)‖=
      ‖polynomial χ inv W D σ freq‖ := by
  rw [←conj_polynomial χ inv W D σ freq hD,norm_conj]

end SevenEighths.HeckeInverseAmplification

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorCoefficientTransfer
namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
open Complex
namespace SevenEighths.HeckeDetectorCoefficientTransfer
open HeckeFamily HeckeDyadic HeckeInverseAmplification

theorem polynomial_eq_of_idealCoeff (χ ψ : Character)
    (hc : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) :
    polynomial χ inv W D σ freq=polynomial ψ inv W D σ freq := by
  unfold polynomial
  congr 1
  apply tsum_congr
  intro J
  simp only [summand,coefficient,hc]

theorem norm_of_oriented_coefficients (χ ψ : Character) (reverse : Bool)
    (hc : ∀ J : Ideal O,idealCoeff χ J=
      if reverse then conj (idealCoeff ψ J) else idealCoeff ψ J)
    (inv : Bool) (W : ℝ→ℂ) (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial χ inv W D σ freq‖=
      ‖polynomial ψ inv (orientedProfile reverse W) D σ (orientedFrequency reverse freq)‖ := by
  cases reverse
  · exact congrArg (fun z : ℂ => ‖z‖) (polynomial_eq_of_idealCoeff χ ψ hc inv W D σ freq)
  · have hc' : ∀ J : Ideal O,idealCoeff χ J=idealCoeff ψ.inverse J := by
      intro J
      simpa only [Bool.true_eq,ite_true,idealCoeff_inverse_conj] using hc J
    rw [polynomial_eq_of_idealCoeff χ ψ.inverse hc' inv W D σ freq]
    have hh := polynomial_inverse_norm ψ inv (fun x => conj (W x)) D σ (-freq) hD
    simpa only [orientedProfile,orientedFrequency,Bool.true_eq,ite_true,conj_conj,neg_neg] using hh

theorem orientedFrequency_abs (reverse : Bool) (freq : ℝ) :
    |orientedFrequency reverse freq|=|freq| := by cases reverse <;> simp [orientedFrequency]

end SevenEighths.HeckeDetectorCoefficientTransfer

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.PrimeAmplitudeBins
namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.HeckePrimeAmplitudeBins

theorem amplitude_bounds (P cap mesh : ℝ) (Q : ℂ) (hcap : 0≤ cap) :
    0≤amplitude P cap mesh Q ∧ amplitude P cap mesh Q≤ cap := by
  unfold amplitude
  split_ifs
  · exact ⟨le_rfl,hcap⟩
  · exact ⟨le_min hcap (le_max_left _ _),min_le_left _ _⟩

end SevenEighths.HeckePrimeAmplitudeBins

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorPhysicalSelection
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorPhysicalSelection
open HeckeFamily HeckePrimeAmplitudeBins
variable (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)

theorem weightedMean_bounds {Slot : Type*} (slots : Finset Slot) (w g : Slot→ℝ)
    (δ : ℝ) (hw : ∀ s∈slots,0≤w s) (hL : 0<∑ s∈slots,w s)
    (hg : ∀ s∈slots,0≤g s ∧ g s≤δ/2) :
    0≤weightedMean slots w g ∧ weightedMean slots w g≤δ/2 := by
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun s hs => mul_nonneg (hw s hs) (hg s hs).1)) hL.le
  · apply (div_le_iff₀ hL).mpr
    calc
      _ ≤ ∑ s∈slots,w s*(δ/2) := Finset.sum_le_sum (fun s hs =>
        mul_le_mul_of_nonneg_left (hg s hs).2 (hw s hs))
      _ = _ := by rw [←Finset.sum_mul]; ring

end SevenEighths.HeckeDetectorPhysicalSelection

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberSpikes
namespace OAI

noncomputable section
open scoped Classical
open Set
namespace SevenEighths.HeckeDetectorFiberSpikes
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorProfiles HeckeDetectorDyadicProfiles

theorem fiber_spikes {Row Label : Type*} (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ) (hU : 1<U) (ha : 0≤a)
    (w : ∀ u, Witness (χ u) U a ε tstar T allowance i)
    (label : Label) (J K : Fin (dyadicLength U))
    (hlabel : ∀ u∈rows,(w u).label=label)
    (hJ : ∀ u∈rows,(w u).left=J) (hK : ∀ u∈rows,(w u).right=K) :
    let r := Real.logb U ((2 : ℝ)^J.val)
    let m := Real.logb U ((2 : ℝ)^K.val)
    ∀ u∈rows,
      (w u).zero.re∈Icc (0 : ℝ) 1 ∧
      |(w u).frequency|≤2*Real.pi*allowance+(3*i : ℕ)*T ∧
      U^((2*a-1)*r-2*ε)≤
        ‖polynomial (χ u label) true
          (HeckeDetectorDyadicBridge.inverseProfile cutoff positiveAnnular (U^tstar) (U^r))
          (U^r) (w u).zero.re (w u).frequency‖^2 ∧
      U^((2*a-1)*m-2*ε)≤
        ‖polynomial (χ u label) false positiveAnnular (U^m) (w u).zero.re (w u).frequency‖^2 := by
  dsimp only
  intro u hu
  have hr : (w u).r=Real.logb U ((2 : ℝ)^J.val) := by rw [(w u).left_exponent hU,hJ u hu]
  have hm : (w u).m=Real.logb U ((2 : ℝ)^K.val) := by rw [(w u).right_exponent hU,hK u hu]
  refine ⟨⟨ha.trans (w u).zero_lower,(w u).real_part_upper⟩,(w u).frequency_bound,?_,?_⟩
  · simpa only [hr,hlabel u hu,Witness.frequency] using (w u).inverse_spike
  · simpa only [hm,hlabel u hu,Witness.frequency] using (w u).plain_spike

end SevenEighths.HeckeDetectorFiberSpikes

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorNoSlotInverseCount
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set Filter
namespace SevenEighths.HeckeDetectorNoSlotInverseCount
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount

theorem no_slot_inverse_count
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (R εm : ℝ) (hR : 0≤R) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ {Label : Type*} (rows : Finset FreeRow) (χ : FreeRow→Label→Character)
        (a ε tstar T allowance : ℝ) (i : ℕ), 1<U → 1/2≤a →
      ∀ (witness : ∀ u,Witness (χ u) U a ε tstar T allowance i)
        (label : Label) (J K : Fin (dyadicLength U)),
      (∀ u∈rows,(witness u).label=label) →
      (∀ u∈rows,(witness u).left=J) → (∀ u∈rows,(witness u).right=K) →
      0≤Real.logb U ((2 : ℝ)^J.val) → Real.logb U ((2 : ℝ)^J.val)≤R →
      ∀ (data : RowData) (reverse : Bool) (C height : ℝ),0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      (∀ u∈rows,((Ideal.span {u.val}).absNorm : ℝ)≤U) →
      (∀ u∈rows,∀ I : Ideal O,idealCoeff (χ u label) I=
        if reverse then starRingEnd ℂ (idealCoeff (data.character ⟨u.val,u.property.1⟩) I)
        else idealCoeff (data.character ⟨u.val,u.property.1⟩) I) →
      (∀ n : ℕ,n≤2 → ∀ s∈Icc (0 : ℝ) 1,∀ t∈Icc (-height) height,
        let W := twistProfile (logTest
          (orientedProfile reverse (inverseTest U tstar (Real.logb U ((2 : ℝ)^J.val)))) n) s t
        RawMoment data W c κ C ∧ RawMoment data (scaleProfile W) c κ C) →
      (rows.card : ℝ)≤(12*(1+height)*(C*K₀))*
        U^(sourceExponent (Real.logb U ((2 : ℝ)^J.val))-
          (2*a-1)*Real.logb U ((2 : ℝ)^J.val)+2*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,he⟩ := no_slot_rowwise_endpoint M H hH S φ hφ hφc hφp hφ0 hφne
    a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB R εm hR hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [he] with U he
  intro Label rows χ a ε tstar T allowance i hU ha witness label J K hlabel hJ hK hr hrR
    data reverse C height hC hheight hfreq hrows hcoeff hraw
  let r := Real.logb U ((2 : ℝ)^J.val)
  let V := orientedProfile reverse (inverseTest U tstar r)
  have hUp : 0<U := zero_lt_one.trans hU
  have hD : 0<U^r := Real.rpow_pos_of_pos hUp _
  have hbase := HeckeDetectorDyadicActual.inverse_profile_support (U^tstar) (U^r)
  have hs : Function.support V⊆Icc (1/4 : ℝ) (9/4) := by
    cases reverse
    · exact hbase
    · simpa only [V,orientedProfile,Bool.true_eq,ite_true,conjugate_profile_support,inverseTest] using hbase
  have hb := HeckeDetectorDyadicActual.inverse_profile_smooth (U^tstar) (U^r)
  have hV : ContDiff ℝ ∞ V := by
    cases reverse
    · exact hb
    · exact conjugate_profile_smooth _ hb
  have hsp := HeckeDetectorFiberSpikes.fiber_spikes rows χ U a ε tstar T allowance i hU
    (by linarith) witness label J K hlabel hJ hK
  have hσ (u : FreeRow) (hu : u∈rows) : (witness u).zero.re∈Icc (0 : ℝ) 1 := (hsp u hu).1
  have hf (u : FreeRow) (hu : u∈rows) :
      orientedFrequency reverse (witness u).frequency∈Icc (-height) height := by
    apply abs_le.mp
    rw [orientedFrequency_abs]
    exact (hsp u hu).2.1.trans hfreq
  have hen := he r data rows V (1/4) (9/4) C height (fun u => (witness u).zero.re)
    (fun u => orientedFrequency reverse (witness u).frequency)
    hr hrR hC hheight (by norm_num) (by norm_num) hs hV hrows hσ hf hraw
  have hspike (u : FreeRow) (hu : u∈rows) : U^((2*a-1)*r-2*ε)≤
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2 := by
    have hh := (hsp u hu).2.2.1
    rw [norm_of_oriented_coefficients (χ u label) (data.character ⟨u.val,u.property.1⟩)
      reverse (hcoeff u hu) true _ _ _ _ hD] at hh
    exact hh
  have hen' : ∑ u∈rows,
      ‖polynomial (data.character ⟨u.val,u.property.1⟩) true V (U^r) (witness u).zero.re
        (orientedFrequency reverse (witness u).frequency)‖^2≤
      (12*(1+height)*(C*K₀))*U^(sourceExponent r+εm) := by
    convert (preTransparency := .instances) hen using 1; ring
  have hc' := HeckeDetectorRowCount.card_of_energy rows _ U ((2*a-1)*r-2*ε)
    (sourceExponent r+εm) (12*(1+height)*(C*K₀)) hUp hspike hen'
  convert (preTransparency := .instances) hc' using 1; congr 2; ring

end SevenEighths.HeckeDetectorNoSlotInverseCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRawFiber
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open Set
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorWitnessRows
open HeckeDetectorSupportedWitness HeckeDetectorCoefficientTransfer HeckeDetectorInverseFiberCount
open HeckeDetectorPhysicalSelection HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.mean_bounds (F : Fiber M H Label Slot U a ε tstar T allowance i) (ha : 1/2≤a) :
    0≤F.q ∧ F.q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := F.nonempty
  apply weightedMean_bounds F.slots F.widths F.bin (2*a-1)
    (fun s hs => (F.widths_pos s hs).le) (by linarith [F.supply])
  intro s hs
  rw [←F.fixed_bin u hu s hs]
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFiberPartition
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorFiberPartition
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

theorem card_eq_sum_fibers {Row Label Slot : Type*} [Fintype Label]
    (rows : Finset Row) (χ : Row→Label→Character)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (w : ∀ u,SupportedWitness (χ u) U a ε tstar T allowance i)
    (slots : Finset Slot) (mesh : ℝ) (hm : 0< mesh) (widths : Slot→ℝ)
    (physical : Row→Slot→ℂ) :
    rows.card=∑ bin : BinLabel slots ((2*a-1)/2) mesh, ∑ label : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        (fiber rows χ U a ε tstar T allowance i w slots mesh hm widths physical bin label J K).card := by
  have hh := Finset.card_eq_sum_card_fiberwise (s:=rows) (t:=Finset.univ)
    (f:=fun u => (amplitudeLabel slots U ((2*a-1)/2) mesh hm widths physical u,
      (w u).label,(w u).left,(w u).right)) (by intro u hu; exact Finset.mem_univ _)
  simpa only [Fintype.sum_prod_type,Prod.mk.injEq,fiber] using hh

end SevenEighths.HeckeDetectorFiberPartition

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorBatch
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorBatch
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorFiberPartition
open HeckeDetectorSupportedWitness HeckeDetectorWitnessRows HeckeDetectorPhysicalSelection

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Batch.card_eq_sum_fibers [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i) :
    B.rows.card=∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
      (B.fiberRows bin j J K).card :=
  HeckeDetectorFiberPartition.card_eq_sum_fibers B.rows B.family U a ε tstar T allowance i B.witness
    B.slots B.binWidth B.binWidth_pos B.widths
    (physical M H (fun u : FreeRow => u.val) B.profile B.upper B.widths B.external U)

theorem Batch.card_bound [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i)
    (C : ℝ) (exponent : B.Bin→ℝ) (hC : 0≤C) (hU : 0<U)
    (hfiber : ∀ bin j J K,∀ hne : (B.fiberRows bin j J K).Nonempty,
      ((B.fiber bin j J K hne).rows.card : ℝ)≤C*U^(exponent bin)) :
    (B.rows.card : ℝ)≤(Fintype.card Label : ℝ)*(dyadicLength U : ℝ)^2*C*
      ∑ bin : B.Bin,U^(exponent bin) := by
  have he : (B.rows.card : ℝ)=∑ bin : B.Bin, ∑ j : Label,
      ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        ((B.fiberRows bin j J K).card : ℝ) := by exact_mod_cast B.card_eq_sum_fibers
  rw [he]
  calc
    _ ≤ ∑ bin : B.Bin, ∑ j : Label, ∑ J : Fin (dyadicLength U), ∑ K : Fin (dyadicLength U),
        C*U^(exponent bin) := by
      apply Finset.sum_le_sum
      intro bin _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro J _
      apply Finset.sum_le_sum
      intro K _
      by_cases hn : (B.fiberRows bin j J K).Nonempty
      · exact hfiber bin j J K hn
      · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
        simp only [Finset.card_empty,Nat.cast_zero]
        exact mul_nonneg hC (Real.rpow_nonneg hU.le _)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      simp_rw [←mul_assoc]
      rw [←Finset.mul_sum]
      ring

end SevenEighths.HeckeDetectorBatch

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorRawBranches
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.HeckeDetectorRawFiber
open HeckeFamily HeckeDyadic HeckeDetectorWitnessRows HeckeDetectorSupportedWitness
open HeckeDetectorInverseFiberCount
variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem Fiber.lengths (F : Fiber M H Label Slot U a ε tstar T allowance i) (hU : 1<U) :
    tstar-F.r-ε≤F.m ∧ F.r≤tstar+ε ∧ F.m≤1/2+75*ε ∧ tstar-1/2-76*ε≤F.r ∧ 0≤F.m :=
  fiber_lengths F.rows F.nonempty F.family U a ε tstar T allowance i hU F.witness
    F.left F.right F.fixed_left F.fixed_right

theorem fiberConstant_bounds (C height K : ℝ) (hC : 0≤C) (hh : 0≤height) (hK : 0≤K) :
    0≤fiberConstant C height K ∧ 192*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*C≤fiberConstant C height K ∧
      12*(1+height)*(C*K)≤fiberConstant C height K := by
  have h1 : 0≤192*(1+height)*C := by positivity
  have h2 : 12*(1+height)*C≤192*(1+height)*C := by nlinarith
  have hbig : 192*(1+height)*C≤fiberConstant C height K :=
    le_mul_of_one_le_right h1 (le_max_left _ _)
  refine ⟨h1.trans hbig,hbig,h2.trans hbig,?_⟩
  calc
    _ = (12*(1+height)*C)*K := by ring
    _ ≤ (192*(1+height)*C)*max 1 K := mul_le_mul h2 (le_max_right _ _) hK h1

end SevenEighths.HeckeDetectorRawFiber

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorCountFromMoments
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorCountFromMoments
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBranchBudget
open HeckeDetectorRowCount

theorem count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε tstar T allowance Δ ν C height : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} (F : Fiber M H Label Slot U a ε tstar T allowance i),
      Moments F Δ c κ C height εm →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(max (shortExponent (2*a-1) (F.q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+F.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hamp⟩ := HeckeDetectorNoSlotInverseCount.no_slot_inverse_count
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB 2 εm (by norm_num) hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hamp] with U hamp
  intro a ε tstar T allowance Δ ν C height i hU ha hδcap hε hεsmall ht ht' hΔ hΔ' hν hC hh hf
    Label Slot F moments
  let δ := 2*a-1
  let x := F.q/δ
  have hδ : 0<δ := by dsimp [δ]; linarith
  have ha' : 1/2≤a := by linarith
  have hδ1 : δ≤1 := by dsimp [δ]; linarith
  obtain ⟨hq0,hqδ⟩ := F.mean_bounds ha'
  have hx : 0≤x := div_nonneg hq0 hδ.le
  have hx' : x≤1/2 := (div_le_iff₀ hδ).mpr (by dsimp [δ]; linarith)
  have hqx : δ*x=F.q := by dsimp [x]; field_simp
  have hgeom := F.lengths hU
  have hr0 : 0≤F.r := by linarith [hgeom.2.2.2.1]
  have hr2 : F.r≤2 := by linarith [hgeom.2.1]
  have hUp : 0<U := zero_lt_one.trans hU
  obtain ⟨hconst,hconstP,hconstI,hconstI0⟩ := fiberConstant_bounds C height K₀ hC hh hK
  have promote (C' p q : ℝ) (hC' : C'≤fiberConstant C height K₀)
      (hb : (F.rows.card : ℝ)≤C'*U^p) (hpq : p≤q) :
      (F.rows.card : ℝ)≤fiberConstant C height K₀*U^q := by
    exact hb.trans ((mul_le_mul_of_nonneg_right hC' (Real.rpow_nonneg hUp.le _)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hU.le hpq) hconst))
  have hi0 := hamp F.rows F.family a ε tstar T allowance i hU ha'
    (fun u => (F.witness u).toWitness) F.label F.left F.right F.fixed_label F.fixed_left F.fixed_right
    hr0 hr2 F.rowData F.reverse C height hC hh hf F.row_norm F.row_coeff moments.inverse_raw
  have hI0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(max 1 ((1+5*F.r)/6)-δ*F.r+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstI0 hi0
    exact no_slot_inverse_loss F.r δ ε εm F.mesh ν hε F.mesh_nonneg hν.le
  have hp0 := F.plain_unmarked_count moments hU (by linarith) hC hh hf
  have hP0 : (F.rows.card : ℝ)≤fiberConstant C height K₀*
      U^(1-2*δ*F.m+commonLoss ε εm F.mesh ν) := by
    apply promote _ _ _ hconstP hp0
    exact no_slot_plain_loss F.m δ ε εm F.mesh ν hε hgeom.2.2.1 F.mesh_nonneg hν.le
  have hI : 23/37≤F.r → F.r<1 → ν<(1-F.r)/2 →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(inverseExponent δ x F.r+commonLoss ε εm F.mesh ν) := by
    intro hr hr1 hv
    obtain ⟨hz,hz',hcap1,hcap2⟩ := inverse_requested_capacity F.r ν hr hr1 hν hv
    have hb := F.inverse_marked_count moments hU ha' hC hh hf ((1-F.r)/2-ν) hz hz' hcap1 hcap2
    apply promote _ _ _ hconstI hb
    have hl := inverse_marked_loss F.r δ x ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    rwa [hqx] at hl
  have hP : F.r≤ crossing x tstar → F.m<1/2 → ν<(1-2*F.m)/(9/2+12*Δ) →
      (F.rows.card : ℝ)≤fiberConstant C height K₀*
        U^(1-2*δ*F.m-2*(δ*x)*(1-2*F.m)/(9/2+12*Δ)+commonLoss ε εm F.mesh ν) := by
    intro hr hm hv
    obtain ⟨hz,hz',hcap⟩ := plain_requested_capacity Δ x tstar F.r F.m ε ν hΔ hx hx' ht ht'
      hr hgeom.1 (by linarith) hν.le hv
    have hb := F.plain_marked_count moments hU ha' hΔ hC hh hf
      ((1-2*F.m)/(9/2+12*Δ)-ν) hz hz' hcap
    apply promote _ _ _ hconstP hb
    have hl := plain_marked_loss F.m δ x Δ ε εm F.mesh ν hδ.le hδ1 hx hx' hε F.mesh_nonneg hν.le
    simpa only [hqx] using hl
  have hc' := count_bound_of_source_branches (F.rows.card : ℝ) (fiberConstant C height K₀) U δ x Δ
    tstar F.r F.m (commonLoss ε εm F.mesh ν) ν ε hconst hU.le hδ.le hδcap hx hx' hΔ hΔ'
    ht ht' hν.le hε hgeom.1 hgeom.2.1 hI0 hP0 hI hP
  convert (preTransparency := .instances) hc' using 1; congr 2
  unfold commonLoss
  ring

end SevenEighths.HeckeDetectorCountFromMoments

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.Hecke.DetectorFixedAmplitudeCount
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.HeckeDetectorFixedAmplitudeCount
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount

variable {M : Ideal O} {H : Subgroup (O ⧸ M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

lemma fiber_mean_eq (B : Batch M H Label Slot U a ε tstar T allowance i) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q)
    (bin : B.Bin) (j : Label) (J K : Fin (dyadicLength U))
    (hne : (B.fiberRows bin j J K).Nonempty) : (B.fiber bin j J K hne).q=q := by
  let u := hne.choose
  have hu : u ∈ B.fiberRows bin j J K := hne.choose_spec
  have huR : u∈B.rows := (Finset.mem_filter.mp hu).1
  rw [←hq u huR]
  unfold Fiber.q rowMean weightedMean
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  exact congrArg (fun g=>B.widths s*g) ((B.fiber bin j J K hne).fixed_bin u hu s hs).symm

lemma batch_mean_bounds (B : Batch M H Label Slot U a ε tstar T allowance i)
    (hne : B.rows.Nonempty) (ha : 1/2≤a) (q : ℝ)
    (hq : ∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
      (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) :
    0≤q ∧ q≤(2*a-1)/2 := by
  obtain ⟨u,hu⟩ := hne
  rw [←hq u hu]
  apply weightedMean_bounds B.slots B.widths _ (2*a-1)
    (fun s hs=>(B.widths_pos s hs).le) (by linarith [B.supply])
  intro s hs
  exact HeckePrimeAmplitudeBins.amplitude_bounds _ _ _ _ (by linarith)

theorem fixed_amplitude_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε tstar T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      1≤tstar → tstar≤3/2 → 0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε tstar T allowance i),
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ := HeckeDetectorCountFromMoments.count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε tstar T allowance Δ ν C height q i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf Label Slot _ B hq moments
  have hb := B.card_bound (fiberConstant C height K₀)
    (fun _=>max (shortExponent (2*a-1) (q/(2*a-1)) tstar) (longExponent (2*a-1) tstar)+
      Δ/4+159*ε+εm+B.mesh+7*ν)
    (fiberConstant_bounds C height K₀ hC hh hK).1 (zero_lt_one.trans hU) (by
      intro bin j J K hne
      have hc' := hcount a ε tstar T allowance Δ ν C height i hU ha hd hε hε' ht ht' hΔ hΔ' hν hC hh hf
        (B.fiber bin j J K hne) (moments bin j J K hne)
      rw [fiber_mean_eq B q hq bin j J K hne] at hc'
      exact hc')
  simpa only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_assoc] using hb
end SevenEighths.HeckeDetectorFixedAmplitudeCount

end

end OAI
end

section
-- module Solutions.OAIHecke.OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCount
namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem balanced_adaptive_count_from_raw_moments_oai
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorFixedAmplitudeCount.fixed_amplitude_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf Label Slot _ B hne hq hmom
  have hδ : 0<2*a-1 := by linarith
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds (2*a-1) q hδ.le
  have hc' := hcount a ε (cutoff (2*a-1) q) T allowance Δ ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hΔ hΔ' hν hC hh hf B hq hmom
  have he : max (shortExponent (2*a-1) (q/(2*a-1)) (cutoff (2*a-1) q))
      (longExponent (2*a-1) (cutoff (2*a-1) q)) =
      Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1)) := by
    rw [cutoff_eq_balanced (2*a-1) q hδ hd hqb.1 hqb.2]
    exact HeckeDetectorRowCount.balanced_count_identity hδ.le hd hx hx'
  rw [he] at hc'
  exact hc'

end SevenEighths.ProbeHighRowFamily

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.SevenEighths.ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments_oai.{u_1, u_2} := @OAI.SevenEighths.ProbeHighRowFamily.balanced_adaptive_count_from_raw_moments_oai.{u_1, u_2}
