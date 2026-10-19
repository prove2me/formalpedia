-- Prove2me | solution 1 for HumanMachine.Alone.pbar_thresholds
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T09:05:30.405251+00:00
-- url     : https://prove2.me/submissions/e4f1950e-8336-41ac-8451-306f9be7834c

import Mathlib
import Definitions.Def_HumanMachine_Alone_model
import Definitions.Def_HumanMachine_Accuracy_DecisionModel
set_option autoImplicit false

namespace HumanMachineEntropy

noncomputable def score (t q : ℝ) := Real.binEntropy t+t*Real.log q+(1-t)*Real.log (1-q)

theorem tangent_strict (q t : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hne : t ≠ q) :
    Real.binEntropy t < Real.binEntropy q+(Real.log (1-q)-Real.log q)*(t-q) := by
  have hd := Real.hasDerivAt_binEntropy (ne_of_gt hq.1) (ne_of_lt hq.2)
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := Real.strictConcave_binEntropy.lt_slope_of_hasDerivAt ht ⟨hq.1.le,hq.2.le⟩ h hd
    rw [slope_def_field] at hh
    have hh' := (lt_div_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']
  · have hh := Real.strictConcave_binEntropy.slope_lt_of_hasDerivAt ⟨hq.1.le,hq.2.le⟩ ht h hd
    rw [slope_def_field] at hh
    have hh' := (div_lt_iff₀ (sub_pos.mpr h)).mp hh
    nlinarith only [hh']

theorem score_self (q : ℝ) : score q q = 0 := by
  simp only [score,Real.binEntropy,Real.log_inv]
  ring

theorem score_neg (q t : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hne : t ≠ q) : score t q < 0 := by
  have h := tangent_strict q t hq ht hne
  have hh := score_self q
  unfold score at hh ⊢
  nlinarith only [h,hh]

theorem score_nonpos (q t : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : score t q ≤ 0 := by
  by_cases h : t=q
  · subst t; exact (score_self q).le
  · exact (score_neg q t hq ht h).le

theorem score_eq_zero_iff (q t : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : score t q = 0 ↔ t=q := by
  constructor
  · intro h
    by_contra hne
    exact (ne_of_lt (score_neg q t hq ht hne)) h
  · rintro rfl; exact score_self _

end HumanMachineEntropy

namespace HumanMachineEntropy

noncomputable def dg (lam p : ℝ) := p*Real.exp (1/lam)+1-p
noncomputable def db (lam p : ℝ) := p+(1-p)*Real.exp (1/lam)
noncomputable def good (lam p : ℝ) := p*Real.exp (1/lam)/dg lam p
noncomputable def bad (lam p : ℝ) := p/db lam p

theorem gibbs_facts (lam p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    good lam p ∈ Set.Ioo (0 : ℝ) 1 ∧ bad lam p ∈ Set.Ioo (0 : ℝ) 1 ∧
    Real.log (good lam p) = Real.log p + 1/lam - Real.log (dg lam p) ∧
    Real.log (1-good lam p) = Real.log (1-p)-Real.log (dg lam p) ∧
    Real.log (bad lam p) = Real.log p-Real.log (db lam p) ∧
    Real.log (1-bad lam p) = Real.log (1-p)+1/lam-Real.log (db lam p) := by
  have he := Real.exp_pos (1/lam)
  have hc : 0 < 1-p := sub_pos.mpr hp.2
  have hdg : 0 < dg lam p := by unfold dg; nlinarith only [mul_pos hp.1 he,hc]
  have hdb : 0 < db lam p := by unfold db; exact add_pos hp.1 (mul_pos hc he)
  have hg : good lam p ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos (mul_pos hp.1 he) hdg
    · apply (div_lt_one hdg).mpr
      unfold dg
      linarith only [hp.2]
  have hb : bad lam p ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · exact div_pos hp.1 hdb
    · apply (div_lt_one hdb).mpr
      unfold db
      nlinarith only [mul_pos hc he]
  have hgc : 1-good lam p = (1-p)/dg lam p := by
    unfold good
    field_simp
    unfold dg
    ring
  have hbc : 1-bad lam p = (1-p)*Real.exp (1/lam)/db lam p := by
    unfold bad
    field_simp
    unfold db
    ring
  refine ⟨hg,hb,?_,?_,?_,?_⟩
  · rw [good, Real.log_div (mul_ne_zero hp.1.ne' he.ne') hdg.ne',Real.log_mul hp.1.ne' he.ne',Real.log_exp]
  · rw [hgc,Real.log_div hc.ne' hdg.ne']
  · rw [bad,Real.log_div hp.1.ne' hdb.ne']
  · rw [hbc,Real.log_div (mul_ne_zero hc.ne' he.ne') hdb.ne',Real.log_mul hc.ne' he.ne',Real.log_exp]

theorem value_identity (lam mu p pg pb : ℝ) (hlam : lam ≠ 0)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    HumanMachine.Alone.value lam mu pg pb =
      lam*(mu*Real.log (dg lam p)+(1-mu)*Real.log (db lam p)) +
        lam*(mu*score pg (good lam p)+(1-mu)*score pb (bad lam p)-
          score (HumanMachine.Alone.choiceProb mu pg pb) p) := by
  obtain ⟨_,_,h1,h2,h3,h4⟩ := gibbs_facts lam p hp
  unfold score
  rw [h1,h2,h3,h4]
  unfold HumanMachine.Alone.value HumanMachine.Alone.cost HumanMachine.Alone.accuracy
    HumanMachine.Alone.choiceProb
  field_simp
  <;> ring

end HumanMachineEntropy

namespace HumanMachineEntropy
open HumanMachine.Alone

theorem choice_bounds (mu pg pb : ℝ) (hm : mu ∈ Set.Icc (0 : ℝ) 1)
    (hg : pg ∈ Set.Icc (0 : ℝ) 1) (hb : pb ∈ Set.Icc (0 : ℝ) 1) :
    choiceProb mu pg pb ∈ Set.Icc (0 : ℝ) 1 := by
  unfold choiceProb
  constructor
  · exact add_nonneg (mul_nonneg hm.1 hg.1) (mul_nonneg (sub_nonneg.mpr hm.2) hb.1)
  · have h1 := mul_le_mul_of_nonneg_left hg.2 hm.1
    have h2 := mul_le_mul_of_nonneg_left hb.2 (sub_nonneg.mpr hm.2)
    nlinarith only [h1,h2]

theorem optimal_interior (lam mu pg pb : ℝ) (hlam : 0 < lam)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (hopt : IsOptimal lam mu pg pb)
    (hp : choiceProb mu pg pb ∈ Set.Ioo (0 : ℝ) 1) :
    pg = good lam (choiceProb mu pg pb) ∧ pb = bad lam (choiceProb mu pg pb) := by
  let p := choiceProb mu pg pb
  obtain ⟨hg,hb,_⟩ := gibbs_facts lam p hp
  have hm : mu ∈ Set.Icc (0 : ℝ) 1 := ⟨hmu0.le,hmu1.le⟩
  have hgm : good lam p ∈ Set.Icc (0 : ℝ) 1 := ⟨hg.1.le,hg.2.le⟩
  have hbm : bad lam p ∈ Set.Icc (0 : ℝ) 1 := ⟨hb.1.le,hb.2.le⟩
  have hnew := hopt.2.2 (good lam p) hgm (bad lam p) hbm
  have hid1 := value_identity lam mu p pg pb hlam.ne' hp
  have hid2 := value_identity lam mu p (good lam p) (bad lam p) hlam.ne' hp
  have hpdef : choiceProb mu pg pb = p := rfl
  rw [hpdef,score_self,sub_zero] at hid1
  rw [score_self,score_self,mul_zero,mul_zero,zero_add,zero_sub] at hid2
  have hsc := score_nonpos p (choiceProb mu (good lam p) (bad lam p)) hp
    (choice_bounds mu _ _ hm hgm hbm)
  have hsc' := mul_nonpos_of_nonneg_of_nonpos hlam.le hsc
  have hsumlam : 0 ≤ lam*(mu*score pg (good lam p)+(1-mu)*score pb (bad lam p)) := by
    nlinarith only [hid1,hid2,hnew,hsc']
  have hsum := nonneg_of_mul_nonneg_right hsumlam hlam
  have h1 := mul_nonpos_of_nonneg_of_nonpos hmu0.le (score_nonpos _ _ hg hopt.1)
  have h2 := mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hmu1).le (score_nonpos _ _ hb hopt.2.1)
  have h1z : mu*score pg (good lam p) = 0 := by linarith only [hsum,h1,h2]
  have h2z : (1-mu)*score pb (bad lam p) = 0 := by linarith only [hsum,h1,h2]
  exact ⟨(score_eq_zero_iff _ _ hg hopt.1).mp ((mul_eq_zero.mp h1z).resolve_left hmu0.ne'),
    (score_eq_zero_iff _ _ hb hopt.2.1).mp ((mul_eq_zero.mp h2z).resolve_left (sub_pos.mpr hmu1).ne')⟩

end HumanMachineEntropy

open HumanMachine.Alone

-- Alexander Richard Towell (queelius), with Codex assistance.
-- Binary Gibbs variational argument for the conditional-choice formulas of Lemma 1.
theorem conditional_solution (lam mu pg pb : ℝ) (hlam : 0 < lam)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (hopt : IsOptimal lam mu pg pb) :
    let p := choiceProb mu pg pb
    pg = p * Real.exp (1 / lam) / (p * Real.exp (1 / lam) + 1 - p) ∧
      pb = p / (p + (1 - p) * Real.exp (1 / lam)) := by
  have hc := HumanMachineEntropy.choice_bounds mu pg pb ⟨hmu0.le,hmu1.le⟩ hopt.1 hopt.2.1
  by_cases hz : choiceProb mu pg pb = 0
  · have hp : mu*pg+(1-mu)*pb=0 := hz
    have hn1 := mul_nonneg hmu0.le hopt.1.1
    have hn2 := mul_nonneg (sub_pos.mpr hmu1).le hopt.2.1.1
    have h1 : mu*pg=0 := by linarith only [hp,hn1,hn2]
    have h2 : (1-mu)*pb=0 := by linarith only [hp,hn1,hn2]
    have hpg := (mul_eq_zero.mp h1).resolve_left hmu0.ne'
    have hpb := (mul_eq_zero.mp h2).resolve_left (sub_pos.mpr hmu1).ne'
    simp [hpg,hpb,choiceProb]
  by_cases ho : choiceProb mu pg pb = 1
  · have hp : mu*pg+(1-mu)*pb=1 := ho
    have hn1 := mul_nonneg hmu0.le (sub_nonneg.mpr hopt.1.2)
    have hn2 := mul_nonneg (sub_pos.mpr hmu1).le (sub_nonneg.mpr hopt.2.1.2)
    have h1 : mu*(1-pg)=0 := by nlinarith only [hp,hn1,hn2]
    have h2 : (1-mu)*(1-pb)=0 := by nlinarith only [hp,hn1,hn2]
    have hpg : pg=1 := by have h := (mul_eq_zero.mp h1).resolve_left hmu0.ne'; linarith only [h]
    have hpb : pb=1 := by have h := (mul_eq_zero.mp h2).resolve_left (sub_pos.mpr hmu1).ne'; linarith only [h]
    simp [hpg,hpb,choiceProb,Real.exp_ne_zero]
  have hi : choiceProb mu pg pb ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · by_contra h
      apply hz
      linarith [hc.1]
    · by_contra h
      apply ho
      linarith [hc.2]
  simpa [HumanMachineEntropy.good,HumanMachineEntropy.bad,HumanMachineEntropy.dg,HumanMachineEntropy.db] using
    HumanMachineEntropy.optimal_interior lam mu pg pb hlam hmu0 hmu1 hopt hi

#print axioms conditional_solution

namespace HumanMachineOptimizer
open HumanMachine.Alone HumanMachineEntropy

lemma exp_large (lam : ℝ) (hlam : 0 < lam) : 1 < Real.exp (1/lam) :=
  Real.one_lt_exp_iff.mpr (one_div_pos.mpr hlam)

lemma pbar_algebra (lam mu : ℝ) (hlam : 0 < lam) :
    pBar lam mu = (mu*(Real.exp (1/lam)+1)-1)/(Real.exp (1/lam)-1) := by
  have he := exp_large lam hlam
  have he0 := Real.exp_pos (1/lam)
  unfold pBar
  rw [Real.exp_neg]
  field_simp
  <;> ring

lemma pbar_thresholds_core (lam : ℝ) (hlam : 0 < lam) :
    ∀ mu : ℝ, (1 ≤ pBar lam mu ↔ muHigh lam ≤ mu) ∧
      (pBar lam mu ≤ 0 ↔ mu ≤ muLow lam) := by
  intro mu
  have he := exp_large lam hlam
  have hp : 0 < Real.exp (1/lam)+1 := by linarith
  have hm : 0 < Real.exp (1/lam)-1 := by linarith
  rw [pbar_algebra lam mu hlam]
  unfold muHigh muLow
  constructor
  · rw [le_div_iff₀ hm,div_le_iff₀ hp]
    constructor <;> intro h <;> nlinarith only [h]
  · rw [div_le_iff₀ hm,le_div_iff₀ hp]
    constructor <;> intro h <;> nlinarith only [h]

lemma interior_core (lam mu p : ℝ) (hlam : 0 < lam)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (heq : p = (1-mu)*(p/(p+(1-p)*Real.exp (1/lam))) +
      mu*(p*Real.exp (1/lam)/(p*Real.exp (1/lam)+1-p))) :
    p = pBar lam mu := by
  have he := exp_large lam hlam
  have hdg : 0 < p*Real.exp (1/lam)+1-p := by nlinarith [mul_pos hp.1 (Real.exp_pos (1/lam))]
  have hdb : 0 < p+(1-p)*Real.exp (1/lam) := add_pos hp.1 (mul_pos (sub_pos.mpr hp.2) (Real.exp_pos _))
  have hdn := ne_of_gt hdg
  have hbn := ne_of_gt hdb
  field_simp at heq
  have hf : p*(Real.exp (1/lam)-1)*(1-p)*
      (-Real.exp (1/lam)*mu+Real.exp (1/lam)*p-mu-p+1)=0 := by
    linear_combination heq
  have hf' := (mul_eq_zero.mp hf).resolve_left
    (mul_ne_zero (mul_ne_zero hp.1.ne' (sub_pos.mpr he).ne') (sub_pos.mpr hp.2).ne')
  rw [pbar_algebra lam mu hlam]
  apply (eq_div_iff (sub_pos.mpr he).ne').mpr
  nlinarith only [hf']

noncomputable def phi (lam mu p : ℝ) :=
  lam*(mu*Real.log (dg lam p)+(1-mu)*Real.log (db lam p))

lemma phi_lower (lam mu pg pb p : ℝ) (hlam : 0 < lam)
    (hm : mu ∈ Set.Icc (0:ℝ) 1) (ho : IsOptimal lam mu pg pb)
    (hp : p ∈ Set.Ioo (0:ℝ) 1) : phi lam mu p ≤ value lam mu pg pb := by
  obtain ⟨hg,hb,_⟩ := gibbs_facts lam p hp
  have hgm : good lam p ∈ Set.Icc (0:ℝ) 1 := ⟨hg.1.le,hg.2.le⟩
  have hbm : bad lam p ∈ Set.Icc (0:ℝ) 1 := ⟨hb.1.le,hb.2.le⟩
  have hid := value_identity lam mu p (good lam p) (bad lam p) hlam.ne' hp
  rw [score_self,score_self,mul_zero,mul_zero,zero_add,zero_sub] at hid
  have hscore := score_nonpos p (choiceProb mu (good lam p) (bad lam p)) hp
    (choice_bounds mu _ _ hm hgm hbm)
  have hopt := ho.2.2 _ hgm _ hbm
  have hmul := mul_nonpos_of_nonneg_of_nonpos hlam.le hscore
  dsimp [phi]
  linarith only [hid,hopt,hmul]

lemma phi_zero (lam mu : ℝ) (hlam : 0 < lam) : phi lam mu 0 = 1-mu := by
  simp [phi,dg,db,Real.log_exp]
  field_simp
  <;> ring

lemma phi_one (lam mu : ℝ) (hlam : 0 < lam) : phi lam mu 1 = mu := by
  simp [phi,dg,db,Real.log_exp]
  field_simp

lemma phi_deriv (lam mu p : ℝ) (hp : p ∈ Set.Icc (0:ℝ) 1) :
    HasDerivAt (phi lam mu)
      (lam*(mu*(Real.exp (1/lam)-1)/dg lam p+
        (1-mu)*(1-Real.exp (1/lam))/db lam p)) p := by
  have he := Real.exp_pos (1/lam)
  have hdg : 0 < dg lam p := by
    unfold dg
    by_cases h : p=0
    · simp [h]
    · have hpos : 0<p := lt_of_le_of_ne hp.1 (Ne.symm h)
      nlinarith [mul_pos hpos he,hp.2]
  have hdb : 0 < db lam p := by
    unfold db
    by_cases h : p=1
    · simp [h]
    · have hc : 0<1-p := sub_pos.mpr (lt_of_le_of_ne hp.2 h)
      nlinarith [mul_pos hc he,hp.1]
  have hdg' : HasDerivAt (dg lam) (Real.exp (1/lam)-1) p := by
    convert (((hasDerivAt_id p).mul_const (Real.exp (1/lam))).add_const 1).sub (hasDerivAt_id p) using 1 <;> first | rfl | ring
  have hdb' : HasDerivAt (db lam) (1-Real.exp (1/lam)) p := by
    convert (hasDerivAt_id p).add (((hasDerivAt_const p 1).sub (hasDerivAt_id p)).mul_const (Real.exp (1/lam))) using 1 <;> first | rfl | ring
  convert (((hdg'.log hdg.ne').const_mul mu).add ((hdb'.log hdb.ne').const_mul (1-mu))).const_mul lam using 1 <;> first | rfl | ring

lemma right_endpoint_deriv {f : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt f d 0)
    (hm : ∀ x ∈ Set.Ioo (0:ℝ) 1, f x ≤ f 0) : d ≤ 0 := by
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  apply le_of_tendsto ht
  have hlt : ∀ᶠ x in nhdsWithin (0:ℝ) (Set.Ioi 0), x<1 :=
    (eventually_lt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hlt] with x hx h1
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (hm x ⟨hx,h1⟩)) (by simpa using hx.le)

lemma left_endpoint_deriv {f : ℝ → ℝ} {d : ℝ} (hd : HasDerivAt f d 1)
    (hm : ∀ x ∈ Set.Ioo (0:ℝ) 1, f x ≤ f 1) : 0 ≤ d := by
  have ht := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).1
  apply ge_of_tendsto ht
  have hgt : ∀ᶠ x in nhdsWithin (1:ℝ) (Set.Iio 1), 0<x :=
    (eventually_gt_nhds (by norm_num : (0:ℝ)<1)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin,hgt] with x hx h0
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr (hm x ⟨h0,hx⟩)) (sub_nonpos.mpr hx.le)


lemma boundary_necessary (lam mu pg pb : ℝ) (hlam : 0 < lam)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (ho : IsOptimal lam mu pg pb) :
    (choiceProb mu pg pb=0 → mu ≤ muLow lam) ∧
    (choiceProb mu pg pb=1 → muHigh lam ≤ mu) := by
  have hf := conditional_solution lam mu pg pb hlam hmu0 hmu1 ho
  have he := exp_large lam hlam
  have he0 := Real.exp_pos (1/lam)
  have hplus : 0 < Real.exp (1/lam)+1 := by linarith
  have hc : 0 < lam*(Real.exp (1/lam)-1)/Real.exp (1/lam) :=
    div_pos (mul_pos hlam (sub_pos.mpr he)) he0
  constructor
  · intro hp
    have hg : pg=0 ∧ pb=0 := by simpa [hp] using hf
    rcases hg with ⟨rfl,rfl⟩
    have hd := right_endpoint_deriv (phi_deriv lam mu 0 (by simp)) (by
      intro x hx
      rw [phi_zero lam mu hlam]
      have hh := phi_lower lam mu 0 0 x hlam ⟨hmu0.le,hmu1.le⟩ ho hx
      simpa [value,accuracy,cost,choiceProb] using hh)
    simp only [dg,db,zero_mul,zero_add,sub_zero,sub_self,one_mul,div_one] at hd
    have hid : lam*(mu*(Real.exp (1/lam)-1)+(1-mu)*(1-Real.exp (1/lam))/Real.exp (1/lam)) =
        (lam*(Real.exp (1/lam)-1)/Real.exp (1/lam))*(mu*(Real.exp (1/lam)+1)-1) := by
      field_simp
      <;> ring
    rw [hid] at hd
    have hz := nonpos_of_mul_nonpos_right hd hc
    apply (le_div_iff₀ hplus).mpr
    linarith only [hz]
  · intro hp
    have hg : pg=1 ∧ pb=1 := by simpa [hp,Real.exp_ne_zero] using hf
    rcases hg with ⟨rfl,rfl⟩
    have hd := left_endpoint_deriv (phi_deriv lam mu 1 (by simp)) (by
      intro x hx
      rw [phi_one lam mu hlam]
      have hh := phi_lower lam mu 1 1 x hlam ⟨hmu0.le,hmu1.le⟩ ho hx
      simpa [value,accuracy,cost,choiceProb] using hh)
    simp only [dg,db,one_mul,sub_self,mul_zero,add_zero,zero_mul,sub_zero,add_sub_cancel_right,div_one] at hd
    have hid : lam*(mu*(Real.exp (1/lam)-1)/Real.exp (1/lam)+(1-mu)*(1-Real.exp (1/lam))) =
        (lam*(Real.exp (1/lam)-1)/Real.exp (1/lam))*(mu*(Real.exp (1/lam)+1)-Real.exp (1/lam)) := by
      field_simp
      <;> ring
    rw [hid] at hd
    have hz := nonneg_of_mul_nonneg_right hd hc
    apply (div_le_iff₀ hplus).mpr
    linarith only [hz]

lemma choice_closed (lam mu pg pb : ℝ) (hlam : 0 < lam)
    (hmu0 : 0 < mu) (hmu1 : mu < 1) (ho : IsOptimal lam mu pg pb) :
    choiceProb mu pg pb = pClosed lam mu := by
  have hb := boundary_necessary lam mu pg pb hlam hmu0 hmu1 ho
  have hc := choice_bounds mu pg pb ⟨hmu0.le,hmu1.le⟩ ho.1 ho.2.1
  have he := exp_large lam hlam
  have hlowhigh : muLow lam < muHigh lam := by
    unfold muLow muHigh
    exact (div_lt_div_iff_of_pos_right (by positivity)).mpr he
  by_cases hz : choiceProb mu pg pb=0
  · rw [hz,pClosed,if_pos (hb.1 hz)]
  by_cases hu : choiceProb mu pg pb=1
  · have hmu := hb.2 hu
    rw [hu,pClosed,if_neg (by linarith),if_neg (not_lt.mpr hmu)]
  have hp : choiceProb mu pg pb ∈ Set.Ioo (0:ℝ) 1 :=
    ⟨lt_of_le_of_ne hc.1 (Ne.symm hz),lt_of_le_of_ne hc.2 hu⟩
  have hf := conditional_solution lam mu pg pb hlam hmu0 hmu1 ho
  have hfix : choiceProb mu pg pb = (1-mu)*(choiceProb mu pg pb /
      (choiceProb mu pg pb+(1-choiceProb mu pg pb)*Real.exp (1/lam))) +
      mu*(choiceProb mu pg pb*Real.exp (1/lam)/
        (choiceProb mu pg pb*Real.exp (1/lam)+1-choiceProb mu pg pb)) := by
    calc
      _ = (1-mu)*pb+mu*pg := by unfold choiceProb; ring
      _ = _ := by rw [← hf.1,← hf.2]
  have hbar := interior_core lam mu _ hlam hmu0 hmu1 hp hfix
  have hth := pbar_thresholds_core lam hlam mu
  have hlo : muLow lam < mu := by
    by_contra h
    have hh := hth.2.mpr (not_lt.mp h)
    rw [← hbar] at hh
    linarith [hp.1]
  have hhi : mu < muHigh lam := by
    by_contra h
    have hh := hth.1.mpr (not_lt.mp h)
    rw [← hbar] at hh
    linarith [hp.2]
  rw [pClosed,if_neg (not_le.mpr hlo),if_pos hhi]
  exact hbar

lemma pclosed_clip (lam mu : ℝ) (hlam : 0 < lam) :
    pClosed lam mu = max 0 (min 1 (pBar lam mu)) := by
  have ht := pbar_thresholds_core lam hlam mu
  unfold pClosed
  split_ifs with hl hh
  · have hb := ht.2.mpr hl
    rw [min_eq_right (hb.trans zero_le_one),max_eq_left hb]
  · have hb0 : 0 ≤ pBar lam mu := le_of_lt (lt_of_not_ge (fun h => hl (ht.2.mp h)))
    have hb1 : pBar lam mu ≤ 1 := le_of_lt (lt_of_not_ge (fun h => (not_le.mpr hh) (ht.1.mp h)))
    rw [min_eq_right hb1,max_eq_right hb0]
  · have hb1 := ht.1.mpr (not_lt.mp hh)
    rw [min_eq_left hb1,max_eq_right zero_le_one]

lemma pclosed_mono (lam : ℝ) (hlam : 0 < lam) : Monotone (pClosed lam) := by
  intro x y hxy
  rw [pclosed_clip lam x hlam,pclosed_clip lam y hlam]
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  rw [pbar_algebra lam x hlam,pbar_algebra lam y hlam]
  apply (div_le_div_iff_of_pos_right (sub_pos.mpr (exp_large lam hlam))).mpr
  have he : 0 ≤ Real.exp (1/lam)+1 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hxy he]

lemma high_eq_one_sub_low (lam : ℝ) : muHigh lam=1-muLow lam := by
  have he := Real.exp_pos (1/lam)
  unfold muHigh muLow
  field_simp
  <;> ring

lemma low_strict_mono : StrictMonoOn muLow (Set.Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  have hinv : 1/y < 1/x := one_div_lt_one_div_of_lt hx hxy
  have hexp : Real.exp (1/y)+1 < Real.exp (1/x)+1 := by simpa [add_comm] using add_lt_add_right (Real.exp_lt_exp.mpr hinv) 1
  exact one_div_lt_one_div_of_lt (by positivity) hexp

lemma high_strict_anti : StrictAntiOn muHigh (Set.Ioi (0:ℝ)) := by
  intro x hx y hy hxy
  rw [high_eq_one_sub_low,high_eq_one_sub_low]
  exact sub_lt_sub_left (low_strict_mono hx hy hxy) 1

lemma threshold_halves (lam : ℝ) (hlam : 0 < lam) :
    muLow lam < (1/2:ℝ) ∧ (1/2:ℝ) < muHigh lam := by
  have he := exp_large lam hlam
  have hp : 0 < Real.exp (1/lam)+1 := by positivity
  have hl : muLow lam < (1/2:ℝ) := by
    unfold muLow
    apply (div_lt_iff₀ hp).mpr
    linarith
  rw [high_eq_one_sub_low]
  exact ⟨hl,by linarith⟩

lemma theorem_1_core :
    (∀ lam : ℝ, 0 < lam →
      (∀ mu : ℝ, mu ∈ Set.Ioo (0 : ℝ) 1 →
        ∀ pg pb : ℝ, IsOptimal lam mu pg pb → choiceProb mu pg pb = pClosed lam mu) ∧
      muLow lam < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < muHigh lam ∧
      MonotoneOn (pClosed lam) (Set.Ioo (0 : ℝ) 1)) ∧
    StrictMonoOn muLow (Set.Ioi (0 : ℝ)) ∧ StrictAntiOn muHigh (Set.Ioi (0 : ℝ)) := by
  refine ⟨?_,low_strict_mono,high_strict_anti⟩
  intro lam hlam
  exact ⟨fun mu hm pg pb ho => choice_closed lam mu pg pb hlam hm.1 hm.2 ho,
    (threshold_halves lam hlam).1,(threshold_halves lam hlam).2,(pclosed_mono lam hlam).monotoneOn _⟩

lemma accuracy_optimal_pieces (lam mu pg pb : ℝ) (hlam : 0 < lam)
    (hm0 : 0 < mu) (hm1 : mu < 1) (ho : IsOptimal lam mu pg pb) :
    accuracy mu pg pb = if mu ≤ muLow lam then 1-mu else
      if mu < muHigh lam then muHigh lam else mu := by
  have hf := conditional_solution lam mu pg pb hlam hm0 hm1 ho
  have hc := choice_closed lam mu pg pb hlam hm0 hm1 ho
  by_cases hl : mu ≤ muLow lam
  · have hp : choiceProb mu pg pb=0 := by simpa [pClosed,hl] using hc
    have hg : pg=0 ∧ pb=0 := by simpa [hp] using hf
    simp [hl,accuracy,hg.1,hg.2]
  rw [if_neg hl]
  by_cases hh : mu < muHigh lam
  · rw [if_pos hh]
    have hp : choiceProb mu pg pb=pBar lam mu := by simpa [pClosed,hl,hh] using hc
    let p := choiceProb mu pg pb
    have he := exp_large lam hlam
    have he0 := Real.exp_pos (1/lam)
    have hp' : p=(mu*(Real.exp (1/lam)+1)-1)/(Real.exp (1/lam)-1) := hp.trans (pbar_algebra lam mu hlam)
    have hline : p*(Real.exp (1/lam)-1)=mu*(Real.exp (1/lam)+1)-1 :=
      (eq_div_iff (sub_pos.mpr he).ne').mp hp'
    have hgden : p*Real.exp (1/lam)+1-p = mu*(Real.exp (1/lam)+1) := by nlinarith only [hline]
    have hbden : p+(1-p)*Real.exp (1/lam) = (1-mu)*(Real.exp (1/lam)+1) := by nlinarith only [hline]
    change pg=p*Real.exp (1/lam)/(p*Real.exp (1/lam)+1-p) ∧ pb=p/(p+(1-p)*Real.exp (1/lam)) at hf
    rw [hgden,hbden] at hf
    unfold accuracy muHigh
    rw [hf.1,hf.2]
    have hm : 1-mu≠0 := (sub_pos.mpr hm1).ne'
    have hn := hm0.ne'
    have heplus : Real.exp (1/lam)+1≠0 := ne_of_gt (by positivity)
    field_simp
    nlinarith only [hline]
  · rw [if_neg hh]
    have hp : choiceProb mu pg pb=1 := by simpa [pClosed,hl,hh] using hc
    have hg : pg=1 ∧ pb=1 := by simpa [hp,Real.exp_ne_zero] using hf
    simp [accuracy,hg.1,hg.2]

lemma optimum_exists (lam mu : ℝ) : ∃ q : ℝ × ℝ, IsOptimal lam mu q.1 q.2 := by
  have hc : Continuous (fun q : ℝ × ℝ => value lam mu q.1 q.2) := by
    unfold value accuracy cost choiceProb
    fun_prop
  obtain ⟨q,hq,hm⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
    (show (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1).Nonempty from ⟨(0,0),by simp⟩)
    hc.continuousOn
  refine ⟨q,hq.1,hq.2,?_⟩
  intro pg hpg pb hpb
  exact hm (show (pg,pb) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 from ⟨hpg,hpb⟩)

lemma chosen_optimal (lam mu : ℝ) : IsOptimal lam mu
    (HumanMachine.Accuracy.optPair lam mu).1 (HumanMachine.Accuracy.optPair lam mu).2 :=
  Classical.epsilon_spec (optimum_exists lam mu)

lemma astar_zero (lam : ℝ) : HumanMachine.Accuracy.AStar lam 0=1 := by
  have ho := chosen_optimal lam 0
  have hh := ho.2.2 0 (by simp) 0 (by simp)
  simp [value,accuracy,cost,choiceProb] at hh
  unfold HumanMachine.Accuracy.AStar accuracy
  simp only [zero_mul,sub_zero,one_mul,zero_add]
  linarith [ho.2.1.1]

lemma astar_one (lam : ℝ) : HumanMachine.Accuracy.AStar lam 1=1 := by
  have ho := chosen_optimal lam 1
  have hh := ho.2.2 1 (by simp) 1 (by simp)
  simp [value,accuracy,cost,choiceProb] at hh
  unfold HumanMachine.Accuracy.AStar accuracy
  simp only [one_mul,sub_self,zero_mul,add_zero]
  linarith [ho.1.2]

lemma astar_max (lam mu : ℝ) (hlam : 0 < lam) (hm : mu ∈ Set.Icc (0:ℝ) 1) :
    HumanMachine.Accuracy.AStar lam mu = max (1-mu) (max mu (muHigh lam)) := by
  have he0 := Real.exp_pos (1/lam)
  have hlow0 : 0 < muLow lam := by unfold muLow; positivity
  have hhigh1 : muHigh lam<1 := by rw [high_eq_one_sub_low]; linarith
  have hhalves := threshold_halves lam hlam
  by_cases h0 : mu=0
  · subst mu
    rw [astar_zero]
    simp only [sub_zero]
    rw [max_eq_right (by linarith : (0:ℝ)≤ muHigh lam),max_eq_left hhigh1.le]
  by_cases h1 : mu=1
  · subst mu
    rw [astar_one]
    simp [max_eq_left hhigh1.le]
  have hm0 : 0< mu := lt_of_le_of_ne hm.1 (Ne.symm h0)
  have hm1 : mu<1 := lt_of_le_of_ne hm.2 h1
  have ha := accuracy_optimal_pieces lam mu _ _ hlam hm0 hm1 (chosen_optimal lam mu)
  change HumanMachine.Accuracy.AStar lam mu = _ at ha
  rw [ha]
  have hs := high_eq_one_sub_low lam
  split_ifs with hl hh
  · rw [max_eq_left (show max mu (muHigh lam) ≤ 1-mu from max_le (by linarith [hhalves.1]) (by linarith))]
  · rw [max_eq_right hh.le,max_eq_right (by linarith : 1-mu≤ muHigh lam)]
  · rw [max_eq_left (not_lt.mp hh),max_eq_right (by linarith [hhalves.2] : 1-mu≤ mu)]

lemma astar_convex_core (lam : ℝ) (hlam : 0 < lam) :
    ConvexOn ℝ (Set.Icc (0:ℝ) 1) (HumanMachine.Accuracy.AStar lam) := by
  have hlin : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun mu : ℝ => 1-mu) := by
    refine ⟨convex_Icc _ _,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    nlinarith only [hab]
  have hid : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun mu : ℝ => mu) := convexOn_id (convex_Icc _ _)
  have hconst : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (fun _ : ℝ => muHigh lam) := convexOn_const _ (convex_Icc _ _)
  exact (hlin.sup (hid.sup hconst)).congr (fun mu hm => (astar_max lam mu hlam hm).symm)

lemma corollary_2_accuracy_core (lam μ : ℝ) (hlam : 0 < lam) (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    (μ ≤ muLow lam → HumanMachine.Accuracy.AStar lam μ = 1-μ) ∧
      (muLow lam < μ → μ < muHigh lam →
        HumanMachine.Accuracy.AStar lam μ = Real.exp (1/lam)/(Real.exp (1/lam)+1)) ∧
      (muHigh lam ≤ μ → HumanMachine.Accuracy.AStar lam μ = μ) := by
  rw [astar_max lam μ hlam hμ]
  have hhalves := threshold_halves lam hlam
  have hs := high_eq_one_sub_low lam
  refine ⟨?_,?_,?_⟩
  · intro h
    exact max_eq_left (max_le (by linarith [hhalves.1]) (by linarith))
  · intro hlo hhi
    rw [max_eq_right hhi.le,max_eq_right (by linarith : 1-μ ≤ muHigh lam)]
    rfl
  · intro h
    rw [max_eq_left h,max_eq_right (by linarith [hhalves.2] : 1-μ ≤ μ)]
end HumanMachineOptimizer





open HumanMachine.Alone

theorem solution (lam : ℝ) (hlam : 0 < lam) :
    ∀ mu : ℝ, (1 ≤ pBar lam mu ↔ muHigh lam ≤ mu) ∧
      (pBar lam mu ≤ 0 ↔ mu ≤ muLow lam) := by exact HumanMachineOptimizer.pbar_thresholds_core lam hlam


#print axioms solution
