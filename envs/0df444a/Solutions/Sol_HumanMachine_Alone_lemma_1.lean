-- Prove2me | solution 1 for HumanMachine.Alone.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-17T08:02:05.304641+00:00
-- url     : https://prove2.me/submissions/ee83903c-c0dd-4bcd-8f30-9878c15b2947

import Mathlib
import Definitions.Def_HumanMachine_Alone_model

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
theorem solution (lam mu pg pb : ℝ) (hlam : 0 < lam)
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

#print axioms solution
