-- Prove2me | solution 1 for KumarSeidman.TwoType.example2_unstable_trajectory_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-11T20:46:24.504685+00:00
-- url     : https://prove2.me/submissions/b878b948-b444-469f-8610-e2341673f204

import Mathlib
import Definitions.Def_KumarSeidman_TwoType_Example2

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace KSHalf

/-! ## Part A: the abstract half-cycle (pure real algebra) -/

/-- `clip u α β = ∫_0^u 1_{[α,β)}` for `0 ≤ α ≤ β`, `0 ≤ u`. -/
def clip (u α β : ℝ) : ℝ := min (max u α) β - α

lemma clip_lo {u α β : ℝ} (hu : u ≤ α) (hab : α ≤ β) : clip u α β = 0 := by
  unfold clip; rw [max_eq_right hu, min_eq_left hab]; ring

lemma clip_mid {u α β : ℝ} (h1 : α ≤ u) (h2 : u ≤ β) : clip u α β = u - α := by
  unfold clip; rw [max_eq_left h1, min_eq_left h2]

lemma clip_hi {u α β : ℝ} (hab : α ≤ β) (hu : β ≤ u) : clip u α β = β - α := by
  unfold clip; rw [max_eq_left (hab.trans hu), min_eq_right hu]

/-- Parameters of a half-cycle in role order `a, b, c, d`. -/
structure HP where
  ta : ℝ
  tb : ℝ
  tc : ℝ
  td : ℝ
  da : ℝ
  db : ℝ
  dc : ℝ
  dd : ℝ

namespace HP

variable (P : HP)

def mirror : HP := ⟨P.tc, P.td, P.ta, P.tb, P.dc, P.dd, P.da, P.db⟩

structure Ok : Prop where
  hta : 0 < P.ta
  htb : 0 < P.tb
  htc : 0 < P.tc
  htd : 0 < P.td
  hda : 0 < P.da
  hdb : 0 < P.db
  hdc : 0 < P.dc
  hdd : 0 < P.dd
  had : P.ta + P.td < 1
  hbc : P.tb + P.tc < 1
  hbd : 1 < P.tb + P.td

lemma Ok.mirror {P : HP} (h : P.Ok) : P.mirror.Ok where
  hta := h.htc
  htb := h.htd
  htc := h.hta
  htd := h.htb
  hda := h.hdc
  hdb := h.hdd
  hdc := h.hda
  hdd := h.hdb
  had := by simp only [HP.mirror]; linarith [h.hbc]
  hbc := by simp only [HP.mirror]; linarith [h.had]
  hbd := by simp only [HP.mirror]; linarith [h.hbd]

lemma mirror_mirror : P.mirror.mirror = P := by
  cases P; rfl

def c1 : ℝ := P.dd + P.td * P.da + P.da
def u2 (A : ℝ) : ℝ := P.ta * A / (1 - P.ta)
def u3 (A : ℝ) : ℝ := P.u2 A + P.dd
def u4 (A : ℝ) : ℝ := P.u3 A + P.td * P.da
def u5 (A : ℝ) : ℝ := P.u4 A + P.da
def u6 (A : ℝ) : ℝ := P.u5 A + P.ta * P.c1 / (1 - P.ta)
def u7 (A : ℝ) : ℝ := (P.tb * A + P.db) / (1 - P.tb)
def u8 (A : ℝ) : ℝ := P.u7 A + P.dc

/-- cumulative outputs within the half (relative time `u`) -/
def Ra (A u : ℝ) : ℝ :=
  clip u 0 (P.u2 A) / P.ta + clip u (P.u5 A) (P.u6 A) / P.ta + clip u (P.u6 A) (P.u8 A)
def Rb (A u : ℝ) : ℝ := clip u P.db (P.u7 A) / P.tb
def Rd (A u : ℝ) : ℝ := clip u (P.u3 A) (P.u4 A) / P.td

/-- levels within the half -/
def La (A u : ℝ) : ℝ := A + u - P.Ra A u
def Lb (A u : ℝ) : ℝ := P.Ra A u - P.Rb A u
def Ld (A u : ℝ) : ℝ := P.da - P.Rd A u

def Valid (A : ℝ) : Prop :=
  0 < A ∧ P.db ≤ P.u2 A ∧ P.c1 / P.tb < P.u2 A / P.ta - (P.u2 A - P.db) / P.tb ∧
    P.u6 A ≤ P.u7 A

variable {P}

section basic
variable (h : P.Ok)
include h

lemma ta_lt_tb : P.ta < P.tb := by linarith [h.had, h.hbd]
lemma ta_lt_one : P.ta < 1 := by linarith [h.had, h.htd]
lemma tb_lt_one : P.tb < 1 := by linarith [h.hbc, h.htc]
lemma td_lt_one : P.td < 1 := by linarith [h.had, h.hta]
lemma c1_pos : 0 < P.c1 := by
  unfold c1; have := mul_pos h.htd h.hda; linarith [h.hdd, h.hda]

lemma u2_mul (A : ℝ) : P.u2 A * (1 - P.ta) = P.ta * A := by
  have h1 : (1 - P.ta) ≠ 0 := by linarith [ta_lt_one h]
  unfold u2; field_simp

lemma u7_mul (A : ℝ) : P.u7 A * (1 - P.tb) = P.tb * A + P.db := by
  have h1 : (1 - P.tb) ≠ 0 := by linarith [tb_lt_one h]
  unfold u7; field_simp

lemma u65_mul (A : ℝ) : (P.u6 A - P.u5 A) * (1 - P.ta) = P.ta * P.c1 := by
  have h1 : (1 - P.ta) ≠ 0 := by linarith [ta_lt_one h]
  unfold u6; field_simp; ring

lemma u5_sub (A : ℝ) : P.u5 A - P.u2 A = P.c1 := by
  unfold u5 u4 u3 c1; ring

lemma u6_eq (A : ℝ) : P.u6 A = (P.ta * A + P.c1) / (1 - P.ta) := by
  have h1 : (1 - P.ta) ≠ 0 := by linarith [ta_lt_one h]
  unfold u6 u5 u4 u3 u2 c1; field_simp; ring

/-- Validity for all large `A`. -/
lemma valid_of_large {A : ℝ} (h1 : P.db < A * P.ta) (h2 : P.c1 < A * (P.tb - P.ta)) :
    P.Valid A := by
  have hta := h.hta; have htb := h.htb
  have hta1 := ta_lt_one h; have htb1 := tb_lt_one h; have hab := ta_lt_tb h
  have hc := c1_pos h
  have hA : 0 < A := by
    by_contra hA; push_neg at hA; nlinarith
  have hu2 := u2_mul h A
  have hu2' : A * P.ta ≤ P.u2 A := by
    have : 0 ≤ A * P.ta * P.ta := by positivity
    nlinarith
  refine ⟨hA, by linarith, ?_, ?_⟩
  · -- c1/tb < u2/ta - (u2-db)/tb
    have e : P.u2 A / P.ta - (P.u2 A - P.db) / P.tb - P.c1 / P.tb
        = (P.u2 A * (P.tb - P.ta) + P.ta * P.db - P.ta * P.c1) / (P.ta * P.tb) := by
      field_simp; ring
    have hpos : 0 < P.u2 A * (P.tb - P.ta) + P.ta * P.db - P.ta * P.c1 := by
      have k1 : A * P.ta * (P.tb - P.ta) ≤ P.u2 A * (P.tb - P.ta) :=
        mul_le_mul_of_nonneg_right hu2' (sub_nonneg.2 hab.le)
      have k2 : P.ta * P.c1 < P.ta * (A * (P.tb - P.ta)) := mul_lt_mul_of_pos_left h2 hta
      nlinarith [mul_pos hta h.hdb]
    have : 0 < (P.u2 A * (P.tb - P.ta) + P.ta * P.db - P.ta * P.c1) / (P.ta * P.tb) := by
      positivity
    linarith
  · rw [u6_eq h, div_le_iff₀ (by linarith)]
    have hu7 := u7_mul h A
    have hu7pos : 0 < P.u7 A := by
      unfold u7; apply div_pos; nlinarith [h.hdb]; linarith
    have : P.u7 A * (1 - P.ta) = P.u7 A * (1 - P.tb) + P.u7 A * (P.tb - P.ta) := by ring
    nlinarith [mul_pos hu7pos (sub_pos.2 hab), h.hdb]

lemma inv_ta_gt_one : 1 < P.ta⁻¹ := by
  rw [lt_inv_comm₀ one_pos h.hta]; simpa using ta_lt_one h

lemma inv_tb_gt_one : 1 < P.tb⁻¹ := by
  rw [lt_inv_comm₀ one_pos h.htb]; simpa using tb_lt_one h

lemma inv_tb_lt_inv_ta : P.tb⁻¹ < P.ta⁻¹ := (inv_lt_inv₀ h.htb h.hta).2 (ta_lt_tb h)

end basic

end HP


namespace HP
variable {P : HP}

section levels
variable (h : P.Ok) {A : ℝ} (hv : P.Valid A)
include h hv

lemma ord : 0 < P.u2 A ∧ P.u2 A < P.u3 A ∧ P.u3 A < P.u4 A ∧ P.u4 A < P.u5 A ∧
    P.u5 A < P.u6 A ∧ P.u6 A ≤ P.u7 A ∧ P.u7 A < P.u8 A := by
  have hta1 := ta_lt_one h
  have hu2 := u2_mul h A
  have hc := c1_pos h
  refine ⟨?_, ?_, ?_, ?_, ?_, hv.2.2.2, ?_⟩
  · by_contra hn; push_neg at hn
    have : 0 < P.ta * A := mul_pos h.hta hv.1
    nlinarith
  · unfold u3; linarith [h.hdd]
  · unfold u4; nlinarith [mul_pos h.htd h.hda]
  · unfold u5; linarith [h.hda]
  · unfold u6
    have : 0 < P.ta * P.c1 / (1 - P.ta) := by
      apply div_pos (mul_pos h.hta hc); linarith
    linarith
  · unfold u8; linarith [h.hdc]

lemma A_eq : A = P.u2 A / P.ta - P.u2 A := by
  have := u2_mul h A
  have ht : P.ta ≠ 0 := h.hta.ne'
  field_simp; linarith

lemma c1_eq : P.c1 = (P.u6 A - P.u5 A) / P.ta - (P.u6 A - P.u5 A) := by
  have := u65_mul h A
  have ht : P.ta ≠ 0 := h.hta.ne'
  field_simp; linarith

lemma u7_eq : (P.u7 A - P.db) / P.tb = A + P.u7 A := by
  have := u7_mul h A
  have ht : P.tb ≠ 0 := h.htb.ne'
  field_simp; linarith

/-- `Ra` on the four regions. -/
lemma Ra_r1 {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ P.u2 A) : P.Ra A u = u / P.ta := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Ra
  rw [clip_mid h0 h1, clip_lo (by linarith) o6.le, clip_lo (by linarith) (by linarith)]
  ring

lemma Ra_r2 {u : ℝ} (h1 : P.u2 A ≤ u) (h2 : u ≤ P.u5 A) : P.Ra A u = P.u2 A / P.ta := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Ra
  rw [clip_hi o2.le h1, clip_lo h2 o6.le, clip_lo (by linarith) (by linarith)]
  ring

lemma Ra_r3 {u : ℝ} (h1 : P.u5 A ≤ u) (h2 : u ≤ P.u6 A) :
    P.Ra A u = P.u2 A / P.ta + (u - P.u5 A) / P.ta := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Ra
  rw [clip_hi o2.le (by linarith), clip_mid h1 h2, clip_lo h2 (by linarith)]
  ring

lemma Ra_r4 {u : ℝ} (h1 : P.u6 A ≤ u) (h2 : u ≤ P.u8 A) :
    P.Ra A u = P.u2 A / P.ta + (P.u6 A - P.u5 A) / P.ta + (u - P.u6 A) := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Ra
  rw [clip_hi o2.le (by linarith), clip_hi o6.le h1, clip_mid h1 h2]
  ring

lemma La_zero0 : P.La A 0 = A := by
  obtain ⟨o2, -⟩ := ord h hv
  unfold La; rw [Ra_r1 h hv le_rfl o2.le]; ring

lemma La_pos1 {u : ℝ} (h0 : 0 ≤ u) (h1 : u < P.u2 A) : 0 < P.La A u := by
  unfold La; rw [Ra_r1 h hv h0 h1.le]
  have e := A_eq h hv
  have k := inv_ta_gt_one h
  simp only [div_eq_mul_inv] at e ⊢
  nlinarith [mul_pos (sub_pos.2 h1) (sub_pos.2 k)]

lemma La_pos2 {u : ℝ} (h1 : P.u2 A < u) (h2 : u < P.u6 A) : 0 < P.La A u := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  have e := A_eq h hv
  have e2 := c1_eq h hv
  have e3 := u5_sub h A
  have k := inv_ta_gt_one h
  unfold La
  rcases le_total u (P.u5 A) with hu | hu
  · rw [Ra_r2 h hv h1.le hu]; linarith
  · rw [Ra_r3 h hv hu h2.le]
    simp only [div_eq_mul_inv] at e e2 ⊢
    nlinarith [mul_pos (sub_pos.2 h2) (sub_pos.2 k)]

lemma La_zero {u : ℝ} (h1 : P.u6 A ≤ u) (h2 : u ≤ P.u8 A) : P.La A u = 0 := by
  have e := A_eq h hv
  have e2 := c1_eq h hv
  have e3 := u5_sub h A
  unfold La; rw [Ra_r4 h hv h1 h2]; linarith

lemma La_nonneg {u : ℝ} (h0 : 0 ≤ u) (h2 : u ≤ P.u8 A) : 0 ≤ P.La A u := by
  rcases lt_or_ge u (P.u2 A) with a | a
  · exact (La_pos1 h hv h0 a).le
  rcases eq_or_lt_of_le a with a | a
  · subst a; unfold La; rw [Ra_r1 h hv (ord h hv).1.le le_rfl]
    have e := A_eq h hv; linarith
  rcases lt_or_ge u (P.u6 A) with b | b
  · exact (La_pos2 h hv a b).le
  · exact (La_zero h hv b h2).ge

lemma Lb_pos {u : ℝ} (h0 : 0 < u) (h7 : u < P.u7 A) : 0 < P.Lb A u := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  have hv3 := hv.2.2.1
  have hdb := hv.2.1
  have e := A_eq h hv
  have e3 := u5_sub h A
  have e7 := u7_eq h hv
  have kab := inv_tb_lt_inv_ta h
  have ktb := inv_tb_gt_one h
  have htbi : 0 < P.tb⁻¹ := inv_pos.2 h.htb
  unfold Lb Rb
  rcases le_total u P.db with a | a
  · rw [Ra_r1 h hv h0.le (a.trans hdb), clip_lo a (by linarith)]
    have := div_pos h0 h.hta; simpa using this
  rw [clip_mid a h7.le]
  rcases le_total u (P.u2 A) with b | b
  · rw [Ra_r1 h hv h0.le b]
    simp only [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left kab.le h0.le, mul_pos h.hdb htbi]
  rcases le_total u (P.u5 A) with c | c
  · rw [Ra_r2 h hv b c]
    rw [← e3] at hv3
    simp only [div_eq_mul_inv] at hv3 ⊢
    nlinarith [mul_le_mul_of_nonneg_right c htbi.le]
  rcases le_total u (P.u6 A) with d | d
  · rw [Ra_r3 h hv c d]
    rw [← e3] at hv3
    simp only [div_eq_mul_inv] at hv3 ⊢
    nlinarith [mul_le_mul_of_nonneg_left (sub_nonneg.2 c) (sub_pos.2 kab).le]
  · have hz := La_zero h hv d (by linarith)
    unfold La at hz
    have hRa : P.Ra A u = A + u := by linarith
    rw [hRa]
    simp only [div_eq_mul_inv] at e7 ⊢
    nlinarith [mul_pos (sub_pos.2 h7) (sub_pos.2 ktb)]

lemma Lb_hi {u : ℝ} (h1 : P.u7 A ≤ u) (h2 : u ≤ P.u8 A) : P.Lb A u = u - P.u7 A := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  have hz := La_zero h hv (by linarith) h2
  have e7 := u7_eq h hv
  unfold La at hz
  unfold Lb Rb
  rw [clip_hi (by linarith [hv.2.1]) h1]
  linarith

lemma Lb_zero0 : P.Lb A 0 = 0 := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Lb Rb; rw [Ra_r1 h hv le_rfl o2.le, clip_lo h.hdb.le (by linarith [hv.2.1])]; ring

lemma Lb_nonneg {u : ℝ} (h0 : 0 ≤ u) (h2 : u ≤ P.u8 A) : 0 ≤ P.Lb A u := by
  rcases eq_or_lt_of_le h0 with a | a
  · subst a; rw [Lb_zero0 h hv]
  rcases lt_or_ge u (P.u7 A) with b | b
  · exact (Lb_pos h hv a b).le
  · rw [Lb_hi h hv b h2]; linarith

lemma Ld_lo {u : ℝ} (h1 : u ≤ P.u3 A) : P.Ld A u = P.da := by
  obtain ⟨o2, o3, o4, -⟩ := ord h hv
  unfold Ld Rd; rw [clip_lo h1 o4.le]; ring

lemma Ld_pos {u : ℝ} (h1 : u < P.u4 A) : 0 < P.Ld A u := by
  obtain ⟨o2, o3, o4, -⟩ := ord h hv
  rcases le_total u (P.u3 A) with a | a
  · rw [Ld_lo h hv a]; exact h.hda
  unfold Ld Rd; rw [clip_mid a h1.le]
  have e : P.u4 A - P.u3 A = P.td * P.da := by unfold u4; ring
  have : (u - P.u3 A) / P.td < P.da := by
    rw [div_lt_iff₀ h.htd]; linarith
  linarith

lemma Ld_hi {u : ℝ} (h1 : P.u4 A ≤ u) : P.Ld A u = 0 := by
  obtain ⟨o2, o3, o4, -⟩ := ord h hv
  unfold Ld Rd; rw [clip_hi o4.le h1]
  have e : P.u4 A - P.u3 A = P.td * P.da := by unfold u4; ring
  rw [e]; field_simp [h.htd.ne']; ring

lemma Ld_nonneg (u : ℝ) : 0 ≤ P.Ld A u := by
  rcases lt_or_ge u (P.u4 A) with a | a
  · exact (Ld_pos h hv a).le
  · rw [Ld_hi h hv a]

end levels

end HP

end KSHalf

/-! ## Part B: rates as right derivatives; FTC -/

namespace KSHalf
open MeasureTheory Set

def ind (α β u : ℝ) : ℝ := if α ≤ u ∧ u < β then 1 else 0

lemma ind_nonneg (α β u : ℝ) : 0 ≤ ind α β u := by unfold ind; split_ifs <;> norm_num
lemma ind_le_one (α β u : ℝ) : ind α β u ≤ 1 := by unfold ind; split_ifs <;> norm_num

lemma ind_measurable (α β : ℝ) : Measurable (ind α β) := by
  unfold ind
  exact Measurable.ite (measurableSet_Ico (a := α) (b := β)) measurable_const measurable_const

lemma clip_cont (α β : ℝ) : Continuous (fun u => clip u α β) := by
  unfold clip; fun_prop

lemma clip_hasDerivWithinAt {α β : ℝ} (hab : α ≤ β) (x : ℝ) :
    HasDerivWithinAt (fun u => clip u α β) (ind α β x) (Ioi x) x := by
  unfold ind
  split_ifs with hx
  · have hd : HasDerivWithinAt (fun u => u - α) 1 (Ioi x) x :=
      ((hasDerivAt_id x).sub_const α).hasDerivWithinAt
    apply hd.congr_of_eventuallyEq
    · filter_upwards [Ioo_mem_nhdsGT hx.2] with u hu
      exact clip_mid (hx.1.trans hu.1.le) hu.2.le
    · exact clip_mid hx.1 hx.2.le
  · push_neg at hx
    rcases lt_or_ge x α with h1 | h1
    · apply (hasDerivWithinAt_const x (Ioi x) (0:ℝ)).congr_of_eventuallyEq
      · filter_upwards [Ioo_mem_nhdsGT h1] with u hu
        exact clip_lo hu.2.le hab
      · exact clip_lo h1.le hab
    · have h2 := hx h1
      apply (hasDerivWithinAt_const x (Ioi x) (β - α)).congr_of_eventuallyEq
      · filter_upwards [self_mem_nhdsWithin] with u hu
        exact clip_hi hab (h2.trans (le_of_lt hu))
      · exact clip_hi hab h2

lemma shift_deriv {f : ℝ → ℝ} {f' x G : ℝ}
    (h : HasDerivWithinAt f f' (Ioi (x - G)) (x - G)) :
    HasDerivWithinAt (fun σ => f (σ - G)) f' (Ioi x) x := by
  have h2 : HasDerivWithinAt (fun σ => σ - G) 1 (Ioi x) x :=
    ((hasDerivAt_id x).sub_const G).hasDerivWithinAt
  have := h.comp x h2 (fun y hy => by simp only [mem_Ioi] at hy ⊢; linarith)
  rw [mul_one] at this
  exact this

/-- FTC for a bounded measurable right derivative. -/
lemma ftc {f r : ℝ → ℝ} {a b C : ℝ} (hab : a ≤ b) (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ico a b, HasDerivWithinAt f (r x) (Ioi x) x) (hm : Measurable r)
    (hB : ∀ x, |r x| ≤ C) : ∫ x in a..b, r x = f b - f a := by
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hc
  · intro x hx; exact hd x ⟨hx.1.le, hx.2⟩
  · apply (intervalIntegrable_const (c := C)).mono_fun hm.aestronglyMeasurable
    filter_upwards with x
    simp only [Real.norm_eq_abs]
    exact (hB x).trans (le_abs_self C)

namespace HP
variable (P : HP)

/-- output rates within the half -/
def ra (A u : ℝ) : ℝ :=
  ind 0 (P.u2 A) u / P.ta + ind (P.u5 A) (P.u6 A) u / P.ta + ind (P.u6 A) (P.u8 A) u
def rb (A u : ℝ) : ℝ := ind P.db (P.u7 A) u / P.tb
def rd (A u : ℝ) : ℝ := ind (P.u3 A) (P.u4 A) u / P.td

variable {P}

section derivs
variable (h : P.Ok) {A : ℝ} (hv : P.Valid A)
include h hv

lemma Ra_deriv (x : ℝ) : HasDerivWithinAt (P.Ra A) (P.ra A x) (Ioi x) x := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Ra ra
  exact (((clip_hasDerivWithinAt o2.le x).div_const _).add
    ((clip_hasDerivWithinAt o6.le x).div_const _)).add (clip_hasDerivWithinAt (by linarith) x)

lemma Rb_deriv (x : ℝ) : HasDerivWithinAt (P.Rb A) (P.rb A x) (Ioi x) x := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Rb rb
  exact (clip_hasDerivWithinAt (by linarith [hv.2.1]) x).div_const _

lemma Rd_deriv (x : ℝ) : HasDerivWithinAt (P.Rd A) (P.rd A x) (Ioi x) x := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv
  unfold Rd rd
  exact (clip_hasDerivWithinAt o4.le x).div_const _

end derivs

lemma Ra_cont (A : ℝ) : Continuous (P.Ra A) := by
  unfold Ra; have := clip_cont; fun_prop
lemma Rb_cont (A : ℝ) : Continuous (P.Rb A) := by
  unfold Rb; have := clip_cont; fun_prop
lemma Rd_cont (A : ℝ) : Continuous (P.Rd A) := by
  unfold Rd; have := clip_cont; fun_prop

end HP

end KSHalf

/-! ## Part C: the sequence of halves -/

namespace KSHalf
open Filter

namespace HP
variable {P : HP}

def cn (P : HP) : ℝ := P.tb / (1 - P.tb)
def K (P : HP) : ℝ := max (P.db / P.ta) (P.c1 / (P.tb - P.ta)) + 1

lemma cn_pos (h : P.Ok) : 0 < P.cn := div_pos h.htb (by linarith [tb_lt_one h])

lemma K_pos (h : P.Ok) : 0 < P.K := by
  unfold K
  have : 0 < P.db / P.ta := div_pos h.hdb h.hta
  have := le_max_left (P.db / P.ta) (P.c1 / (P.tb - P.ta))
  linarith

lemma valid_of_ge (h : P.Ok) {A : ℝ} (hA : P.K ≤ A) : P.Valid A := by
  have hab := ta_lt_tb h
  apply valid_of_large h
  · have h1 : P.db / P.ta < A := by
      have := le_max_left (P.db / P.ta) (P.c1 / (P.tb - P.ta)); unfold K at hA; linarith
    rw [div_lt_iff₀ h.hta] at h1; linarith
  · have h1 : P.c1 / (P.tb - P.ta) < A := by
      have := le_max_right (P.db / P.ta) (P.c1 / (P.tb - P.ta)); unfold K at hA; linarith
    rw [div_lt_iff₀ (sub_pos.2 hab)] at h1; linarith

lemma u8_ge (h : P.Ok) (A : ℝ) : P.cn * A ≤ P.u8 A := by
  have htb1 := tb_lt_one h
  have hu7 := u7_mul h A
  unfold cn u8
  rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
  nlinarith [mul_pos h.hdc (sub_pos.2 htb1), h.hdb]

lemma u7_pos (h : P.Ok) {A : ℝ} (hv : P.Valid A) : 0 < P.u7 A := by
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := ord h hv; linarith

lemma u8_gt (h : P.Ok) {A : ℝ} (hv : P.Valid A) : P.dc < P.u8 A := by
  have := u7_pos h hv; unfold u8; linarith

end HP

namespace Seq
variable (P0 : HP)

/-- half `n` uses the mirror parameters when `n` is even, the normal ones when odd -/
def par (n : ℕ) : HP := if n % 2 = 0 then P0.mirror else P0

lemma par_even (k : ℕ) : par P0 (2 * k) = P0.mirror := by unfold par; simp
lemma par_odd (k : ℕ) : par P0 (2 * k + 1) = P0 := by unfold par; simp [Nat.add_mod]

lemma par_ok {P0 : HP} (h : P0.Ok) (n : ℕ) : (par P0 n).Ok := by
  unfold par; split_ifs
  · exact h.mirror
  · exact h

/-- the size parameter `A_n` of half `n` -/
def A (A0 : ℝ) : ℕ → ℝ
  | 0 => A0
  | n + 1 => (par P0 n).u8 (A A0 n)

/-- global start time of half `n` -/
def G (A0 : ℝ) : ℕ → ℝ
  | 0 => -(par P0 0).u7 A0
  | n + 1 => G A0 n + (par P0 n).u8 (A P0 A0 n)

lemma A_zero (A0 : ℝ) : A P0 A0 0 = A0 := rfl
lemma A_succ (A0 : ℝ) (n : ℕ) : A P0 A0 (n + 1) = (par P0 n).u8 (A P0 A0 n) := rfl
lemma G_zero (A0 : ℝ) : G P0 A0 0 = -(par P0 0).u7 A0 := rfl
lemma G_succ (A0 : ℝ) (n : ℕ) : G P0 A0 (n + 1) = G P0 A0 n + (par P0 n).u8 (A P0 A0 n) := rfl

def Mo : ℝ := max P0.K (P0.mirror.K / P0.cn)
def Me : ℝ := P0.cn * Mo P0
def dmin : ℝ := min P0.da P0.dc

/-- the threshold on `ξ` -/
def xi0 : ℝ := (P0.td * Me P0 + P0.dd) / (1 - P0.td)
/-- the initial size parameter for a given `ξ` (so that `u7` of half 0 equals `ξ`) -/
def A0of (ξ : ℝ) : ℝ := ((1 - P0.td) * ξ - P0.dd) / P0.td

section consts
variable {P0} (h : P0.Ok)
include h

lemma lam_ge : 1 ≤ P0.mirror.cn * P0.cn := by
  have h2 := HP.tb_lt_one h
  have h4 := HP.td_lt_one h
  unfold HP.cn HP.mirror
  simp only
  rw [div_mul_div_comm, le_div_iff₀ (mul_pos (by linarith) (by linarith))]
  nlinarith [h.hbd]

lemma Mo_pos : 0 < Mo P0 := lt_of_lt_of_le (HP.K_pos h) (le_max_left _ _)

lemma Me_pos : 0 < Me P0 := mul_pos (HP.cn_pos h) (Mo_pos h)

lemma dmin_pos : 0 < dmin P0 := lt_min h.hda h.hdc

lemma par_dc_ge (n : ℕ) : dmin P0 ≤ (par P0 n).dc := by
  unfold par dmin; split_ifs
  · exact min_le_left _ _
  · exact min_le_right _ _

lemma A0of_ge {ξ : ℝ} (hξ : xi0 P0 ≤ ξ) : Me P0 ≤ A0of P0 ξ := by
  have h4 := HP.td_lt_one h
  unfold xi0 at hξ; unfold A0of
  rw [div_le_iff₀ (by linarith)] at hξ
  rw [le_div_iff₀ h.htd]
  nlinarith

lemma u7_A0of (ξ : ℝ) : (par P0 0).u7 (A0of P0 ξ) = ξ := by
  have h4 := HP.td_lt_one h
  have : (par P0 0) = P0.mirror := par_even P0 0
  rw [this]
  unfold HP.u7 A0of HP.mirror
  simp only
  have : P0.td ≠ 0 := h.htd.ne'
  have : (1 - P0.td) ≠ 0 := by linarith
  field_simp
  ring

end consts

section inv
variable {P0} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h

lemma step_e {k : ℕ} (hk : Me P0 ≤ A P0 A0 (2 * k)) : Mo P0 ≤ A P0 A0 (2 * k + 1) := by
  rw [A_succ, par_even]
  have hcm := HP.cn_pos h.mirror
  have hl := lam_ge h
  have hMo := Mo_pos h
  have k1 := HP.u8_ge h.mirror (A P0 A0 (2 * k))
  have k2 : P0.mirror.cn * Me P0 ≤ P0.mirror.cn * A P0 A0 (2 * k) :=
    mul_le_mul_of_nonneg_left hk hcm.le
  have k3 := mul_le_mul_of_nonneg_right hl hMo.le
  unfold Me at k2
  nlinarith

lemma step_o {k : ℕ} (hk : Mo P0 ≤ A P0 A0 (2 * k + 1)) : Me P0 ≤ A P0 A0 (2 * k + 1 + 1) := by
  rw [A_succ, par_odd]
  have hcn := HP.cn_pos h
  have k1 := HP.u8_ge h (A P0 A0 (2 * k + 1))
  have k2 : P0.cn * Mo P0 ≤ P0.cn * A P0 A0 (2 * k + 1) := mul_le_mul_of_nonneg_left hk hcn.le
  unfold Me
  linarith

include hA0

lemma inv2 (k : ℕ) : Me P0 ≤ A P0 A0 (2 * k) ∧ Mo P0 ≤ A P0 A0 (2 * k + 1) := by
  induction k with
  | zero =>
    have e0 : Me P0 ≤ A P0 A0 (2 * 0) := hA0
    exact ⟨e0, step_e h e0⟩
  | succ k ih =>
    have e : Me P0 ≤ A P0 A0 (2 * (k + 1)) := by
      rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring]; exact step_o h ih.2
    exact ⟨e, step_e h e⟩

/-- every half is valid -/
lemma valid (n : ℕ) : (par P0 n).Valid (A P0 A0 n) := by
  have hcn := HP.cn_pos h
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [par_even]; apply HP.valid_of_ge h.mirror
    have k1 := (inv2 h hA0 k).1
    have k2 := le_max_right P0.K (P0.mirror.K / P0.cn)
    rw [div_le_iff₀ hcn] at k2
    have k3 : P0.mirror.K ≤ Me P0 := by unfold Me Mo; linarith
    linarith
  · rw [par_odd]; apply HP.valid_of_ge h
    have k1 := (inv2 h hA0 k).2
    have k2 : P0.K ≤ Mo P0 := le_max_left _ _
    linarith

lemma A_pos (n : ℕ) : 0 < A P0 A0 n := (valid h hA0 n).1

lemma G_gt (n : ℕ) : G P0 A0 n + dmin P0 < G P0 A0 (n + 1) := by
  rw [G_succ]
  have := HP.u8_gt (par_ok h n) (valid h hA0 n)
  have := par_dc_ge h n
  linarith

lemma G_lower (n : ℕ) : G P0 A0 0 + n * dmin P0 ≤ G P0 A0 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have := G_gt h hA0 n
    push_cast; linarith

lemma G_strictMono : StrictMono (G P0 A0) :=
  strictMono_nat_of_lt_succ fun n => by
    have := G_gt h hA0 n; have := dmin_pos h; linarith

lemma G_tendsto : Tendsto (G P0 A0) atTop atTop := by
  have hd := dmin_pos h
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨⌈(b - G P0 A0 0) / dmin P0⌉₊, fun n hn => ?_⟩
  have h1 : (b - G P0 A0 0) / dmin P0 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  rw [div_le_iff₀ hd] at h1
  have := G_lower h hA0 n
  linarith

end inv

/-- the half containing global time `σ` -/
def loc (A0 σ : ℝ) : ℕ := sInf {n : ℕ | σ < G P0 A0 (n + 1)}

section locs
variable {P0} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h hA0

lemma loc_spec {σ : ℝ} (hσ : G P0 A0 0 ≤ σ) :
    G P0 A0 (loc P0 A0 σ) ≤ σ ∧ σ < G P0 A0 (loc P0 A0 σ + 1) := by
  have hx : ({n : ℕ | σ < G P0 A0 (n + 1)}).Nonempty := by
    obtain ⟨n, hn⟩ := ((G_tendsto h hA0).eventually_gt_atTop σ).exists
    exact ⟨n, hn.trans (G_strictMono h hA0 (Nat.lt_succ_self n))⟩
  refine ⟨?_, Nat.sInf_mem hx⟩
  unfold loc
  by_contra hc; push_neg at hc
  have hne : sInf {n : ℕ | σ < G P0 A0 (n + 1)} ≠ 0 := by
    intro h0; rw [h0] at hc; linarith
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hne
  rw [hm] at hc
  have := Nat.sInf_le (show m ∈ {n : ℕ | σ < G P0 A0 (n + 1)} from hc)
  omega

lemma loc_eq {σ : ℝ} {n : ℕ} (h1 : G P0 A0 n ≤ σ) (h2 : σ < G P0 A0 (n + 1)) :
    loc P0 A0 σ = n := by
  have hσ : G P0 A0 0 ≤ σ := ((G_strictMono h hA0).monotone (Nat.zero_le n)).trans h1
  obtain ⟨s1, s2⟩ := loc_spec h hA0 hσ
  have le1 : loc P0 A0 σ ≤ n := Nat.sInf_le (show n ∈ {n : ℕ | σ < G P0 A0 (n + 1)} from h2)
  by_contra hne
  have lt : loc P0 A0 σ + 1 ≤ n := by omega
  have := (G_strictMono h hA0).monotone lt
  linarith

lemma loc_rel {σ : ℝ} (hσ : G P0 A0 0 ≤ σ) :
    0 ≤ σ - G P0 A0 (loc P0 A0 σ) ∧
      σ - G P0 A0 (loc P0 A0 σ) < (par P0 (loc P0 A0 σ)).u8 (A P0 A0 (loc P0 A0 σ)) := by
  obtain ⟨s1, s2⟩ := loc_spec h hA0 hσ
  rw [G_succ] at s2
  constructor <;> linarith

end locs

end Seq

end KSHalf

/-! ## Part D: global rates, cumulative outputs per half -/

namespace KSHalf
open MeasureTheory Set Filter

namespace HP
variable {Q : HP}

/-- sum of inverse processing times (mirror invariant) -/
def S (Q : HP) : ℝ := Q.ta⁻¹ + Q.tb⁻¹ + Q.tc⁻¹ + Q.td⁻¹

lemma S_mirror (Q : HP) : Q.mirror.S = Q.S := by unfold S mirror; simp only; ring

lemma ind_div_le {t : ℝ} (ht : 0 < t) (α β u : ℝ) : ind α β u / t ≤ t⁻¹ := by
  rw [div_eq_mul_inv]; exact mul_le_of_le_one_left (inv_pos.2 ht).le (ind_le_one _ _ _)

lemma ind_div_nonneg {t : ℝ} (ht : 0 < t) (α β u : ℝ) : 0 ≤ ind α β u / t :=
  div_nonneg (ind_nonneg _ _ _) ht.le

lemma rates_bd (hQ : Q.Ok) (A u : ℝ) :
    (0 ≤ Q.ra A u ∧ Q.ra A u ≤ 2 * Q.S + 1) ∧ (0 ≤ Q.rb A u ∧ Q.rb A u ≤ 2 * Q.S + 1) ∧
      (0 ≤ Q.rd A u ∧ Q.rd A u ≤ 2 * Q.S + 1) := by
  have i1 := inv_pos.2 hQ.hta
  have i2 := inv_pos.2 hQ.htb
  have i3 := inv_pos.2 hQ.htc
  have i4 := inv_pos.2 hQ.htd
  have a1 := ind_div_le hQ.hta 0 (Q.u2 A) u
  have a2 := ind_div_le hQ.hta (Q.u5 A) (Q.u6 A) u
  have a3 := ind_le_one (Q.u6 A) (Q.u8 A) u
  have b1 := ind_div_nonneg hQ.hta 0 (Q.u2 A) u
  have b2 := ind_div_nonneg hQ.hta (Q.u5 A) (Q.u6 A) u
  have b3 := ind_nonneg (Q.u6 A) (Q.u8 A) u
  have c1 := ind_div_le hQ.htb Q.db (Q.u7 A) u
  have c2 := ind_div_nonneg hQ.htb Q.db (Q.u7 A) u
  have d1 := ind_div_le hQ.htd (Q.u3 A) (Q.u4 A) u
  have d2 := ind_div_nonneg hQ.htd (Q.u3 A) (Q.u4 A) u
  unfold ra rb rd S
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> linarith

lemma ra_meas (A : ℝ) : Measurable (Q.ra A) := by
  unfold ra
  exact (((ind_measurable _ _).div_const _).add ((ind_measurable _ _).div_const _)).add
    (ind_measurable _ _)
lemma rb_meas (A : ℝ) : Measurable (Q.rb A) := by
  unfold rb; exact (ind_measurable _ _).div_const _
lemma rd_meas (A : ℝ) : Measurable (Q.rd A) := by
  unfold rd; exact (ind_measurable _ _).div_const _

end HP

namespace Seq
variable (P0 : HP)

/-- rate of buffer (type `p`, stage `i`) in half `n` at relative time `u`;
the main type of half `n` is `(n+1) % 2`; roles a,b (main) and c,d (other) -/
def prate (A0 : ℝ) (n p i : ℕ) (u : ℝ) : ℝ :=
  if p = (n + 1) % 2 then
    (if i = 0 then (par P0 n).ra (A P0 A0 n) u else (par P0 n).rb (A P0 A0 n) u)
  else (if i = 0 then 0 else (par P0 n).rd (A P0 A0 n) u)

/-- cumulative output within half `n` -/
def pcum (A0 : ℝ) (n p i : ℕ) (u : ℝ) : ℝ :=
  if p = (n + 1) % 2 then
    (if i = 0 then (par P0 n).Ra (A P0 A0 n) u else (par P0 n).Rb (A P0 A0 n) u)
  else (if i = 0 then 0 else (par P0 n).Rd (A P0 A0 n) u)

/-- level within half `n` -/
def plev (A0 : ℝ) (n p i : ℕ) (u : ℝ) : ℝ :=
  if p = (n + 1) % 2 then
    (if i = 0 then (par P0 n).La (A P0 A0 n) u else (par P0 n).Lb (A P0 A0 n) u)
  else (if i = 0 then u else (par P0 n).Ld (A P0 A0 n) u)

/-- global rate of buffer (type `p`, stage `i`) at global time `σ` -/
def grate (A0 : ℝ) (p i : ℕ) (σ : ℝ) : ℝ :=
  prate P0 A0 (loc P0 A0 σ) p i (σ - G P0 A0 (loc P0 A0 σ))

/-- global cumulative output -/
def gy (A0 : ℝ) (p i : ℕ) (t : ℝ) : ℝ := ∫ σ in (0 : ℝ)..t, grate P0 A0 p i σ

lemma pcum_cont (A0 : ℝ) (n p i : ℕ) : Continuous (pcum P0 A0 n p i) := by
  unfold pcum
  split_ifs
  · exact HP.Ra_cont _
  · exact HP.Rb_cont _
  · exact continuous_const
  · exact HP.Rd_cont _

lemma prate_meas (A0 : ℝ) (n p i : ℕ) : Measurable (prate P0 A0 n p i) := by
  unfold prate
  split_ifs
  · exact HP.ra_meas _
  · exact HP.rb_meas _
  · exact measurable_const
  · exact HP.rd_meas _

lemma par_cases (n : ℕ) : par P0 n = P0.mirror ∨ par P0 n = P0 := by
  unfold par; split_ifs <;> simp

section D
variable {P0} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h

lemma prate_bd (n p i : ℕ) (u : ℝ) :
    0 ≤ prate P0 A0 n p i u ∧ prate P0 A0 n p i u ≤ 2 * P0.S + 1 := by
  have hS : (par P0 n).S = P0.S := by
    rcases par_cases P0 n with e | e <;> rw [e]
    exact HP.S_mirror P0
  have hb := HP.rates_bd (par_ok h n) (A P0 A0 n) u
  rw [hS] at hb
  have hSp : 0 ≤ P0.S := by
    unfold HP.S
    have := inv_pos.2 h.hta; have := inv_pos.2 h.htb
    have := inv_pos.2 h.htc; have := inv_pos.2 h.htd
    linarith
  unfold prate
  split_ifs
  · exact hb.1
  · exact hb.2.1
  · constructor <;> linarith
  · exact hb.2.2

lemma grate_bd (p i : ℕ) (σ : ℝ) : |grate P0 A0 p i σ| ≤ 2 * P0.S + 1 := by
  obtain ⟨b1, b2⟩ := prate_bd h (A0 := A0) (loc P0 A0 σ) p i (σ - G P0 A0 (loc P0 A0 σ))
  unfold grate
  rw [abs_of_nonneg b1]; exact b2

include hA0

lemma pcum_deriv (n p i : ℕ) (u : ℝ) :
    HasDerivWithinAt (pcum P0 A0 n p i) (prate P0 A0 n p i u) (Ioi u) u := by
  have hok := par_ok h n
  have hv := valid h hA0 n
  unfold pcum prate
  split_ifs
  · exact HP.Ra_deriv hok hv u
  · exact HP.Rb_deriv hok hv u
  · exact hasDerivWithinAt_const _ _ _
  · exact HP.Rd_deriv hok hv u

lemma loc_nonempty (σ : ℝ) : ({n : ℕ | σ < G P0 A0 (n + 1)}).Nonempty := by
  obtain ⟨n, hn⟩ := ((G_tendsto h hA0).eventually_gt_atTop σ).exists
  exact ⟨n, hn.trans (G_strictMono h hA0 (Nat.lt_succ_self n))⟩

lemma loc_iff (σ : ℝ) (n : ℕ) :
    loc P0 A0 σ = n ↔ σ < G P0 A0 (n + 1) ∧ ∀ m < n, G P0 A0 (m + 1) ≤ σ := by
  constructor
  · rintro rfl
    refine ⟨Nat.sInf_mem (loc_nonempty h hA0 σ), fun m hm => ?_⟩
    by_contra hc; push_neg at hc
    have := Nat.sInf_le (show m ∈ {n : ℕ | σ < G P0 A0 (n + 1)} from hc)
    unfold loc at hm; omega
  · rintro ⟨h1, h2⟩
    apply le_antisymm (Nat.sInf_le h1)
    by_contra hc; push_neg at hc
    have k1 := h2 _ hc
    have k2 : σ < G P0 A0 (sInf {n : ℕ | σ < G P0 A0 (n + 1)} + 1) :=
      Nat.sInf_mem (loc_nonempty h hA0 σ)
    linarith

lemma loc_meas : Measurable (loc P0 A0) := by
  refine measurable_to_countable' fun n => ?_
  have e : (loc P0 A0) ⁻¹' {n} = Iio (G P0 A0 (n + 1)) ∩ ⋂ m : Fin n, Ici (G P0 A0 (m + 1)) := by
    ext σ
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_Iio, mem_iInter, mem_Ici]
    rw [loc_iff h hA0]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun m => h2 m m.2⟩
    · rintro ⟨h1, h2⟩; exact ⟨h1, fun m hm => h2 ⟨m, hm⟩⟩
  rw [e]
  exact measurableSet_Iio.inter (MeasurableSet.iInter fun _ => measurableSet_Ici)

lemma grate_meas (p i : ℕ) : Measurable (grate P0 A0 p i) := by
  intro T hT
  have e : (grate P0 A0 p i) ⁻¹' T = ⋃ n : ℕ, (loc P0 A0 ⁻¹' {n}) ∩
      ((fun σ => prate P0 A0 n p i (σ - G P0 A0 n)) ⁻¹' T) := by
    ext σ; simp [grate]
  rw [e]
  refine MeasurableSet.iUnion fun n => (loc_meas h hA0 (measurableSet_singleton n)).inter ?_
  exact ((prate_meas P0 A0 n p i).comp (measurable_id.sub_const _)) hT

/-- cumulative output over a piece of half `n` -/
lemma ydiff {n p i : ℕ} {s t : ℝ} (hst : s ≤ t) (hs : G P0 A0 n ≤ s)
    (ht : t ≤ G P0 A0 (n + 1)) :
    ∫ σ in s..t, grate P0 A0 p i σ =
      pcum P0 A0 n p i (t - G P0 A0 n) - pcum P0 A0 n p i (s - G P0 A0 n) := by
  have hc := pcum_cont P0 A0 n p i
  apply ftc (f := fun σ => pcum P0 A0 n p i (σ - G P0 A0 n)) hst
    (Continuous.continuousOn (by fun_prop))
  · intro x hx
    have hl : loc P0 A0 x = n := by
      rw [loc_iff h hA0]
      refine ⟨lt_of_lt_of_le hx.2 ht, fun m hm => ?_⟩
      have := (G_strictMono h hA0).monotone (show m + 1 ≤ n by omega)
      linarith [hx.1]
    have e : grate P0 A0 p i x = prate P0 A0 n p i (x - G P0 A0 n) := by
      unfold grate; rw [hl]
    rw [e]
    exact shift_deriv (pcum_deriv h hA0 n p i (x - G P0 A0 n))
  · exact grate_meas h hA0 p i
  · exact grate_bd h p i

end D

end Seq

end KSHalf

/-! ## Part D3: closed form of the global levels -/

namespace KSHalf
open MeasureTheory Set Filter

namespace Seq
variable (P0 : HP)

/-- global level of buffer (type `p`, stage `i`); stage 0 has inflow rate 1, stage 1 receives
the output of stage 0 -/
def X (A0 : ℝ) (p i : ℕ) (t : ℝ) : ℝ :=
  plev P0 A0 0 p i (-G P0 A0 0) + (if i = 0 then t else gy P0 A0 p 0 t) - gy P0 A0 p i t

lemma plev_diff (A0 : ℝ) (n p i : ℕ) (u v : ℝ) :
    plev P0 A0 n p i v - plev P0 A0 n p i u =
      (if i = 0 then v - u else pcum P0 A0 n p 0 v - pcum P0 A0 n p 0 u) -
        (pcum P0 A0 n p i v - pcum P0 A0 n p i u) := by
  by_cases hp : p = (n + 1) % 2 <;> by_cases hi : i = 0 <;>
    simp [plev, pcum, hp, hi, HP.La, HP.Lb, HP.Ld] <;> ring

section D3
variable {P0} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h hA0

lemma grate_ii (p i : ℕ) (a b : ℝ) : IntervalIntegrable (grate P0 A0 p i) volume a b := by
  apply (intervalIntegrable_const (c := 2 * P0.S + 1)).mono_fun
    (grate_meas h hA0 p i).aestronglyMeasurable
  filter_upwards with x
  simp only [Real.norm_eq_abs]
  exact (grate_bd h p i x).trans (le_abs_self _)

lemma gy_sub (p i : ℕ) (s t : ℝ) :
    gy P0 A0 p i t - gy P0 A0 p i s = ∫ σ in s..t, grate P0 A0 p i σ := by
  unfold gy
  exact intervalIntegral.integral_interval_sub_left (grate_ii h hA0 p i 0 t) (grate_ii h hA0 p i 0 s)

lemma X_diff {n p i : ℕ} {s t : ℝ} (hst : s ≤ t) (hs : G P0 A0 n ≤ s)
    (ht : t ≤ G P0 A0 (n + 1)) :
    X P0 A0 p i t - X P0 A0 p i s =
      plev P0 A0 n p i (t - G P0 A0 n) - plev P0 A0 n p i (s - G P0 A0 n) := by
  rw [plev_diff]
  have e1 := gy_sub h hA0 p i s t
  have e0 := gy_sub h hA0 p 0 s t
  rw [ydiff h hA0 hst hs ht] at e1 e0
  unfold X
  by_cases hi : i = 0
  · simp only [if_pos hi]; linarith
  · simp only [if_neg hi]; linarith

lemma G1_pos : 0 < G P0 A0 1 := by
  rw [G_succ, G_zero, A_zero]; unfold HP.u8; linarith [(par_ok h 0).hdc]

lemma G0_neg : G P0 A0 0 < 0 := by
  rw [G_zero]
  have := HP.u7_pos (par_ok h 0) (valid h hA0 0)
  rw [A_zero] at this; linarith

lemma par_dc_succ (n : ℕ) : (par P0 n).dc = (par P0 (n + 1)).da := by
  unfold par
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · have : (n + 1) % 2 = 1 := by omega
    simp [e, this, HP.mirror]
  · have : (n + 1) % 2 = 0 := by omega
    simp [e, this, HP.mirror]

lemma plev_bdry {n p i : ℕ} (hp : p < 2) :
    plev P0 A0 n p i ((par P0 n).u8 (A P0 A0 n)) = plev P0 A0 (n + 1) p i 0 := by
  have hok := par_ok h n
  have hv := valid h hA0 n
  have hok' := par_ok h (n + 1)
  have hv' := valid h hA0 (n + 1)
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hok hv
  obtain ⟨q2, q3, -⟩ := HP.ord hok' hv'
  have hdd := par_dc_succ h hA0 n
  unfold plev
  by_cases hm : p = (n + 1) % 2
  · have hm' : ¬ p = (n + 1 + 1) % 2 := by omega
    rw [if_pos hm, if_neg hm']
    by_cases hi : i = 0
    · rw [if_pos hi, if_pos hi]; exact HP.La_zero hok hv (by linarith) le_rfl
    · rw [if_neg hi, if_neg hi, HP.Lb_hi hok hv (by linarith) le_rfl,
        HP.Ld_lo hok' hv' (by linarith)]
      unfold HP.u8; linarith
  · have hm' : p = (n + 1 + 1) % 2 := by omega
    rw [if_neg hm, if_pos hm']
    by_cases hi : i = 0
    · rw [if_pos hi, if_pos hi, HP.La_zero0 hok' hv', A_succ]
    · rw [if_neg hi, if_neg hi, HP.Ld_hi hok hv (by linarith), HP.Lb_zero0 hok' hv']

/-- closed form of the levels on every half -/
lemma X_eq (n : ℕ) {p i : ℕ} (hp : p < 2) {t : ℝ} (h0 : 0 ≤ t) (h1 : G P0 A0 n ≤ t)
    (h2 : t ≤ G P0 A0 (n + 1)) :
    X P0 A0 p i t = plev P0 A0 n p i (t - G P0 A0 n) := by
  induction n generalizing t with
  | zero =>
    have hG0 := G0_neg h hA0
    have e := X_diff h hA0 (p := p) (i := i) h0 hG0.le h2
    have x0 : X P0 A0 p i 0 = plev P0 A0 0 p i (-G P0 A0 0) := by
      unfold X gy; simp
    rw [x0, zero_sub] at e; linarith
  | succ n ih =>
    have hG1 := G1_pos h hA0
    have hG : 0 ≤ G P0 A0 (n + 1) := by
      have := (G_strictMono h hA0).monotone (show 1 ≤ n + 1 by omega); linarith
    have hlo : G P0 A0 n ≤ G P0 A0 (n + 1) := (G_strictMono h hA0 (Nat.lt_succ_self n)).le
    have k1 := ih hG hlo le_rfl
    have hd : G P0 A0 (n + 1) - G P0 A0 n = (par P0 n).u8 (A P0 A0 n) := by rw [G_succ]; ring
    rw [hd, plev_bdry h hA0 hp] at k1
    have e := X_diff h hA0 (p := p) (i := i) h1 le_rfl h2
    rw [sub_self] at e
    linarith

/-- the levels at global time `t ≥ 0` -/
lemma X_loc {p i : ℕ} (hp : p < 2) {t : ℝ} (h0 : 0 ≤ t) :
    X P0 A0 p i t = plev P0 A0 (loc P0 A0 t) p i (t - G P0 A0 (loc P0 A0 t)) := by
  obtain ⟨s1, s2⟩ := loc_spec h hA0 ((G0_neg h hA0).le.trans h0)
  exact X_eq h hA0 _ hp h0 s1 s2.le

/-- initial levels: type 0 stage 0 holds `u7` of half 0, everything else is empty -/
lemma X_zero (p i : ℕ) (hp : p < 2) :
    X P0 A0 p i 0 = if p = 0 ∧ i = 0 then (par P0 0).u7 A0 else 0 := by
  have hok := par_ok h 0
  have hv := valid h hA0 0
  rw [A_zero] at hv
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hok hv
  rw [X_eq h hA0 0 hp le_rfl (G0_neg h hA0).le (G1_pos h hA0).le, zero_sub, G_zero, neg_neg]
  unfold plev
  rw [A_zero]
  interval_cases p
  · have : ¬ (0 = (0 + 1) % 2) := by omega
    rw [if_neg this]
    by_cases hi : i = 0
    · simp [hi]
    · simp only [hi, if_false, and_false]
      exact HP.Ld_hi hok hv (by linarith)
  · rw [if_pos (by omega)]
    by_cases hi : i = 0
    · simp only [hi, if_true, and_true, one_ne_zero, if_false]
      exact HP.La_zero hok hv o7 o8.le
    · simp only [hi, if_false, and_false]
      rw [HP.Lb_hi hok hv le_rfl o8.le]; ring

end D3

end Seq

end KSHalf

/-! ## Part E: half-runs (machine `m`, half `n`, half-run `i ∈ {0,1}`) -/

namespace KSHalf
open Filter

namespace Seq
variable (P0 : HP)

/-- offset (within half `n`) of the start of half-run `i` of machine `m`; machine `m` is
`MA` (roles a, d) of half `n` iff `m = (n+1) % 2` -/
def hoff (A0 : ℝ) (m n i : ℕ) : ℝ :=
  if m = (n + 1) % 2 then
    (if i = 0 then (par P0 n).u2 (A P0 A0 n) else (par P0 n).u4 (A P0 A0 n))
  else (if i = 0 then 0 else (par P0 n).u7 (A P0 A0 n))

/-- offset of the start of the processing phase of half-run `i` -/
def poff (A0 : ℝ) (m n i : ℕ) : ℝ :=
  if m = (n + 1) % 2 then
    (if i = 0 then (par P0 n).u3 (A P0 A0 n) else (par P0 n).u5 (A P0 A0 n))
  else (if i = 0 then (par P0 n).db else (par P0 n).u8 (A P0 A0 n))

/-- set-up time of half-run `i` (MA: d then a; MB: b then c) -/
def hset (m n i : ℕ) : ℝ :=
  if m = (n + 1) % 2 then (if i = 0 then (par P0 n).dd else (par P0 n).da)
  else (if i = 0 then (par P0 n).db else (par P0 n).dc)

def hs (A0 : ℝ) (m n i : ℕ) : ℝ := G P0 A0 n + hoff P0 A0 m n i
def hp (A0 : ℝ) (m n i : ℕ) : ℝ := G P0 A0 n + poff P0 A0 m n i

/-- start of the `j`-th half-run of machine `m` -/
def HS (A0 : ℝ) (m j : ℕ) : ℝ := hs P0 A0 m (j / 2) (j % 2)

lemma hp_eq (A0 : ℝ) (m n i : ℕ) : hp P0 A0 m n i = hs P0 A0 m n i + hset P0 m n i := by
  unfold hp hs poff hoff hset
  split_ifs <;> (try unfold HP.u3) <;> (try unfold HP.u5) <;> (try unfold HP.u8) <;> ring

section E
variable {P0} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h

lemma hset_pos (m n i : ℕ) : 0 < hset P0 m n i := by
  have hok := par_ok h n
  unfold hset
  split_ifs
  · exact hok.hdd
  · exact hok.hda
  · exact hok.hdb
  · exact hok.hdc

include hA0

lemma hs_lt_hp (m n i : ℕ) : hs P0 A0 m n i < hp P0 A0 m n i := by
  rw [hp_eq]; linarith [hset_pos h m n i]

lemma G_le_hs (m n i : ℕ) : G P0 A0 n ≤ hs P0 A0 m n i := by
  have hok := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hok hv
  unfold hs hoff
  split_ifs <;> linarith

lemma hp_le_G (m n i : ℕ) : hp P0 A0 m n i ≤ G P0 A0 (n + 1) := by
  have hok := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hok hv
  have hdb := hv.2.1
  rw [G_succ]
  unfold hp poff
  split_ifs <;> linarith

lemma hp_le_hs1 (m n : ℕ) : hp P0 A0 m n 0 ≤ hs P0 A0 m n 1 := by
  have hok := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hok hv
  have hdb := hv.2.1
  unfold hp hs poff hoff
  by_cases hm : m = (n + 1) % 2 <;> simp [hm] <;> linarith

lemma hp_le_succ (m j : ℕ) :
    hp P0 A0 m (j / 2) (j % 2) ≤ hs P0 A0 m ((j + 1) / 2) ((j + 1) % 2) := by
  rcases Nat.mod_two_eq_zero_or_one j with e | e
  · have e1 : (j + 1) / 2 = j / 2 := by omega
    have e2 : (j + 1) % 2 = 1 := by omega
    rw [e, e1, e2]; exact hp_le_hs1 h hA0 m (j / 2)
  · have e1 : (j + 1) / 2 = j / 2 + 1 := by omega
    have e2 : (j + 1) % 2 = 0 := by omega
    rw [e, e1, e2]
    exact (hp_le_G h hA0 m (j / 2) 1).trans (G_le_hs h hA0 m (j / 2 + 1) 0)

lemma HS_lt_succ (m j : ℕ) : HS P0 A0 m j < HS P0 A0 m (j + 1) := by
  unfold HS
  exact (hs_lt_hp h hA0 m _ _).trans_le (hp_le_succ h hA0 m j)

lemma HS_strictMono (m : ℕ) : StrictMono (HS P0 A0 m) :=
  strictMono_nat_of_lt_succ (HS_lt_succ h hA0 m)

lemma HS_tendsto (m : ℕ) : Tendsto (HS P0 A0 m) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.1 (G_tendsto h hA0) b
  refine ⟨2 * N, fun j hj => ?_⟩
  have := hN (j / 2) (by omega)
  have := G_le_hs h hA0 m (j / 2) (j % 2)
  unfold HS; linarith

end E

end Seq

end KSHalf

/-! ## Part F: the schedule of Example 2 -/

namespace KSHalf
namespace Seq
section Fnn
variable {P0 : HP} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h hA0

lemma plev_nonneg (n p i : ℕ) {u : ℝ} (h0 : 0 ≤ u) (h8 : u ≤ (par P0 n).u8 (A P0 A0 n)) :
    0 ≤ plev P0 A0 n p i u := by
  have hok := par_ok h n
  have hv := valid h hA0 n
  unfold plev
  split_ifs
  · exact HP.La_nonneg hok hv h0 h8
  · exact HP.Lb_nonneg hok hv h0 h8
  · exact h0
  · exact HP.Ld_nonneg hok hv u

lemma X_nonneg {p i : ℕ} (hp : p < 2) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ X P0 A0 p i t := by
  rw [X_loc h hA0 hp ht]
  obtain ⟨r1, r2⟩ := loc_rel h hA0 ((G0_neg h hA0).le.trans ht)
  exact plev_nonneg h hA0 _ _ _ r1 r2.le

end Fnn
end Seq
end KSHalf

namespace KumarSeidman.TwoType
namespace KSProof
open Example2 KSHalf KSHalf.Seq MeasureTheory Filter

variable (P : HP) (A0 : ℝ)

/-- the clearing schedule: half-run `j` of machine `m` is global run `j - m` -/
def sched : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Schedule where
  x := fun b t => X P A0 (b.1 : ℕ) (b.2 : ℕ) t
  y := fun b t => gy P A0 (b.1 : ℕ) (b.2 : ℕ) t
  nruns := fun _ => ⊤
  β := fun m k => if (k + (m : ℕ)) % 2 = 0 then (if (m : ℕ) = 0 then b₄ else b₂)
    else (if (m : ℕ) = 0 then b₁ else b₃)
  s := fun m k => if k = 0 then 0 else HS P A0 (m : ℕ) (k + (m : ℕ))

lemma y_zero (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) :
    (sched P A0).y b 0 = 0 := by
  simp [sched, gy]

lemma x_eq (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) (t : ℝ) :
    (sched P A0).x b t = (sched P A0).x b 0 +
      System.inflow _ (sched P A0).y b t - (sched P A0).y b t := by
  have hi : (b.2 : ℕ) < 2 := b.2.isLt
  by_cases h0 : (b.2 : ℕ) = 0
  · rw [System.inflow, if_pos h0]
    have hd : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).d b.1 = 1 := rfl
    rw [hd]
    show X P A0 _ _ t = X P A0 _ _ 0 + 1 * t - gy P A0 _ _ t
    unfold X
    rw [if_pos h0, if_pos h0]
    simp only [gy, intervalIntegral.integral_same]
    ring
  · have h1 : (b.2 : ℕ) - 1 = 0 := by omega
    simp [sched, System.inflow, X, gy, h0, h1]

section
variable {P} (h : P.Ok) {A0} (hA0 : Me P ≤ A0)
include h hA0

lemma y_mono (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) :
    MonotoneOn ((sched P A0).y b) (Set.Ici 0) := by
  intro s _ t _ hst
  have e := gy_sub h hA0 (b.1 : ℕ) (b.2 : ℕ) s t
  have hn : 0 ≤ ∫ σ in s..t, grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ :=
    intervalIntegral.integral_nonneg hst (fun σ _ => (prate_bd h (A0 := A0) _ _ _ _).1)
  show gy P A0 _ _ s ≤ gy P A0 _ _ t
  linarith

lemma x_nonneg (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ (sched P A0).x b t :=
  X_nonneg h hA0 (p := (b.1 : ℕ)) (i := (b.2 : ℕ)) b.1.isLt ht

lemma starts {ξ : ℝ} (hξ : A0 = A0of P ξ) :
    (sched P A0).StartsAt (levels ξ 0 0 0) (setups b₄ b₃) := by
  constructor
  · intro b
    have hp2 : (b.1 : ℕ) < 2 := b.1.isLt
    show X P A0 b.1 b.2 0 = _
    rw [X_zero h hA0 _ _ hp2]
    rw [hξ, u7_A0of h]
    rcases b with ⟨⟨p, hp⟩, ⟨i, hi⟩⟩
    have hp' : p < 2 := hp
    have hi' : i < 2 := hi
    interval_cases p <;> interval_cases i <;> simp [levels] <;> rfl
  · intro m
    rcases m with ⟨m, hm⟩
    have hm' : m < 2 := hm
    interval_cases m <;> simp [sched, setups] <;> rfl

end

end KSProof
end KumarSeidman.TwoType

/-! ## Part F2: run structure of the schedule (IsTrajectory clauses 5-8) -/

namespace KumarSeidman.TwoType
namespace KSProof
open Example2 KSHalf KSHalf.Seq MeasureTheory Filter

lemma hset_tab (P : HP) (m n i : ℕ) (hm : m < 2) (hi : i < 2) :
    hset P m n i = if i = 0 then (if m = 0 then P.dd else P.db)
      else (if m = 0 then P.da else P.dc) := by
  unfold hset par
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · have e1 : (n + 1) % 2 = 1 := by omega
    interval_cases m <;> interval_cases i <;> simp [e, e1, HP.mirror]
  · have e1 : (n + 1) % 2 = 0 := by omega
    interval_cases m <;> interval_cases i <;> simp [e, e1]

variable (P : HP) (A0 : ℝ)

lemma mach_beta (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach ((sched P A0).β m k) = m := by
  rcases m with ⟨m, hm⟩
  have hm' : m < 2 := hm
  interval_cases m <;> simp only [sched] <;> split_ifs <;> first | rfl | contradiction

lemma delta_eq (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).δ ((sched P A0).β m k)
      ((sched P A0).β m (k + 1)) = hset P m ((k + 1 + m) / 2) ((k + 1 + m) % 2) := by
  have hm2 : (m : ℕ) < 2 := m.isLt
  rw [hset_tab P _ _ _ hm2 (Nat.mod_lt _ (by norm_num))]
  rcases m with ⟨m, hm⟩
  have hm' : m < 2 := hm
  rcases Nat.mod_two_eq_zero_or_one k with e | e
  · interval_cases m
    · have e0 : (k + 0) % 2 = 0 := by omega
      have e1 : (k + 1 + 0) % 2 = 1 := by omega
      simp [sched, e, e1, example2, b₁, b₄]
    · have e0 : (k + 1) % 2 = 1 := by omega
      have e1 : (k + 1 + 1) % 2 = 0 := by omega
      simp [sched, e0, e1, example2, b₂, b₃]
  · interval_cases m
    · have e0 : (k + 0) % 2 = 1 := by omega
      have e1 : (k + 1 + 0) % 2 = 0 := by omega
      simp [sched, e, e1, example2, b₁, b₄]
    · have e0 : (k + 1) % 2 = 0 := by omega
      have e1 : (k + 1 + 1) % 2 = 1 := by omega
      simp [sched, e0, e1, example2, b₂, b₃]

lemma s_succ (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    (sched P A0).s m (k + 1) = HS P A0 m (k + 1 + m) := by
  simp [sched]

lemma procStart_succ (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    (sched P A0).procStart m (k + 1) = hp P A0 m ((k + 1 + m) / 2) ((k + 1 + m) % 2) := by
  show (sched P A0).s m (k + 1) + _ = _
  rw [delta_eq, hp_eq, s_succ]
  rfl

lemma runExists (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    (sched P A0).RunExists m k := by
  simp [System.Schedule.RunExists, sched]

section
variable {P} (h : P.Ok) {A0} (hA0 : Me P ≤ A0)
include h hA0

lemma s_one_nonneg (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) :
    0 ≤ (sched P A0).s m 1 := by
  rw [s_succ]
  rcases m with ⟨m, hm⟩
  have hm' : m < 2 := hm
  interval_cases m
  · have : HS P A0 0 1 = 0 := by simp [HS, hs, hoff, G_zero, A_zero]
    simp [this]
  · show 0 ≤ HS P A0 1 2
    have e : HS P A0 1 2 = hs P A0 1 1 0 := rfl
    rw [e]
    exact (G1_pos h hA0).le.trans (G_le_hs h hA0 1 1 0)

lemma procStart_le (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    (sched P A0).procStart m k ≤ (sched P A0).s m (k + 1) := by
  cases k with
  | zero =>
    show (sched P A0).s m 0 ≤ _
    have : (sched P A0).s m 0 = 0 := by simp [sched]
    rw [this]; exact s_one_nonneg h hA0 m
  | succ k =>
    rw [procStart_succ, s_succ]
    have := hp_le_succ h hA0 (m : ℕ) (k + 1 + m)
    have e : k + 1 + 1 + (m : ℕ) = k + 1 + m + 1 := by omega
    rw [e]; exact this

lemma s_tendsto (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) :
    Tendsto ((sched P A0).s m) atTop atTop := by
  have h1 : Tendsto (fun k : ℕ => HS P A0 m (k + m)) atTop atTop :=
    (HS_tendsto h hA0 m).comp (tendsto_add_atTop_nat (m : ℕ))
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [s_succ]

end

end KSProof
end KumarSeidman.TwoType

/-! ## Part F3: rate cap and full rate (IsTrajectory clauses 9-10) -/

namespace KSHalf

lemma f3_ind_one {α β u : ℝ} (h1 : α ≤ u) (h2 : u < β) : ind α β u = 1 := by
  unfold ind; rw [if_pos ⟨h1, h2⟩]

lemma f3_ind_zero {α β u : ℝ} (h : ¬ (α ≤ u ∧ u < β)) : ind α β u = 0 := by
  unfold ind; rw [if_neg h]

lemma f3_ind_pos {α β u t : ℝ} (hr : 0 < ind α β u / t) : α ≤ u ∧ u < β := by
  by_contra hc; rw [f3_ind_zero hc, zero_div] at hr; exact lt_irrefl _ hr

namespace HP
variable {Q : HP}

lemma f3_ra_le (hQ : Q.Ok) {A : ℝ} (hv : Q.Valid A) (u : ℝ) : Q.ra A u ≤ Q.ta⁻¹ := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := HP.ord hQ hv
  have h1 : 1 ≤ Q.ta⁻¹ := (HP.inv_ta_gt_one hQ).le
  unfold HP.ra
  by_cases c1 : 0 ≤ u ∧ u < Q.u2 A
  · have c2 : ¬ (Q.u5 A ≤ u ∧ u < Q.u6 A) := fun c => by linarith [c.1, c1.2]
    have c3 : ¬ (Q.u6 A ≤ u ∧ u < Q.u8 A) := fun c => by linarith [c.1, c1.2]
    rw [f3_ind_one c1.1 c1.2, f3_ind_zero c2, f3_ind_zero c3]
    simp only [zero_div, add_zero, one_div, le_refl]
  · rw [f3_ind_zero c1]
    by_cases c2 : Q.u5 A ≤ u ∧ u < Q.u6 A
    · have c3 : ¬ (Q.u6 A ≤ u ∧ u < Q.u8 A) := fun c => by linarith [c.1, c2.2]
      rw [f3_ind_one c2.1 c2.2, f3_ind_zero c3]
      simp only [zero_div, add_zero, zero_add, one_div, le_refl]
    · rw [f3_ind_zero c2]
      by_cases c3 : Q.u6 A ≤ u ∧ u < Q.u8 A
      · rw [f3_ind_one c3.1 c3.2]; simp only [zero_div, zero_add]; exact h1
      · rw [f3_ind_zero c3]; simp only [zero_div, zero_add]; linarith

lemma f3_ra_pos (hQ : Q.Ok) {A : ℝ} (hv : Q.Valid A) {u : ℝ} (hr : 0 < Q.ra A u) :
    (0 ≤ u ∧ u < Q.u2 A) ∨ (Q.u5 A ≤ u ∧ u < Q.u8 A) := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := HP.ord hQ hv
  by_cases c1 : 0 ≤ u ∧ u < Q.u2 A
  · exact Or.inl c1
  by_cases c2 : Q.u5 A ≤ u ∧ u < Q.u6 A
  · exact Or.inr ⟨c2.1, by linarith [c2.2]⟩
  by_cases c3 : Q.u6 A ≤ u ∧ u < Q.u8 A
  · exact Or.inr ⟨by linarith [c3.1], c3.2⟩
  unfold HP.ra at hr
  rw [f3_ind_zero c1, f3_ind_zero c2, f3_ind_zero c3] at hr
  simp at hr

end HP

namespace Seq

def ptau (P0 : HP) (p i : ℕ) : ℝ :=
  if p = 0 then (if i = 0 then P0.ta else P0.tb) else (if i = 0 then P0.tc else P0.td)

lemma ptau_pos {P0 : HP} (h : P0.Ok) (p i : ℕ) : 0 < ptau P0 p i := by
  unfold ptau
  split_ifs
  · exact h.hta
  · exact h.htb
  · exact h.htc
  · exact h.htd

lemma tau_roles (P0 : HP) (n : ℕ) :
    (par P0 n).ta = ptau P0 ((n + 1) % 2) 0 ∧ (par P0 n).tb = ptau P0 ((n + 1) % 2) 1 ∧
      (par P0 n).td = ptau P0 (1 - (n + 1) % 2) 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with e | e
  · have e1 : (n + 1) % 2 = 1 := by omega
    simp [par, e, e1, ptau, HP.mirror]
  · have e1 : (n + 1) % 2 = 0 := by omega
    simp [par, e, e1, ptau]

section F3
variable {P0 : HP} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h hA0

lemma grate_at {p i n : ℕ} {σ : ℝ} (h1 : G P0 A0 n ≤ σ) (h2 : σ < G P0 A0 (n + 1)) :
    grate P0 A0 p i σ = prate P0 A0 n p i (σ - G P0 A0 n) := by
  unfold grate; rw [loc_eq h hA0 h1 h2]

lemma G0_u7 : G P0 A0 0 + (par P0 0).u7 (A P0 A0 0) = 0 := by
  rw [G_zero, A_zero]; ring

lemma grate_le {p i : ℕ} (hi2 : i < 2) (hp2 : p < 2) (σ : ℝ) :
    grate P0 A0 p i σ ≤ (ptau P0 p i)⁻¹ := by
  unfold grate
  obtain ⟨n, hn⟩ : ∃ n, loc P0 A0 σ = n := ⟨_, rfl⟩
  rw [hn]
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨t1, t2, t3⟩ := tau_roles P0 n
  unfold prate
  by_cases hpm : p = (n + 1) % 2
  · rw [if_pos hpm]; subst hpm
    by_cases hi0 : i = 0
    · subst hi0; rw [if_pos rfl, ← t1]; exact HP.f3_ra_le hQ hv _
    · have : i = 1 := by omega
      subst this; rw [if_neg one_ne_zero, ← t2]; exact HP.ind_div_le hQ.htb _ _ _
  · rw [if_neg hpm]
    by_cases hi0 : i = 0
    · subst hi0; rw [if_pos rfl]; exact (inv_pos.2 (ptau_pos h _ _)).le
    · have : i = 1 := by omega
      subst this; rw [if_neg one_ne_zero]
      have hp' : p = 1 - (n + 1) % 2 := by omega
      rw [hp', ← t3]; exact HP.ind_div_le hQ.htd _ _ _

lemma window_of_rate_n {p i : ℕ} (hp2 : p < 2) (hi2 : i < 2) {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ)
    (hl1 : G P0 A0 n ≤ σ) (hl2 : σ < G P0 A0 (n + 1))
    (hr : 0 < prate P0 A0 n p i (σ - G P0 A0 n)) :
    ∃ j, j % 2 + i = 1 ∧ (p + i) % 2 ≤ j ∧ hp P0 A0 ((p + i) % 2) (j / 2) (j % 2) ≤ σ ∧
      σ < HS P0 A0 ((p + i) % 2) (j + 1) := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  have h00 := G0_u7 h hA0
  unfold prate at hr
  by_cases hpm : p = (n + 1) % 2
  · rw [if_pos hpm] at hr
    by_cases hi0 : i = 0
    · subst hi0
      rw [if_pos rfl] at hr
      rcases HP.f3_ra_pos hQ hv hr with ⟨c1, c2⟩ | ⟨c1, c2⟩
      · rcases n with _ | n'
        · exfalso; linarith
        · have hG' := G_succ P0 A0 n'
          refine ⟨2 * n' + 1, by omega, by omega, ?_, ?_⟩
          · have e1 : (2 * n' + 1) / 2 = n' := by omega
            have e2 : (2 * n' + 1) % 2 = 1 := by omega
            rw [e1, e2]
            unfold hp poff
            split_ifs <;> first | (exfalso; omega) | linarith
          · have e1 : (2 * n' + 1 + 1) / 2 = n' + 1 := by omega
            have e2 : (2 * n' + 1 + 1) % 2 = 0 := by omega
            unfold HS; rw [e1, e2]
            unfold hs hoff
            split_ifs <;> first | (exfalso; omega) | linarith
      · refine ⟨2 * n + 1, by omega, by omega, ?_, ?_⟩
        · have e1 : (2 * n + 1) / 2 = n := by omega
          have e2 : (2 * n + 1) % 2 = 1 := by omega
          rw [e1, e2]
          unfold hp poff
          split_ifs <;> first | (exfalso; omega) | linarith
        · have e1 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
          have e2 : (2 * n + 1 + 1) % 2 = 0 := by omega
          unfold HS; rw [e1, e2]
          have := G_le_hs h hA0 ((p + 0) % 2) (n + 1) 0
          unfold hs at this ⊢
          linarith
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [if_neg one_ne_zero] at hr
      obtain ⟨c1, c2⟩ := f3_ind_pos hr
      refine ⟨2 * n, by omega, by omega, ?_, ?_⟩
      · have e1 : 2 * n / 2 = n := by omega
        have e2 : 2 * n % 2 = 0 := by omega
        rw [e1, e2]
        unfold hp poff
        split_ifs <;> first | (exfalso; omega) | linarith
      · have e1 : (2 * n + 1) / 2 = n := by omega
        have e2 : (2 * n + 1) % 2 = 1 := by omega
        unfold HS; rw [e1, e2]
        unfold hs hoff
        split_ifs <;> first | (exfalso; omega) | linarith
  · rw [if_neg hpm] at hr
    by_cases hi0 : i = 0
    · subst hi0; rw [if_pos rfl] at hr; exact absurd hr (lt_irrefl 0)
    · have hi1 : i = 1 := by omega
      subst hi1
      rw [if_neg one_ne_zero] at hr
      obtain ⟨c1, c2⟩ := f3_ind_pos hr
      rcases n with _ | n'
      · exfalso; linarith
      · refine ⟨2 * (n' + 1), by omega, by omega, ?_, ?_⟩
        · have e1 : 2 * (n' + 1) / 2 = n' + 1 := by omega
          have e2 : 2 * (n' + 1) % 2 = 0 := by omega
          rw [e1, e2]
          unfold hp poff
          split_ifs <;> first | (exfalso; omega) | linarith
        · have e1 : (2 * (n' + 1) + 1) / 2 = n' + 1 := by omega
          have e2 : (2 * (n' + 1) + 1) % 2 = 1 := by omega
          unfold HS; rw [e1, e2]
          unfold hs hoff
          split_ifs <;> first | (exfalso; omega) | linarith

lemma window_of_rate {p i : ℕ} (hp2 : p < 2) (hi2 : i < 2) {σ : ℝ} (hσ : 0 ≤ σ)
    (hr : 0 < grate P0 A0 p i σ) :
    ∃ j, j % 2 + i = 1 ∧ (p + i) % 2 ≤ j ∧ hp P0 A0 ((p + i) % 2) (j / 2) (j % 2) ≤ σ ∧
      σ < HS P0 A0 ((p + i) % 2) (j + 1) := by
  obtain ⟨hl1, hl2⟩ := loc_spec h hA0 (le_trans (G0_neg h hA0).le hσ)
  rw [grate_at h hA0 hl1 hl2] at hr
  exact window_of_rate_n h hA0 hp2 hi2 hσ _ hl1 hl2 hr

lemma rate_of_window {p i : ℕ} (hp2 : p < 2) (hi2 : i < 2) {σ : ℝ} (hσ : 0 ≤ σ) {j : ℕ}
    (hj : j % 2 + i = 1) (h1 : hp P0 A0 ((p + i) % 2) (j / 2) (j % 2) ≤ σ)
    (h2 : σ < HS P0 A0 ((p + i) % 2) (j + 1)) (hx : 0 < X P0 A0 p i σ) :
    grate P0 A0 p i σ = (ptau P0 p i)⁻¹ := by
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' j
  · have hi : i = 1 := by omega
    subst hi
    have e1 : 2 * n / 2 = n := by omega
    have e2 : 2 * n % 2 = 0 := by omega
    have e3 : (2 * n + 1) / 2 = n := by omega
    have e4 : (2 * n + 1) % 2 = 1 := by omega
    rw [e1, e2] at h1
    unfold HS at h2; rw [e3, e4] at h2
    have hQ := par_ok h n
    have hv := valid h hA0 n
    obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := HP.ord hQ hv
    have hG := G_succ P0 A0 n
    obtain ⟨t1, t2, t3⟩ := tau_roles P0 n
    unfold hp poff at h1
    unfold hs hoff at h2
    by_cases hm : (p + 1) % 2 = (n + 1) % 2
    · rw [if_pos hm, if_pos rfl] at h1
      rw [if_pos hm, if_neg one_ne_zero] at h2
      rw [grate_at h hA0 (n := n) (by linarith) (by linarith)]
      have hpm : ¬ p = (n + 1) % 2 := by omega
      unfold prate; rw [if_neg hpm, if_neg one_ne_zero]
      unfold HP.rd; rw [f3_ind_one (by linarith) (by linarith), t3]
      have : 1 - (n + 1) % 2 = p := by omega
      rw [this, one_div]
    · rw [if_neg hm, if_pos rfl] at h1
      rw [if_neg hm, if_neg one_ne_zero] at h2
      rw [grate_at h hA0 (n := n) (by linarith [hQ.hdb]) (by linarith)]
      have hpm : p = (n + 1) % 2 := by omega
      unfold prate; rw [if_pos hpm, if_neg one_ne_zero]
      unfold HP.rb; rw [f3_ind_one (by linarith) (by linarith), t2, ← hpm, one_div]
  · have hi : i = 0 := by omega
    subst hi
    have e1 : (2 * n + 1) / 2 = n := by omega
    have e2 : (2 * n + 1) % 2 = 1 := by omega
    have e3 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
    have e4 : (2 * n + 1 + 1) % 2 = 0 := by omega
    rw [e1, e2] at h1
    unfold HS at h2; rw [e3, e4] at h2
    have hQ := par_ok h n
    have hv := valid h hA0 n
    obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := HP.ord hQ hv
    have hG := G_succ P0 A0 n
    obtain ⟨t1, t2, t3⟩ := tau_roles P0 n
    unfold hp poff at h1
    unfold hs hoff at h2
    by_cases hm : (p + 0) % 2 = (n + 1) % 2
    · -- a-run of half n: [u5, u8)
      rw [if_pos hm, if_neg one_ne_zero] at h1
      have hm' : ¬ (p + 0) % 2 = (n + 1 + 1) % 2 := by omega
      rw [if_neg hm', if_pos rfl] at h2
      have hl2 : σ < G P0 A0 (n + 1) := by linarith
      rw [grate_at h hA0 (by linarith) hl2]
      have hpm : p = (n + 1) % 2 := by omega
      by_cases hu6 : σ - G P0 A0 n < (par P0 n).u6 (A P0 A0 n)
      · unfold prate; rw [if_pos hpm, if_pos rfl]
        unfold HP.ra
        rw [f3_ind_zero (fun c => by linarith [c.2]), f3_ind_one (by linarith) hu6,
          f3_ind_zero (fun c => by linarith [c.1]), t1, ← hpm]
        simp only [zero_div, zero_add, add_zero, one_div]
      · exfalso
        rw [X_eq h hA0 n hp2 hσ (by linarith) hl2.le] at hx
        unfold plev at hx
        rw [if_pos hpm, if_pos rfl, HP.La_zero hQ hv (not_lt.mp hu6) (by linarith)] at hx
        exact lt_irrefl _ hx
    · -- c-run of half n = a-role of half n+1: [0, u2')
      rw [if_neg hm, if_neg one_ne_zero] at h1
      have hm' : (p + 0) % 2 = (n + 1 + 1) % 2 := by omega
      rw [if_pos hm', if_pos rfl] at h2
      have hQ1 := par_ok h (n + 1)
      have hv1 := valid h hA0 (n + 1)
      obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := HP.ord hQ1 hv1
      have hG1 := G_succ P0 A0 (n + 1)
      obtain ⟨s1, s2, s3⟩ := tau_roles P0 (n + 1)
      rw [grate_at h hA0 (n := n + 1) (by linarith) (by linarith)]
      have hpm : p = (n + 1 + 1) % 2 := by omega
      unfold prate; rw [if_pos hpm, if_pos rfl]
      unfold HP.ra
      rw [f3_ind_one (by linarith) (by linarith), f3_ind_zero (fun c => by linarith [c.1]),
        f3_ind_zero (fun c => by linarith [c.1]), s1, ← hpm]
      simp only [zero_div, add_zero, one_div]

lemma hp_init (m : ℕ) (hm : m < 2) : hp P0 A0 m (m / 2) (m % 2) ≤ 0 := by
  have hQ := par_ok h 0
  have hv := valid h hA0 0
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := HP.ord hQ hv
  have h00 := G0_u7 h hA0
  have hdb := hv.2.1
  interval_cases m
  · show G P0 A0 0 + poff P0 A0 0 0 0 ≤ 0
    unfold poff; rw [if_neg (by norm_num), if_pos rfl]; linarith
  · show G P0 A0 0 + poff P0 A0 1 0 1 ≤ 0
    unfold poff; rw [if_pos (by norm_num), if_neg one_ne_zero]; linarith

end F3
end Seq
end KSHalf

namespace KumarSeidman.TwoType
namespace KSProof
open Example2 KSHalf KSHalf.Seq MeasureTheory Filter

lemma mach_val (P : HP) (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) :
    ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) =
      ((b.1 : ℕ) + (b.2 : ℕ)) % 2 := by
  rcases b with ⟨⟨p, hp⟩, ⟨i, hi⟩⟩
  have hp' : p < 2 := hp
  have hi' : i < 2 := hi
  interval_cases p <;> interval_cases i <;> first | rfl | decide | simp [System.mach, example2]

lemma procTime_val (P : HP) (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) :
    (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).procTime b = ptau P b.1 b.2 := by
  rcases b with ⟨⟨p, hp⟩, ⟨i, hi⟩⟩
  have hp' : p < 2 := hp
  have hi' : i < 2 := hi
  interval_cases p <;> interval_cases i <;> rfl

/-- stage index of a buffer -/
def bsnd (P : HP) (c : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) : ℕ := c.2

section
variable {P : HP} (h : P.Ok) {A0 : ℝ} (hA0 : Me P ≤ A0)
include h hA0

lemma proc_of_window (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) {σ : ℝ}
    (hσ : 0 ≤ σ) {j : ℕ} (hj : j % 2 + (b.2 : ℕ) = 1) (hmj : ((b.1 : ℕ) + (b.2 : ℕ)) % 2 ≤ j)
    (h1 : hp P A0 (((b.1 : ℕ) + (b.2 : ℕ)) % 2) (j / 2) (j % 2) ≤ σ)
    (h2 : σ < HS P A0 (((b.1 : ℕ) + (b.2 : ℕ)) % 2) (j + 1)) :
    (sched P A0).ProcessingBuffer ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b) b σ := by
  have mv := mach_val P b
  rw [← mv] at hmj h1 h2
  refine ⟨j - ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ), ?_,
    runExists P A0 _ _, ?_, fun _ => ?_⟩
  · show (if (j - ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) +
        ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ)) % 2 = 0 then
        (if ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) = 0 then b₄ else b₂)
        else (if ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) = 0 then b₁
          else b₃)) = b
    rw [Nat.sub_add_cancel hmj, mv]
    rcases b with ⟨⟨p, hp⟩, ⟨i, hi⟩⟩
    simp only at hj ⊢
    have hp' : p < 2 := hp
    have hi' : i < 2 := hi
    interval_cases p <;> interval_cases i
    · have e : j % 2 = 1 := by omega
      simp [e, b₁]
      first | rfl | decide
    · have e : j % 2 = 0 := by omega
      simp [e, b₂]
      first | rfl | decide
    · have e : j % 2 = 1 := by omega
      simp [e, b₃]
      first | rfl | decide
    · have e : j % 2 = 0 := by omega
      simp [e, b₄]
      first | rfl | decide
  · rcases hk : j - ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) with _ | k
    · show (sched P A0).s _ 0 ≤ σ
      simp [sched]; exact hσ
    · rw [procStart_succ]
      have e : k + 1 + ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) = j := by
        omega
      rw [e]; exact h1
  · rw [s_succ]
    have e : j - ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) + 1 +
        ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b : ℕ) = j + 1 := by omega
    rw [e]; exact h2

lemma window_of_proc (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) {σ : ℝ}
    (hσ : 0 ≤ σ)
    (hP : (sched P A0).ProcessingBuffer
      ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b) b σ) :
    ∃ j, j % 2 + (b.2 : ℕ) = 1 ∧ hp P A0 (((b.1 : ℕ) + (b.2 : ℕ)) % 2) (j / 2) (j % 2) ≤ σ ∧
      σ < HS P A0 (((b.1 : ℕ) + (b.2 : ℕ)) % 2) (j + 1) := by
  have mv := mach_val P b
  rw [← mv]
  generalize (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b = m at hP mv
  obtain ⟨k, hβ, _, hps, hlt⟩ := hP
  subst hβ
  refine ⟨k + m, ?_, ?_, ?_⟩
  · have v1 : bsnd P b₁ = 0 := by first | rfl | decide
    have v2 : bsnd P b₂ = 1 := by first | rfl | decide
    have v3 : bsnd P b₃ = 0 := by first | rfl | decide
    have v4 : bsnd P b₄ = 1 := by first | rfl | decide
    show (k + (m : ℕ)) % 2 + bsnd P
      (if (k + (m : ℕ)) % 2 = 0 then (if (m : ℕ) = 0 then b₄ else b₂)
        else (if (m : ℕ) = 0 then b₁ else b₃)) = 1
    rw [apply_ite (bsnd P), apply_ite (bsnd P), apply_ite (bsnd P), v1, v2, v3, v4]
    split_ifs <;> omega
  · rcases k with _ | k
    · simp only [zero_add]
      exact (hp_init h hA0 m m.isLt).trans hσ
    · rw [procStart_succ] at hps; exact hps
  · have := hlt (runExists P A0 _ _)
    rw [s_succ] at this
    rw [show k + (m : ℕ) + 1 = k + 1 + m by omega]; exact this

lemma rate_cap (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    (sched P A0).y b t - (sched P A0).y b s ≤
      (volume {σ | σ ∈ Set.Icc s t ∧ (sched P A0).ProcessingBuffer
        ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b) b σ}).toReal /
        (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).procTime b := by
  have hp2 : (b.1 : ℕ) < 2 := b.1.isLt
  have hi2 : (b.2 : ℕ) < 2 := b.2.isLt
  rw [procTime_val]
  have hτ : 0 < ptau P b.1 b.2 := ptau_pos h _ _
  have hf : Measurable (grate P A0 (b.1 : ℕ) (b.2 : ℕ)) := grate_meas h hA0 _ _
  have hE : MeasurableSet {σ | 0 < grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ} :=
    measurableSet_lt measurable_const hf
  have e := gy_sub h hA0 (b.1 : ℕ) (b.2 : ℕ) s t
  have hy : (sched P A0).y b t - (sched P A0).y b s =
      ∫ σ in s..t, grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ := by
    show gy P A0 _ _ t - gy P A0 _ _ s = _; linarith
  rw [hy]
  have hg : IntervalIntegrable ({σ | 0 < grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ}.indicator
      fun _ => (ptau P b.1 b.2)⁻¹) volume s t := by
    rw [intervalIntegrable_iff]
    exact (intervalIntegrable_iff.mp (intervalIntegrable_const)).indicator hE
  have h1 : ∫ σ in s..t, grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ ≤
      ∫ σ in s..t, ({σ | 0 < grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ}.indicator
        fun _ => (ptau P b.1 b.2)⁻¹) σ := by
    apply intervalIntegral.integral_mono_on hst (grate_ii h hA0 _ _ _ _) hg
    intro σ _
    by_cases hσ : σ ∈ {σ | 0 < grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ}
    · rw [Set.indicator_apply, if_pos hσ]; exact grate_le h hA0 hi2 hp2 σ
    · rw [Set.indicator_apply, if_neg hσ]; exact not_lt.mp hσ
  have h2 : ∫ σ in s..t, ({σ | 0 < grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ}.indicator
        fun _ => (ptau P b.1 b.2)⁻¹) σ =
      (volume ({σ | 0 < grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ} ∩ Set.Ioc s t)).toReal *
        (ptau P b.1 b.2)⁻¹ := by
    rw [intervalIntegral.integral_of_le hst, integral_indicator hE, setIntegral_const,
      smul_eq_mul, measureReal_def, Measure.restrict_apply hE]
  have h3 : volume ({σ | 0 < grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ} ∩ Set.Ioc s t) ≤
      volume {σ | σ ∈ Set.Icc s t ∧ (sched P A0).ProcessingBuffer
        ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b) b σ} := by
    apply measure_mono
    rintro σ ⟨hσE, hσI⟩
    refine ⟨Set.Ioc_subset_Icc_self hσI, ?_⟩
    have hσ0 : 0 ≤ σ := by linarith [hσI.1]
    obtain ⟨j, hj, hmj, hh1, hh2⟩ := window_of_rate h hA0 hp2 hi2 hσ0 hσE
    exact proc_of_window h hA0 b hσ0 hj hmj hh1 hh2
  have hfin : volume {σ | σ ∈ Set.Icc s t ∧ (sched P A0).ProcessingBuffer
        ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b) b σ} ≠ ⊤ :=
    ne_top_of_le_ne_top measure_Icc_lt_top.ne (measure_mono (fun σ hσ => hσ.1))
  have h4 := ENNReal.toReal_mono hfin h3
  rw [div_eq_mul_inv]
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ _ := mul_le_mul_of_nonneg_right h4 (inv_nonneg.2 hτ.le)

lemma full_rate (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t)
    (hP : ∀ σ ∈ Set.Ico s t, (sched P A0).ProcessingBuffer
      ((example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b) b σ ∧ 0 < (sched P A0).x b σ) :
    (sched P A0).y b t - (sched P A0).y b s =
      (t - s) / (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).procTime b := by
  rw [procTime_val]
  have e := gy_sub h hA0 (b.1 : ℕ) (b.2 : ℕ) s t
  have hy : (sched P A0).y b t - (sched P A0).y b s =
      ∫ σ in s..t, grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ := by
    show gy P A0 _ _ t - gy P A0 _ _ s = _; linarith
  rw [hy]
  have hae : ∀ᵐ σ ∂(volume : Measure ℝ), σ ≠ t := by
    rw [ae_iff]; simp [measure_singleton]
  have hc : ∫ σ in s..t, grate P A0 (b.1 : ℕ) (b.2 : ℕ) σ =
      ∫ σ in s..t, (ptau P b.1 b.2)⁻¹ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hae] with σ hσt hσI
    rw [Set.uIoc_of_le hst] at hσI
    obtain ⟨hpb, hx⟩ := hP σ ⟨hσI.1.le, lt_of_le_of_ne hσI.2 hσt⟩
    have hσ0 : 0 ≤ σ := by linarith [hσI.1]
    obtain ⟨j, hj, hh1, hh2⟩ := window_of_proc h hA0 b hσ0 hpb
    exact rate_of_window h hA0 b.1.isLt b.2.isLt hσ0 hj hh1 hh2 hx
  rw [hc, intervalIntegral.integral_const, smul_eq_mul, div_eq_mul_inv]

theorem isTrajectory : (sched P A0).IsTrajectory := by
  refine ⟨fun b => y_zero P A0 b, fun b => y_mono h hA0 b, fun b t _ => x_eq P A0 b t,
    fun b t ht => x_nonneg h hA0 b ht, fun m => ⟨runExists P A0 m 0, by simp [sched]⟩,
    fun m k _ => ?_, fun m k _ => ?_, fun m _ => ?_,
    fun b s t hs hst => rate_cap h hA0 b s t hs hst,
    fun b s t hs hst hP => full_rate h hA0 b s t hs hst hP⟩
  · exact mach_beta P A0 m k
  · exact procStart_le h hA0 m k
  · exact s_tendsto h hA0 m

end

end KSProof
end KumarSeidman.TwoType


/-! ## Part G1: half-level facts for the clearing rule -/

namespace KSHalf
namespace Seq
open MeasureTheory

section G1
variable {P0 : HP} (h : P0.Ok) {A0 : ℝ} (hA0 : Me P0 ≤ A0)
include h hA0

lemma g1_gy_mono (p i : ℕ) {s t : ℝ} (hst : s ≤ t) : gy P0 A0 p i s ≤ gy P0 A0 p i t := by
  have e := gy_sub h hA0 p i s t
  have hn : 0 ≤ ∫ σ in s..t, grate P0 A0 p i σ :=
    intervalIntegral.integral_nonneg hst (fun σ _ => (prate_bd h (A0 := A0) _ _ _ _).1)
  linarith

lemma g1_inact_const {n q : ℕ} (hq : q ≠ (n + 1) % 2) {s t : ℝ} (hst : s ≤ t)
    (hs : G P0 A0 n ≤ s) (ht : t ≤ G P0 A0 (n + 1)) : gy P0 A0 q 0 s = gy P0 A0 q 0 t := by
  have e1 := gy_sub h hA0 q 0 s t
  have e2 := ydiff h hA0 (p := q) (i := 0) hst hs ht
  simp [pcum, hq] at e2
  linarith

lemma g1_act_incr {n p : ℕ} (hp : p = (n + 1) % 2) {σ : ℝ} (hσ : G P0 A0 n < σ) :
    gy P0 A0 p 0 (G P0 A0 n) < gy P0 A0 p 0 σ := by
  subst hp
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  have t1 : G P0 A0 n < min σ (G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) := lt_min hσ (by linarith)
  have t2 : min σ (G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) ≤
      G P0 A0 n + (par P0 n).u2 (A P0 A0 n) := min_le_right _ _
  have t3 : min σ (G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) ≤ σ := min_le_left _ _
  have e1 := gy_sub h hA0 ((n + 1) % 2) 0 (G P0 A0 n) (min σ (G P0 A0 n + (par P0 n).u2 (A P0 A0 n)))
  have e2 := ydiff h hA0 (p := (n + 1) % 2) (i := 0) t1.le le_rfl (by linarith)
  simp only [pcum, if_true, sub_self] at e2
  rw [HP.Ra_r1 hQ hv le_rfl o2.le, HP.Ra_r1 hQ hv (by linarith) (by linarith)] at e2
  have hta := hQ.hta
  have hpos : 0 < (min σ (G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) - G P0 A0 n) / (par P0 n).ta :=
    div_pos (by linarith) hta
  have hm := g1_gy_mono h hA0 ((n + 1) % 2) 0 t3
  rw [zero_div] at e2
  linarith

lemma g1_MA0_int {n q : ℕ} (hq2 : q < 2) (hq : q ≠ (n + 1) % 2) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : G P0 A0 n + (par P0 n).u3 (A P0 A0 n) < t)
    (h2 : t < G P0 A0 n + (par P0 n).u4 (A P0 A0 n)) : 0 < X P0 A0 q 1 t := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  rw [X_eq h hA0 n hq2 h0 (by linarith) (by linarith)]
  simp only [plev, if_neg hq, if_neg one_ne_zero]
  exact HP.Ld_pos hQ hv (by linarith)

lemma g1_MA_d0 {n q : ℕ} (hq2 : q < 2) (hq : q ≠ (n + 1) % 2) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : G P0 A0 n + (par P0 n).u4 (A P0 A0 n) ≤ t) (h2 : t ≤ G P0 A0 (n + 1)) :
    X P0 A0 q 1 t = 0 := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  rw [X_eq h hA0 n hq2 h0 (by linarith) h2]
  simp only [plev, if_neg hq, if_neg one_ne_zero]
  exact HP.Ld_hi hQ hv (by linarith)

lemma g1_MA1_exit {n p : ℕ} (hp2 : p < 2) (hp : p = (n + 1) % 2) (h0 : 0 ≤ G P0 A0 (n + 1)) :
    X P0 A0 p 0 (G P0 A0 (n + 1)) = 0 := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  rw [X_eq h hA0 n hp2 h0 (by linarith) le_rfl]
  have e : G P0 A0 (n + 1) - G P0 A0 n = (par P0 n).u8 (A P0 A0 n) := by linarith
  rw [e]
  simp only [plev, if_pos hp, if_true]
  exact HP.La_zero hQ hv (by linarith) le_rfl

lemma g1_MB0_int {n p : ℕ} (hp2 : p < 2) (hp : p = (n + 1) % 2) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : G P0 A0 n + (par P0 n).db < t)
    (h2 : t < G P0 A0 n + (par P0 n).u7 (A P0 A0 n)) : 0 < X P0 A0 p 1 t := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  have hdb := hQ.hdb
  rw [X_eq h hA0 n hp2 h0 (by linarith) (by linarith)]
  simp only [plev, if_pos hp, if_neg one_ne_zero]
  exact HP.Lb_pos hQ hv (by linarith) (by linarith)

lemma g1_MB0_exit {n p : ℕ} (hp2 : p < 2) (hp : p = (n + 1) % 2)
    (h0 : 0 ≤ G P0 A0 n + (par P0 n).u7 (A P0 A0 n)) :
    X P0 A0 p 1 (G P0 A0 n + (par P0 n).u7 (A P0 A0 n)) = 0 := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  rw [X_eq h hA0 n hp2 h0 (by linarith) (by linarith), add_sub_cancel_left]
  simp only [plev, if_pos hp, if_neg one_ne_zero]
  rw [HP.Lb_hi hQ hv le_rfl o8.le, sub_self]

lemma g1_MB1_int {n p : ℕ} (hp2 : p < 2) (hp : p = (n + 1) % 2) {t : ℝ} (h0 : 0 ≤ t)
    (h1 : G P0 A0 n ≤ t) (h2 : t < G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) :
    0 < X P0 A0 p 0 t := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  rw [X_eq h hA0 n hp2 h0 h1 (by linarith)]
  simp only [plev, if_pos hp, if_true]
  exact HP.La_pos1 hQ hv (by linarith) (by linarith)

lemma g1_MB1_exit {n p : ℕ} (hp2 : p < 2) (hp : p = (n + 1) % 2)
    (h0 : 0 ≤ G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) :
    X P0 A0 p 0 (G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) = 0 := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  rw [X_eq h hA0 n hp2 h0 (by linarith) (by linarith), add_sub_cancel_left]
  simp only [plev, if_pos hp, if_true]
  have e1 := HP.A_eq hQ hv
  have e2 := HP.Ra_r1 hQ hv o2.le le_rfl
  unfold HP.La
  rw [e2]
  linarith

lemma g1_MB1_next {n q : ℕ} (hq2 : q < 2) (hq : q ≠ (n + 1) % 2)
    (h0 : 0 ≤ G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) :
    0 < X P0 A0 q 1 (G P0 A0 n + (par P0 n).u2 (A P0 A0 n)) := by
  have hQ := par_ok h n
  have hv := valid h hA0 n
  obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
  have hG := G_succ P0 A0 n
  rw [X_eq h hA0 n hq2 h0 (by linarith) (by linarith), add_sub_cancel_left]
  simp only [plev, if_neg hq, if_neg one_ne_zero]
  rw [HP.Ld_lo hQ hv o3.le]
  exact hQ.hda

end G1
end Seq
end KSHalf

/-! ## Part G2: schedule-level helpers -/

namespace KumarSeidman.TwoType
namespace KSProof
open Example2 KSHalf KSHalf.Seq MeasureTheory Filter

lemma g2_beta_comp (P : HP) (A0 : ℝ) (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M)
    (k : ℕ) : (((sched P A0).β m k).1 : ℕ) = (if (k + m) % 2 = 0 then 1 - (m : ℕ) else m) ∧
      (((sched P A0).β m k).2 : ℕ) = (if (k + m) % 2 = 0 then 1 else 0) := by
  rcases m with ⟨m, hm⟩
  have hm' : m < 2 := hm
  have hb : (sched P A0).β ⟨m, hm⟩ k = (if (k + m) % 2 = 0 then (if m = 0 then b₄ else b₂)
      else (if m = 0 then b₁ else b₃) : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) :=
    rfl
  show ((((sched P A0).β ⟨m, hm⟩ k).1 : ℕ) = (if (k + m) % 2 = 0 then 1 - m else m)) ∧
    ((((sched P A0).β ⟨m, hm⟩ k).2 : ℕ) = (if (k + m) % 2 = 0 then 1 else 0))
  by_cases e : (k + m) % 2 = 0
  · have hb' : (sched P A0).β ⟨m, hm⟩ k = (if m = 0 then b₄ else b₂) := by rw [hb, if_pos e]
    rw [hb', if_pos e, if_pos e]
    interval_cases m <;> exact ⟨rfl, rfl⟩
  · have hb' : (sched P A0).β ⟨m, hm⟩ k = (if m = 0 then b₁ else b₃) := by rw [hb, if_neg e]
    rw [hb', if_neg e, if_neg e]
    interval_cases m <;> exact ⟨rfl, rfl⟩

lemma g2_buf_ext (P : HP) {b c : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer}
    (h1 : (b.1 : ℕ) = c.1) (h2 : (b.2 : ℕ) = c.2) : b = c := by
  rcases b with ⟨⟨p, hp⟩, ⟨i, hi⟩⟩
  rcases c with ⟨⟨p', hp'⟩, ⟨i', hi'⟩⟩
  dsimp only at h1 h2
  subst h1
  subst h2
  rfl

lemma g2_dem0 (P : HP) (A0 : ℝ) (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer)
    (hb : (b.2 : ℕ) = 0) (t : ℝ) : (sched P A0).Demanding b t := by
  refine Or.inr (fun σ hσ => ?_)
  simp only [System.inflow, if_pos hb]
  show 1 * t < 1 * σ
  linarith

lemma g2_inflow1 (P : HP) (A0 : ℝ) (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer)
    (hb : (b.2 : ℕ) = 1) (t : ℝ) :
    System.inflow _ (sched P A0).y b t = gy P A0 b.1 0 t := by
  have hb' : ¬ (b.2 : ℕ) = 0 := by omega
  simp only [System.inflow, if_neg hb']
  show gy P A0 (b.1 : ℕ) ((b.2 : ℕ) - 1) t = _
  rw [hb]

lemma g2_dem_incr (P : HP) (A0 : ℝ) (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer)
    (hb : (b.2 : ℕ) = 1) (t : ℝ) (hi : ∀ σ, t < σ → gy P A0 b.1 0 t < gy P A0 b.1 0 σ) :
    (sched P A0).Demanding b t :=
  Or.inr (fun σ hσ => by rw [g2_inflow1 P A0 b hb, g2_inflow1 P A0 b hb]; exact hi σ hσ)

lemma g2_not_dem (P : HP) (A0 : ℝ) (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer)
    (hb : (b.2 : ℕ) = 1) {t σ : ℝ} (hx : X P A0 b.1 b.2 t = 0) (hσ : t < σ)
    (heq : gy P A0 b.1 0 t = gy P A0 b.1 0 σ) : ¬ (sched P A0).Demanding b t := by
  rintro (h1 | h1)
  · have e : (sched P A0).x b t = X P A0 b.1 b.2 t := rfl
    rw [e, hx] at h1
    exact lt_irrefl _ h1
  · have h2 := h1 σ hσ
    rw [g2_inflow1 P A0 b hb, g2_inflow1 P A0 b hb, heq] at h2
    exact lt_irrefl _ h2

section
variable {P : HP} (h : P.Ok) {A0 : ℝ} (hA0 : Me P ≤ A0)
include h hA0

lemma g2_procStart_nonneg (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    0 ≤ (sched P A0).procStart m k := by
  cases k with
  | zero =>
    show 0 ≤ (sched P A0).s m 0
    simp [sched]
  | succ k =>
    show 0 ≤ (sched P A0).s m (k + 1) + _
    rw [delta_eq]
    have h1 := s_one_nonneg h hA0 m
    have e := s_succ P A0 m 0
    simp only [zero_add] at e
    rw [e] at h1
    rw [s_succ]
    have h2 := (HS_strictMono h hA0 (m : ℕ)).monotone (show 1 + (m : ℕ) ≤ k + 1 + m by omega)
    have h3 := hset_pos h (m : ℕ) ((k + 1 + m) / 2) ((k + 1 + m) % 2)
    linarith


lemma g3_proc_ge (m : Fin (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).M) (k : ℕ) :
    hp P A0 m ((k + m) / 2) ((k + m) % 2) ≤ (sched P A0).procStart m k := by
  cases k with
  | zero =>
    have e := hp_init h hA0 (m : ℕ) m.isLt
    have e0 : (sched P A0).s m 0 = 0 := by simp [sched]
    show hp P A0 m ((0 + m) / 2) ((0 + m) % 2) ≤ (sched P A0).s m 0
    rw [e0, zero_add]
    exact e
  | succ k =>
    rw [procStart_succ]

theorem isClearing : (sched P A0).IsClearing := by
  intro m k _
  have hm2 : (m : ℕ) < 2 := m.isLt
  obtain ⟨hb1, hb2⟩ := g2_beta_comp P A0 m k
  obtain ⟨hc1, hc2⟩ := g2_beta_comp P A0 m (k + 1)
  have hpg := g3_proc_ge h hA0 m k
  have hp0 := g2_procStart_nonneg h hA0 m k
  have hpl := procStart_le h hA0 m k
  have hs1 : (sched P A0).s m (k + 1) = hs P A0 m ((k + 1 + m) / 2) ((k + 1 + m) % 2) :=
    s_succ P A0 m k
  have hx : ∀ (b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer) (t : ℝ),
      (sched P A0).x b t = X P A0 b.1 b.2 t := fun _ _ => rfl
  have hne : (sched P A0).β m (k + 1) ≠ (sched P A0).β m k := by
    intro e
    have e2 := congrArg
      (fun b : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer => (b.2 : ℕ)) e
    rw [hb2, hc2] at e2
    split_ifs at e2 <;> omega
  have hoth : ∀ b' : (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).Buffer,
      (example2 P.ta P.tb P.tc P.td P.da P.db P.dc P.dd).mach b' = m →
      b' ≠ (sched P A0).β m k → b' = (sched P A0).β m (k + 1) := by
    intro b' hb' hne'
    have mv := mach_val P b'
    rw [hb'] at mv
    have l1 : (b'.1 : ℕ) < 2 := b'.1.isLt
    have l2 : (b'.2 : ℕ) < 2 := b'.2.isLt
    by_cases hs2 : (b'.2 : ℕ) = ((sched P A0).β m k).2
    · refine absurd (g2_buf_ext P ?_ hs2) hne'
      rw [hb1]; rw [hb2] at hs2; split_ifs at hs2 ⊢ <;> omega
    · apply g2_buf_ext P
      · rw [hc1]; rw [hb2] at hs2; split_ifs at hs2 ⊢ <;> omega
      · rw [hc2]; rw [hb2] at hs2; split_ifs at hs2 ⊢ <;> omega
  rcases Nat.mod_two_eq_zero_or_one (k + m) with hi | hi
  · -- stage-1 run (d or b): the next buffer is a first-stage buffer
    obtain ⟨n, hn⟩ : ∃ n, k + (m : ℕ) = 2 * n := ⟨(k + m) / 2, by omega⟩
    have e1 : (k + (m : ℕ)) / 2 = n := by omega
    have e3 : (k + 1 + (m : ℕ)) / 2 = n := by omega
    have e4 : (k + 1 + (m : ℕ)) % 2 = 1 := by omega
    rw [e1, hi] at hpg
    rw [e3, e4] at hs1
    have hxb : ∀ t, (sched P A0).x ((sched P A0).β m k) t = X P A0 (1 - (m : ℕ)) 1 t := by
      intro t; rw [hx, hb1, hb2, hi]; simp
    have hdem : ∀ t, (sched P A0).Demanding ((sched P A0).β m (k + 1)) t :=
      g2_dem0 P A0 _ (by rw [hc2, e4]; simp)
    have hQ := par_ok h n
    have hv := valid h hA0 n
    obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
    have hG := G_succ P A0 n
    have hdb := hQ.hdb
    by_cases hMA : (m : ℕ) = (n + 1) % 2
    · simp only [hp, poff, hs, hoff, if_pos hMA, eq_self_iff_true, if_true, one_ne_zero,
        if_false] at hpg hs1
      have hq : 1 - (m : ℕ) ≠ (n + 1) % 2 := by omega
      refine ⟨fun t ht1 ht2 => ?_, fun _ => ⟨?_, hne, hdem _⟩⟩
      · have ht2' := ht2 (runExists P A0 m (k + 1))
        rintro ⟨hx0, -⟩
        rw [hxb] at hx0
        have := g1_MA0_int h hA0 (t := t) (by omega) hq (by linarith) (by linarith) (by linarith)
        linarith
      · rw [hxb, hs1]
        exact g1_MA_d0 h hA0 (by omega) hq (by linarith) le_rfl (by linarith)
    · simp only [hp, poff, hs, hoff, if_neg hMA, eq_self_iff_true, if_true, one_ne_zero,
        if_false] at hpg hs1
      have hpp : 1 - (m : ℕ) = (n + 1) % 2 := by omega
      refine ⟨fun t ht1 ht2 => ?_, fun _ => ⟨?_, hne, hdem _⟩⟩
      · have ht2' := ht2 (runExists P A0 m (k + 1))
        rintro ⟨hx0, -⟩
        rw [hxb] at hx0
        have := g1_MB0_int h hA0 (t := t) (by omega) hpp (by linarith) (by linarith) (by linarith)
        linarith
      · rw [hxb, hs1]
        exact g1_MB0_exit h hA0 (by omega) hpp (by linarith)
  · -- stage-0 run (a or c): the next buffer is a second-stage buffer
    obtain ⟨n, hn⟩ : ∃ n, k + (m : ℕ) = 2 * n + 1 := ⟨(k + m) / 2, by omega⟩
    have e1 : (k + (m : ℕ)) / 2 = n := by omega
    have e3 : (k + 1 + (m : ℕ)) / 2 = n + 1 := by omega
    have e4 : (k + 1 + (m : ℕ)) % 2 = 0 := by omega
    rw [e1, hi] at hpg
    rw [e3, e4] at hs1
    have hxb : ∀ t, (sched P A0).x ((sched P A0).β m k) t = X P A0 (m : ℕ) 0 t := by
      intro t; rw [hx, hb1, hb2, hi]; simp
    have hc2' : (((sched P A0).β m (k + 1)).2 : ℕ) = 1 := by rw [hc2, e4]; simp
    have hc1' : (((sched P A0).β m (k + 1)).1 : ℕ) = 1 - (m : ℕ) := by rw [hc1, e4]; simp
    have hQ := par_ok h n
    have hv := valid h hA0 n
    obtain ⟨o2, o3, o4, o5, o6, o7, o8⟩ := HP.ord hQ hv
    have hG := G_succ P A0 n
    have hQ' := par_ok h (n + 1)
    have hv' := valid h hA0 (n + 1)
    obtain ⟨p2, p3, p4, p5, p6, p7, p8⟩ := HP.ord hQ' hv'
    by_cases hMA : (m : ℕ) = (n + 1) % 2
    · have hMA' : ¬ (m : ℕ) = (n + 1 + 1) % 2 := by omega
      simp only [hp, poff, hs, hoff, if_pos hMA, if_neg hMA', eq_self_iff_true, if_true,
        one_ne_zero, if_false, add_zero] at hpg hs1
      have hq : 1 - (m : ℕ) ≠ (n + 1) % 2 := by omega
      refine ⟨fun t ht1 ht2 => ?_, fun _ => ⟨?_, hne, ?_⟩⟩
      · have ht2' := ht2 (runExists P A0 m (k + 1))
        rintro ⟨-, b', hb', hne', hd⟩
        rw [hoth b' hb' hne'] at hd
        refine g2_not_dem P A0 _ hc2' ?_ (σ := G P A0 (n + 1)) (by linarith) ?_ hd
        · rw [hc1', hc2']
          exact g1_MA_d0 h hA0 (by omega) hq (by linarith) (by linarith) (by linarith)
        · rw [hc1']
          exact g1_inact_const h hA0 hq (by linarith) (by linarith) le_rfl
      · rw [hxb, hs1]
        exact g1_MA1_exit h hA0 (by omega) hMA (by linarith)
      · rw [hs1]
        refine g2_dem_incr P A0 _ hc2' _ (fun σ hσ => ?_)
        rw [hc1']
        exact g1_act_incr h hA0 (n := n + 1) (by omega) hσ
    · have hMA' : (m : ℕ) = (n + 1 + 1) % 2 := by omega
      simp only [hp, poff, hs, hoff, if_neg hMA, if_pos hMA', eq_self_iff_true, if_true,
        one_ne_zero, if_false] at hpg hs1
      have hq : 1 - (m : ℕ) ≠ (n + 1 + 1) % 2 := by omega
      refine ⟨fun t ht1 ht2 => ?_, fun _ => ⟨?_, hne, ?_⟩⟩
      · have ht2' := ht2 (runExists P A0 m (k + 1))
        rintro ⟨hx0, -⟩
        rw [hxb] at hx0
        have := g1_MB1_int h hA0 (n := n + 1) (t := t) (by omega) hMA' (by linarith) (by linarith)
          (by linarith)
        linarith
      · rw [hxb, hs1]
        exact g1_MB1_exit h hA0 (by omega) hMA' (by linarith)
      · rw [hs1]
        left
        rw [hx, hc1', hc2']
        exact g1_MB1_next h hA0 (by omega) hq (by linarith)

end
end KSProof
end KumarSeidman.TwoType

/-! ## Part H: the solution -/

open KumarSeidman.TwoType KumarSeidman.TwoType.Example2 in
theorem solution (τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄ : ℝ)
    (hτ₁ : 0 < τ₁) (hτ₂ : 0 < τ₂) (hτ₃ : 0 < τ₃) (hτ₄ : 0 < τ₄)
    (hδ₁ : 0 < δ₁) (hδ₂ : 0 < δ₂) (hδ₃ : 0 < δ₃) (hδ₄ : 0 < δ₄)
    (h7 : τ₂ + τ₄ > 1) (h1₁ : τ₁ + τ₄ < 1) (h1₂ : τ₂ + τ₃ < 1) :
    ∃ ξ₀ : ℝ, ∀ ξ ≥ ξ₀, ∃ T : (example2 τ₁ τ₂ τ₃ τ₄ δ₁ δ₂ δ₃ δ₄).Schedule,
      T.IsClearingFrom (levels ξ 0 0 0) (setups b₄ b₃) := by
  have h : (⟨τ₁, τ₂, τ₃, τ₄, δ₁, δ₂, δ₃, δ₄⟩ : KSHalf.HP).Ok :=
    ⟨hτ₁, hτ₂, hτ₃, hτ₄, hδ₁, hδ₂, hδ₃, hδ₄, h1₁, h1₂, h7⟩
  refine ⟨KSHalf.Seq.xi0 ⟨τ₁, τ₂, τ₃, τ₄, δ₁, δ₂, δ₃, δ₄⟩, fun ξ hξ => ?_⟩
  have hA0 := KSHalf.Seq.A0of_ge h hξ
  refine ⟨KSProof.sched ⟨τ₁, τ₂, τ₃, τ₄, δ₁, δ₂, δ₃, δ₄⟩
    (KSHalf.Seq.A0of ⟨τ₁, τ₂, τ₃, τ₄, δ₁, δ₂, δ₃, δ₄⟩ ξ), ?_, ?_, ?_⟩
  · exact KSProof.isTrajectory h hA0
  · exact KSProof.starts h hA0 rfl
  · exact KSProof.isClearing h hA0
