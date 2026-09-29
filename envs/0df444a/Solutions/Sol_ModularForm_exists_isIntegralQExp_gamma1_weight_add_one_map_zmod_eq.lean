-- Prove2me | solution 1 for ModularForm.exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/05cbc7b2-b1e5-5f71-8659-a52be84cff7d

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Modularity
import Theorems.Thm_ModularForm_exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm MatrixGroups BigOperators

namespace HasseLiftOrthE96

theorem isPrimitive_of_odd_prime {p : ℕ} [hp : Fact p.Prime] (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) :
    χ.IsPrimitive := by
  have hne : χ ≠ 1 := by
    intro h
    rw [h, DirichletCharacter.Odd] at hodd
    have : ((1 : DirichletCharacter ℂ p) (-1 : ZMod p)) = 1 := by
      rw [MulChar.one_apply]; exact (isUnit_one.neg)
    rw [this] at hodd
    norm_num at hodd
  rw [DirichletCharacter.isPrimitive_def]
  rcases hp.out.eq_one_or_self_of_dvd _ (DirichletCharacter.conductor_dvd_level χ) with h1 | h2
  · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1) hne
  · exact h2

open Classical in

theorem sum_odd_apply_eq {p : ℕ} [hp : Fact p.Prime] (d : ZMod p) :
    (∑ χ : DirichletCharacter ℂ p, if χ.Odd then χ d else 0)
      = ((p - 1 : ℕ) : ℂ) / 2 * ((if d = 1 then 1 else 0) - (if d = -1 then 1 else 0)) := by

  have key : ∀ χ : DirichletCharacter ℂ p,
      (if χ.Odd then χ d else 0) = (χ d - χ (-d)) / 2 := by
    intro χ
    rcases χ.even_or_odd with he | ho
    · rw [if_neg he.not_odd, he.eval_neg, sub_self, zero_div]
    · rw [if_pos ho, ho.eval_neg]; ring
  simp_rw [key, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [DirichletCharacter.sum_characters_eq, DirichletCharacter.sum_characters_eq]
  have htot : (p.totient : ℂ) = ((p - 1 : ℕ) : ℂ) := by rw [Nat.totient_prime hp.out]
  have hneg : (-d = 1) ↔ (d = -1) := neg_eq_iff_eq_neg
  simp only [htot, hneg]
  split_ifs <;> ring

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

theorem one_mem_strictPeriods :
    (1 : ℝ) ∈ ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  have h := CongruenceSubgroup.strictPeriods_Gamma1 p
  change ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods = _ at h
  rw [h]
  exact AddSubgroup.mem_zmultiples 1

def eis (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) : ModularForm (Gamma1 p) 1 :=
  Classical.choose (ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd p χ
    (isPrimitive_of_odd_prime χ hodd) hodd)

theorem eis_qCoeff_zero (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) :
    ModularFormClass.qCoeff (eis p χ hodd) 0 =
      -(∑ a ∈ Finset.range p, (a : ℂ) * χ (a : ZMod p)) / (2 * p) :=
  (Classical.choose_spec (ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd p χ
    (isPrimitive_of_odd_prime χ hodd) hodd)).2.1

theorem eis_qCoeff_pos (χ : DirichletCharacter ℂ p) (hodd : χ.Odd) (n : ℕ) (hn : 0 < n) :
    ModularFormClass.qCoeff (eis p χ hodd) n = ∑ d ∈ n.divisors, χ (d : ZMod p) :=
  (Classical.choose_spec (ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd p χ
    (isPrimitive_of_odd_prime χ hodd) hodd)).2.2 n hn

open Classical in

def term (χ : DirichletCharacter ℂ p) : ModularForm (Gamma1 p) 1 :=
  if h : χ.Odd then eis p χ h else 0

def G0 : ModularForm (Gamma1 p) 1 := ∑ χ : DirichletCharacter ℂ p, term p χ

theorem qExpansion_sum {ι : Type*} (s : Finset ι) {k : ℤ} (F : ι → ModularForm (Gamma1 p) k) :
    UpperHalfPlane.qExpansion 1 (⇑(∑ i ∈ s, F i)) = ∑ i ∈ s, UpperHalfPlane.qExpansion 1 (⇑(F i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [UpperHalfPlane.qExpansion_zero]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ModularForm.coe_add,
      UpperHalfPlane.qExpansion_add
        (ModularFormClass.analyticAt_cuspFunction_zero (F a) one_pos (one_mem_strictPeriods p))
        (ModularFormClass.analyticAt_cuspFunction_zero (∑ i ∈ s, F i) one_pos (one_mem_strictPeriods p)),
      ih]

open Classical in
theorem coeff_qExpansion_term (χ : DirichletCharacter ℂ p) (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑(term p χ))) =
      if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) n else 0 := by
  unfold term
  split_ifs with h
  · rfl
  · simp [UpperHalfPlane.qExpansion_zero]

open Classical in
theorem coeff_qExpansion_G0 (n : ℕ) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑(G0 p))) =
      ∑ χ : DirichletCharacter ℂ p, if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) n else 0 := by
  unfold G0
  rw [qExpansion_sum, map_sum]
  exact Finset.sum_congr rfl fun χ _ => coeff_qExpansion_term p χ n

end

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

def A (n : ℕ) : ℕ := (n.divisors.filter (fun d : ℕ => ((d : ZMod p)) = 1)).card

def B (n : ℕ) : ℕ := (n.divisors.filter (fun d : ℕ => ((d : ZMod p)) = -1)).card

theorem natCast_zmod_eq_one_iff {a : ℕ} (ha : a < p) : ((a : ZMod p) = 1) ↔ a = 1 := by
  haveI : Fact (1 < p) := ⟨hp.out.one_lt⟩
  constructor
  · intro h
    have := congrArg ZMod.val h
    rwa [ZMod.val_natCast, Nat.mod_eq_of_lt ha, ZMod.val_one] at this
  · rintro rfl; simp

theorem natCast_zmod_eq_neg_one_iff {a : ℕ} (ha : a < p) : ((a : ZMod p) = -1) ↔ a = p - 1 := by
  constructor
  · intro h
    have h1 : ((a + 1 : ℕ) : ZMod p) = 0 := by
      push_cast; rw [h]; ring
    rw [ZMod.natCast_eq_zero_iff] at h1
    have h2 : a + 1 = p := by
      obtain ⟨c, hc⟩ := h1
      rcases c with _ | c
      · simp at hc
      · nlinarith [hp.out.pos]
    omega
  · rintro rfl
    have h1 : ((p - 1 : ℕ) : ZMod p) + 1 = 0 := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel hp.out.one_le, ZMod.natCast_self]
    exact eq_neg_of_add_eq_zero_left h1

theorem sum_range_mul_ite_one :
    (∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = 1 then 1 else 0)) = 1 := by
  have : ∀ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = 1 then (1 : ℂ) else 0) =
      if a = 1 then (a : ℂ) else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases h1 : a = 1
    · subst h1; simp
    · have h1' : ¬ ((a : ZMod p) = 1) := fun h => h1 ((natCast_zmod_eq_one_iff p ha).mp h)
      simp [h1, h1']
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr hp.out.one_lt)]
  simp

theorem sum_range_mul_ite_neg_one :
    (∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = -1 then 1 else 0)) = (p : ℂ) - 1 := by
  have : ∀ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = -1 then (1 : ℂ) else 0) =
      if a = p - 1 then (a : ℂ) else 0 := by
    intro a ha
    rw [Finset.mem_range] at ha
    by_cases h1 : a = p - 1
    · subst h1
      have h1' : (((p - 1 : ℕ) : ZMod p) = -1) := (natCast_zmod_eq_neg_one_iff p ha).mpr rfl
      simp [h1']
    · have h1' : ¬ ((a : ZMod p) = -1) := fun h => h1 ((natCast_zmod_eq_neg_one_iff p ha).mp h)
      simp [h1, h1']
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq']
  rw [if_pos (Finset.mem_range.mpr (Nat.sub_lt hp.out.pos one_pos))]
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]

open Classical in

theorem coeff_G0_zero :
    PowerSeries.coeff 0 (UpperHalfPlane.qExpansion 1 (⇑(G0 p))) =
      ((p - 1 : ℕ) : ℂ) * ((p : ℂ) - 2) / (4 * p) := by
  rw [coeff_qExpansion_G0]
  have step1 : ∀ χ : DirichletCharacter ℂ p,
      (if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) 0 else 0) =
        ∑ a ∈ Finset.range p, (-(1 : ℂ) / (2 * p)) * ((a : ℂ) * (if χ.Odd then χ (a : ZMod p) else 0)) := by
    intro χ
    by_cases h : χ.Odd
    · rw [dif_pos h, eis_qCoeff_zero]
      simp only [if_pos h, ← Finset.mul_sum]
      ring
    · rw [dif_neg h]
      symm
      apply Finset.sum_eq_zero
      intro a _
      simp only [if_neg h, mul_zero]
  simp_rw [step1]
  rw [Finset.sum_comm]
  have inner : ∀ a ∈ Finset.range p,
      (∑ χ : DirichletCharacter ℂ p, (-(1 : ℂ) / (2 * p)) * ((a : ℂ) * (if χ.Odd then χ (a : ZMod p) else 0))) =
        (-(1 : ℂ) / (2 * p)) * ((a : ℂ) * (((p - 1 : ℕ) : ℂ) / 2 *
          ((if (a : ZMod p) = 1 then 1 else 0) - (if (a : ZMod p) = -1 then 1 else 0)))) := by
    intro a _
    rw [← Finset.mul_sum, ← Finset.mul_sum, sum_odd_apply_eq]
  rw [Finset.sum_congr rfl inner, ← Finset.mul_sum]
  have split : (∑ a ∈ Finset.range p, (a : ℂ) * (((p - 1 : ℕ) : ℂ) / 2 *
      ((if (a : ZMod p) = 1 then (1 : ℂ) else 0) - (if (a : ZMod p) = -1 then 1 else 0)))) =
      ((p - 1 : ℕ) : ℂ) / 2 * ((∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = 1 then (1 : ℂ) else 0)) -
        (∑ a ∈ Finset.range p, (a : ℂ) * (if (a : ZMod p) = -1 then (1 : ℂ) else 0))) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  rw [split, sum_range_mul_ite_one, sum_range_mul_ite_neg_one]
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  field_simp
  ring

open Classical in

theorem coeff_G0_pos (n : ℕ) (hn : 0 < n) :
    PowerSeries.coeff n (UpperHalfPlane.qExpansion 1 (⇑(G0 p))) =
      ((p - 1 : ℕ) : ℂ) / 2 * ((A p n : ℂ) - (B p n : ℂ)) := by
  rw [coeff_qExpansion_G0]
  have step1 : ∀ χ : DirichletCharacter ℂ p,
      (if h : χ.Odd then ModularFormClass.qCoeff (eis p χ h) n else 0) =
        ∑ d ∈ n.divisors, (if χ.Odd then χ (d : ZMod p) else 0) := by
    intro χ
    by_cases h : χ.Odd
    · rw [dif_pos h, eis_qCoeff_pos p χ h n hn]
      simp only [if_pos h]
    · rw [dif_neg h]
      symm
      apply Finset.sum_eq_zero
      intro a _
      simp only [if_neg h, mul_zero]
  simp_rw [step1]
  rw [Finset.sum_comm]
  simp_rw [sum_odd_apply_eq, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [A, B, Finset.sum_boole, Nat.cast_id]

end

noncomputable section

variable (p : ℕ) [hp : Fact p.Prime]

def G : ModularForm (Gamma1 p) 1 := ((4 * p : ℂ) / ((p : ℂ) - 1)) • G0 p

def pG : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then (p : ℤ) - 2 else 2 * p * ((A p n : ℤ) - (B p n : ℤ))

theorem qExpansion_G : UpperHalfPlane.qExpansion 1 (⇑(G p)) =
    ((4 * p : ℂ) / ((p : ℂ) - 1)) • UpperHalfPlane.qExpansion 1 (⇑(G0 p)) := by
  unfold G
  rw [ModularForm.IsGLPos.coe_smul]
  exact UpperHalfPlane.qExpansion_smul
    (ModularFormClass.analyticAt_cuspFunction_zero (G0 p) one_pos (one_mem_strictPeriods p)) _

theorem isIntegralQExp_G (hp3 : 3 ≤ p) : ModularCurve.IsIntegralQExp (⇑(G p)) (pG p) := by
  rw [ModularCurve.isIntegralQExp_iff]
  intro n
  have hp1 : ((p : ℂ) - 1) ≠ 0 := by
    have : (p : ℂ) ≠ 1 := by exact_mod_cast (show p ≠ 1 by omega)
    exact sub_ne_zero.mpr this
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hcast : ((p - 1 : ℕ) : ℂ) = (p : ℂ) - 1 := by rw [Nat.cast_sub hp.out.one_le, Nat.cast_one]
  rw [qExpansion_G, map_smul, smul_eq_mul]
  unfold pG
  rw [PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [if_pos rfl, coeff_G0_zero, hcast]
    push_cast
    field_simp
    try ring
  · rw [if_neg hn.ne', coeff_G0_pos p n hn, hcast]
    push_cast
    field_simp
    try ring

def H : ModularForm (Gamma1 p) 0 := (((p : ℂ) - 2)) • (1 : ModularForm (Gamma1 p) 0)

def pH : PowerSeries ℤ := PowerSeries.C ((p : ℤ) - 2)

theorem isIntegralQExp_H : ModularCurve.IsIntegralQExp (⇑(H p)) (pH p) := by
  unfold H pH ModularCurve.IsIntegralQExp
  rw [ModularForm.IsGLPos.coe_smul, ModularForm.one_coe_eq_one,
    UpperHalfPlane.qExpansion_smul (by
      rw [← ModularForm.one_coe_eq_one (Γ := ((Gamma1 p : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)))]
      exact ModularFormClass.analyticAt_cuspFunction_zero (1 : ModularForm (Gamma1 p) 0) one_pos
        (one_mem_strictPeriods p)),
    UpperHalfPlane.qExpansion_one, PowerSeries.map_C]
  ext n
  simp [PowerSeries.coeff_C, Algebra.smul_def]

theorem map_pH : (pH p).map (Int.castRingHom (ZMod p)) = PowerSeries.C (-2 : ZMod p) := by
  unfold pH
  rw [PowerSeries.map_C]
  congr 1
  simp

theorem map_pH_ne_zero (hp3 : 3 ≤ p) : (pH p).map (Int.castRingHom (ZMod p)) ≠ 0 := by
  rw [map_pH]
  intro h
  have h2 : (-2 : ZMod p) = 0 := by
    have := congrArg (PowerSeries.coeff 0) h
    simpa using this
  have h2' : ((2 : ℕ) : ZMod p) = 0 := by
    have := congrArg Neg.neg h2
    simpa using this
  rw [ZMod.natCast_eq_zero_iff] at h2'
  have := Nat.le_of_dvd two_pos h2'
  omega

theorem map_pG (hp3 : 3 ≤ p) : (pG p).map (Int.castRingHom (ZMod p)) = PowerSeries.C (-2 : ZMod p) := by
  ext n
  unfold pG
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_C]
  split_ifs with h
  · simp
  · push_cast
    simp [ZMod.natCast_self]

end

end HasseLiftOrthE96

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) :
    ∃ (k : ℤ) (G : ModularForm (Gamma1 p) (k + 1)) (H : ModularForm (Gamma1 p) k)
      (pG pH : PowerSeries ℤ),
      ModularCurve.IsIntegralQExp G pG ∧ ModularCurve.IsIntegralQExp H pH ∧
      pH.map (Int.castRingHom (ZMod p)) ≠ 0 ∧
      pG.map (Int.castRingHom (ZMod p)) = pH.map (Int.castRingHom (ZMod p)) := by
  have hp3 : 3 ≤ p := le_trans (by norm_num) hp5
  refine ⟨0, HasseLiftOrthE96.G p, HasseLiftOrthE96.H p, HasseLiftOrthE96.pG p, HasseLiftOrthE96.pH p,
    HasseLiftOrthE96.isIntegralQExp_G p hp3, HasseLiftOrthE96.isIntegralQExp_H p,
    HasseLiftOrthE96.map_pH_ne_zero p hp3, ?_⟩
  rw [HasseLiftOrthE96.map_pG p hp3, HasseLiftOrthE96.map_pH]

end S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq
end P2MW
export P2MW.S_ModularForm_exists_isIntegralQExp_gamma1_weight_add_one_map_zmod_eq (solution)
