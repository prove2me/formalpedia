-- Prove2me | solution 1 for ModularCurve.nonToricPoint_equation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/910b0e5d-8c2d-5ba3-9ebf-fbe30d02f3b2

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Theorems.Thm_ModularCurve_tateUniv_equation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonToricPoint_equation
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX tateUnivY tateUnivA4 tateUnivA6 tateUnivCurve slotFamily slotSubst nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateA4 tateA6 tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg tateUniv_equation"
p2m_open "ModularCurve~equation_tateBase_iff"

section BaseFaces

variable (K : Type*) [CommRing K] (p : ℕ) [NeZero p]

theorem tateBase_a₁ : (tateBase K p).a₁ = 1 := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map_a₁, tatePowerSeries_a₁, map_one]

theorem tateBase_a₂ : (tateBase K p).a₂ = 0 := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map_a₂, tatePowerSeries_a₂, map_zero]

theorem tateBase_a₃ : (tateBase K p).a₃ = 0 := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map_a₃, tatePowerSeries_a₃, map_zero]

theorem tateBase_a₄ : (tateBase K p).a₄ = qExpand K p (laurentOfInt K tateA4) := by
  simp only [tateBase, WeierstrassCurve.map_a₄, tateLaurent_a₄]

theorem tateBase_a₆ : (tateBase K p).a₆ = qExpand K p (laurentOfInt K tateA6) := by
  simp only [tateBase, WeierstrassCurve.map_a₆, tateLaurent_a₆]

private theorem equation_tateBase_iff (x y : LaurentSeries K) :
    (tateBase K p).toAffine.Equation x y ↔
      y ^ 2 + x * y = x ^ 3 + qExpand K p (laurentOfInt K tateA4) * x
        + qExpand K p (laurentOfInt K tateA6) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have e1 : (tateBase K p).toAffine.a₁ = 1 := tateBase_a₁ K p
  have e2 : (tateBase K p).toAffine.a₂ = 0 := tateBase_a₂ K p
  have e3 : (tateBase K p).toAffine.a₃ = 0 := tateBase_a₃ K p
  have e4 : (tateBase K p).toAffine.a₄ = qExpand K p (laurentOfInt K tateA4) := tateBase_a₄ K p
  have e6 : (tateBase K p).toAffine.a₆ = qExpand K p (laurentOfInt K tateA6) := tateBase_a₆ K p
  rw [e1, e2, e3, e4, e6]
  constructor <;> intro h <;> linear_combination h

end BaseFaces

section SlotSubstAPI

variable (K : Type*) [CommRing K]

theorem hasSubst_slotFamily (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries.HasSubst (slotFamily K p c j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s
  · show PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  · show PowerSeries.constantCoeff (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp), mul_zero]

def slotHom (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries (Fin 2) ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp
    (MvPowerSeries.substAlgHom (hasSubst_slotFamily K p c j hj hjp)).toRingHom

theorem slotHom_apply (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) :
    slotHom K p c j hj hjp f = HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j f) := by
  simp only [slotHom, slotSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPowerSeries.substAlgHom_apply]

end SlotSubstAPI

section SpecS0

def reidxLineSet (a b N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter fun e => a * e.1 + b * e.2 = N

def toFin2 (e : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e.1, e.2]

@[scoped simp] theorem toFin2_apply_zero (e : ℕ × ℕ) : toFin2 e 0 = e.1 := by simp [toFin2]

@[scoped simp] theorem toFin2_apply_one (e : ℕ × ℕ) : toFin2 e 1 = e.2 := by simp [toFin2]

theorem toFin2_injective : Function.Injective toFin2 := by
  intro x y h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp only [toFin2_apply_zero, toFin2_apply_one] at h0 h1
  exact Prod.ext h0 h1

theorem toFin2_pair (d : Fin 2 →₀ ℕ) : toFin2 (d 0, d 1) = d := by
  ext i
  fin_cases i
  · exact toFin2_apply_zero _
  · exact toFin2_apply_one _

theorem mem_reidxLineSet {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) {e : ℕ × ℕ} :
    e ∈ reidxLineSet a b N ↔ a * e.1 + b * e.2 = N := by
  simp only [reidxLineSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    and_iff_right_iff_imp]
  intro h
  have h1 : e.1 ≤ a * e.1 := Nat.le_mul_of_pos_left _ ha
  have h2 : e.2 ≤ b * e.2 := Nat.le_mul_of_pos_left _ hb
  exact ⟨Nat.lt_succ_of_le (h1.trans (le_of_le_of_eq (Nat.le_add_right _ _) h)),
    Nat.lt_succ_of_le (h2.trans (le_of_le_of_eq (Nat.le_add_left _ _) h))⟩

end SpecS0

section SpecS1

theorem prod_pow_fin_two {M : Type*} [CommMonoid M] (a : Fin 2 → M) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => a s ^ n) = a 0 ^ (d 0) * a 1 ^ (d 1) := by
  rw [Finsupp.prod_fintype d (fun s n => a s ^ n) fun _ => pow_zero _, Fin.prod_univ_two]

theorem coeff_subst_pair {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (A B : PowerSeries S) (hA : PowerSeries.constantCoeff A = 0)
    (hB : PowerSeries.constantCoeff B = 0) (f : MvPowerSeries (Fin 2) R) (N : ℕ) :
    PowerSeries.coeff N (MvPowerSeries.subst ![A, B] f : PowerSeries S) =
      ∑ e ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        MvPowerSeries.coeff (toFin2 e) f • PowerSeries.coeff N (A ^ e.1 * B ^ e.2) := by
  have ha : MvPowerSeries.HasSubst (![A, B] : Fin 2 → PowerSeries S) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
      fin_cases s
      · exact hA
      · exact hB
  have key : ∀ d : Fin 2 →₀ ℕ, ¬(d 0 ≤ N ∧ d 1 ≤ N) →
      PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0 := by
    intro d hd
    obtain ⟨A', hA'⟩ := PowerSeries.X_dvd_iff.mpr hA
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.mpr hB
    rw [hA', hB', mul_pow, mul_pow, mul_mul_mul_comm, ← _root_.pow_add, PowerSeries.coeff_X_pow_mul',
      if_neg (by omega)]
  change MvPowerSeries.coeff (Finsupp.single () N) (MvPowerSeries.subst ![A, B] f) = _
  rw [MvPowerSeries.coeff_subst ha,
    finsum_eq_sum_of_support_subset _
      (s := (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).image toFin2)]
  · rw [Finset.sum_image fun x _ y _ h => toFin2_injective h]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff (toFin2 e) f •
        PowerSeries.coeff N (A ^ (toFin2 e 0) * B ^ (toFin2 e 1)) = _
    rw [toFin2_apply_zero, toFin2_apply_one]
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_image, Set.mem_image]
    refine ⟨(d 0, d 1), ?_, toFin2_pair d⟩
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    by_contra hbox
    apply hd
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff d f • PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0
    rw [key d (by omega), smul_zero]

end SpecS1

section SpecS2

variable (K : Type*) [CommRing K]

theorem coeff_slotSubst (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) (N : ℕ) :
    PowerSeries.coeff N (slotSubst K p c j f) =
      ∑ e ∈ reidxLineSet j (p - j) N,
        ((f (toFin2 e) : ℤ) : K) * ((c ^ e.1 * c⁻¹ ^ e.2 : Kˣ) : K) := by
  have hA : PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  have hB : PowerSeries.constantCoeff
      (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp),
      mul_zero]
  rw [slotSubst, slotFamily, coeff_subst_pair _ _ hA hB, reidxLineSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← map_mul,
    ← _root_.pow_add, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : j * e.1 + (p - j) * e.2 = N
  · rw [if_pos h.symm, if_pos h, Algebra.smul_def, eq_intCast, MvPowerSeries.coeff_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  · rw [if_neg (Ne.symm h), if_neg h, smul_zero]

end SpecS2

section SpecS3

variable (K : Type*) [CommRing K]

theorem coeff_slotSubst_diag (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) (g : PowerSeries ℤ)
    (hf : ∀ e : Fin 2 →₀ ℕ, f e = if e 0 = e 1 then PowerSeries.coeff (e 0) g else 0) (N : ℕ) :
    PowerSeries.coeff N (slotSubst K p c j f) =
      if p ∣ N then ((PowerSeries.coeff (N / p) g : ℤ) : K) else 0 := by
  have hpj : 0 < p - j := Nat.sub_pos_of_lt hjp
  have hline : ∀ m : ℕ, j * m + (p - j) * m = p * m := fun m => by
    rw [← add_mul, Nat.add_sub_cancel' hjp.le]
  rw [coeff_slotSubst K p c j hj hjp]
  by_cases hN : p ∣ N
  · obtain ⟨m, rfl⟩ := hN
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (NeZero.pos p),
      Finset.sum_eq_single_of_mem (m, m) ((mem_reidxLineSet hj hpj).mpr (hline m))]
    · rw [hf, toFin2_apply_zero, toFin2_apply_one, if_pos rfl, ← mul_pow, mul_inv_cancel, one_pow,
        Units.val_one, mul_one]
    · intro e he hne
      have h := (mem_reidxLineSet hj hpj).mp he
      rw [hf, toFin2_apply_zero, toFin2_apply_one]
      by_cases h01 : e.1 = e.2
      · exfalso
        refine hne (Prod.ext ?_ ?_)
        · change e.1 = m
          rw [h01, hline e.2] at h
          exact h01.trans (Nat.eq_of_mul_eq_mul_left (NeZero.pos p) h)
        · change e.2 = m
          rw [h01, hline e.2] at h
          exact Nat.eq_of_mul_eq_mul_left (NeZero.pos p) h
      · rw [if_neg h01, Int.cast_zero, zero_mul]
  · rw [if_neg hN]
    refine Finset.sum_eq_zero fun e he => ?_
    have h := (mem_reidxLineSet hj hpj).mp he
    rw [hf, toFin2_apply_zero, toFin2_apply_one]
    by_cases h01 : e.1 = e.2
    · exfalso
      rw [h01, hline e.2] at h
      exact hN ⟨e.2, h.symm⟩
    · rw [if_neg h01, Int.cast_zero, zero_mul]

theorem ofPowerSeries_slotSubst_diag (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) (f : MvPowerSeries (Fin 2) ℤ) (g : PowerSeries ℤ)
    (hf : ∀ e : Fin 2 →₀ ℕ, f e = if e 0 = e 1 then PowerSeries.coeff (e 0) g else 0) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j f) = qExpand K p (laurentOfInt K g) := by
  ext n
  by_cases hpn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hpn
    rw [qExpand_coeff_mul, laurentOfInt_apply]
    rcases lt_or_ge k 0 with hk | hk
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _
        (mul_neg_of_pos_of_neg (by exact_mod_cast NeZero.pos p) hk)]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [show (p : ℤ) * (m : ℤ) = ((p * m : ℕ) : ℤ) by push_cast; rfl,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map, coeff_slotSubst_diag K p c j hj hjp f g hf,
        if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m (NeZero.pos p), eq_intCast]
  · rw [qExpand_coeff_of_not_dvd p _ hpn]
    rcases lt_or_ge n 0 with hn | hn
    · exact ofPowerSeries_coeff_of_neg _ hn
    · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_slotSubst_diag K p c j hj hjp f g hf,
        if_neg (fun h => hpn (Int.natCast_dvd_natCast.mpr h))]

theorem ofPowerSeries_slotSubst_tateUnivA4 (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivA4) = (tateBase K p).a₄ :=
  (ofPowerSeries_slotSubst_diag K p c j hj hjp tateUnivA4 tateA4 fun _ => rfl).trans rfl

theorem ofPowerSeries_slotSubst_tateUnivA6 (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivA6) = (tateBase K p).a₆ :=
  (ofPowerSeries_slotSubst_diag K p c j hj hjp tateUnivA6 tateA6 fun _ => rfl).trans rfl

end SpecS3

section SpecS4

variable (K : Type*) [CommRing K]

theorem tateUnivCurve_map_slotHom (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) : tateUnivCurve.map (slotHom K p c j hj hjp) = tateBase K p := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · change slotHom K p c j hj hjp 1 = qExpand K p (laurentOfInt K 1)
    simp only [map_one]
  · change slotHom K p c j hj hjp 0 = qExpand K p (laurentOfInt K 0)
    simp only [map_zero]
  · change slotHom K p c j hj hjp 0 = qExpand K p (laurentOfInt K 0)
    simp only [map_zero]
  · change slotHom K p c j hj hjp tateUnivA4 = (tateBase K p).a₄
    rw [slotHom_apply, ofPowerSeries_slotSubst_tateUnivA4 K p c j hj hjp]
  · change slotHom K p c j hj hjp tateUnivA6 = (tateBase K p).a₆
    rw [slotHom_apply, ofPowerSeries_slotSubst_tateUnivA6 K p c j hj hjp]

end SpecS4

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_nonToricPoint_equation.ModularCurve"

p2m_open "ModularCurve~equation_tateBase_iff" in open _root_.P2MW.S_ModularCurve_nonToricPoint_equation.ModularCurve in
theorem solution (K : Type*) [Field K] [CharZero K] (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    (tateBase K p).toAffine.Equation (nonToricPoint K p c j).1 (nonToricPoint K p c j).2 := by
  rw [nonToricPoint_fst, nonToricPoint_snd, ← slotHom_apply K p c j hj hjp, ← slotHom_apply K p c j hj hjp,
    ← tateUnivCurve_map_slotHom K p c j hj hjp]
  exact (tateUniv_equation).map (slotHom K p c j hj hjp)

end
p2m_reactivate "P2MW.S_ModularCurve_nonToricPoint_equation.ModularCurve"

end S_ModularCurve_nonToricPoint_equation
end P2MW
export P2MW.S_ModularCurve_nonToricPoint_equation (solution)
