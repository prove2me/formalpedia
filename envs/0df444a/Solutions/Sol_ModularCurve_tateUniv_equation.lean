-- Prove2me | solution 1 for ModularCurve.tateUniv_equation
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/09d0eac6-c2c0-58dc-908f-3a24057922c5

import Theorems.Thm_ModularCurve_equation_tateBase_iff
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Theorems.Thm_ModularCurve_toricPoint_fst_coeff_zero
import Theorems.Thm_ModularCurve_toricPoint_fst_coeff_of_not_dvd
import Theorems.Thm_ModularCurve_toricPoint_fst_coeff_mul
import Theorems.Thm_ModularCurve_toricPoint_snd_coeff_zero
import Theorems.Thm_ModularCurve_toricPoint_snd_coeff_of_not_dvd
import Theorems.Thm_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors
import Theorems.Thm_ModularCurve_tsum_of_coeff_lt_eq_zero
import Theorems.Thm_ModularCurve_slotSubst_gen_injective
import Theorems.Thm_ModularCurve_single_div_one_sub_sq
import Theorems.Thm_ModularCurve_single_sq_div_one_sub_cube
import Theorems.Thm_ModularCurve_tsum_lambertTerm_eq
import Definitions.Def_TateCurve_QSeries
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_TateCurve_Tails
import Theorems.Thm_TateCurve_equation_pointX_pointY
import Theorems.Thm_TateCurve_pointX_qExpansion
import Theorems.Thm_TateCurve_pointY_qExpansion
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Definitions.Def_ModularCurve_TateSlots
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_tateUniv_equation
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries
p2m_open "ModularCurve P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"
open WithZero Filter Finset Topology

namespace ModularCurve
p2m_export "ModularCurve" "equation_tateBase_iff tateUnivX tateUnivY tateUnivA4 tateUnivA6 tateUnivCurve slotFamily slotSubst nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd toricPoint toricPoint_fst toricPoint_snd tateB twelve_mul_tateB tateA4 tateA6 tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY toricPoint_fst_coeff_zero toricPoint_fst_coeff_of_not_dvd toricPoint_fst_coeff_mul toricPoint_snd_coeff_zero toricPoint_snd_coeff_of_not_dvd toricPoint_snd_coeff_mul_eq_sum_divisors tsum_of_coeff_lt_eq_zero slotSubst_gen_injective single_div_one_sub_sq single_sq_div_one_sub_cube tsum_lambertTerm_eq"
p2m_open "ModularCurve"

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

section Seam

variable (K : Type*) [Field K]

theorem isRankOneDiscrete_valued :
    (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
  (Valuation.IsRankOneDiscrete.mk' _ : ((PowerSeries.idealX K).valuation (LaurentSeries K)).IsRankOneDiscrete)

abbrev rankOneLaurent : (Valued.v : Valuation (LaurentSeries K) (WithZero (Multiplicative ℤ))).RankOne :=
  haveI := isRankOneDiscrete_valued K
  Valuation.IsRankOneDiscrete.rankOne _ (e := (2 : NNReal)) (by norm_num)

end Seam

section Kit

variable (K : Type*) [Field K]

abbrev w4bNormed : NontriviallyNormedField (LaurentSeries K) :=
  @Valued.toNontriviallyNormedField (LaurentSeries K) _ (WithZero (Multiplicative ℤ)) _ _ (rankOneLaurent K)

def tateQ (p : ℕ) : LaurentSeries K := HahnSeries.single (p : ℤ) (1 : K)

variable {K}

theorem valued_single_zero_of_ne_zero {c : K} (hc : c ≠ 0) :
    Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) = 1 := by
  have hle : ∀ {d : K}, Valued.v (HahnSeries.single (0 : ℤ) d : LaurentSeries K) ≤ 1 := by
    intro d
    have h := (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K (D := 0)
      (f := (HahnSeries.single (0 : ℤ) d : LaurentSeries K))).mpr
      (fun n hn => HahnSeries.coeff_single_of_ne hn.ne)
    simpa using h
  have hmul : (HahnSeries.single (0 : ℤ) c : LaurentSeries K) * HahnSeries.single (0 : ℤ) c⁻¹ = 1 := by
    rw [HahnSeries.single_mul_single, add_zero, mul_inv_cancel₀ hc]
    rfl
  have h1 : Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) *
      Valued.v (HahnSeries.single (0 : ℤ) c⁻¹ : LaurentSeries K) = 1 := by
    rw [← map_mul, hmul, map_one]
  refine le_antisymm hle ?_
  by_contra hlt
  push Not at hlt
  have : Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) *
      Valued.v (HahnSeries.single (0 : ℤ) c⁻¹ : LaurentSeries K) < 1 :=
    calc _ ≤ Valued.v (HahnSeries.single (0 : ℤ) c : LaurentSeries K) * 1 := mul_le_mul_right hle _
      _ = _ := mul_one _
      _ < 1 := hlt
  exact absurd h1 this.ne

theorem valued_single_of_ne_zero (n : ℤ) {c : K} (hc : c ≠ 0) :
    Valued.v (HahnSeries.single n c : LaurentSeries K) = WithZero.exp (-n) := by
  have h : (HahnSeries.single n c : LaurentSeries K) =
      HahnSeries.single n (1 : K) * HahnSeries.single (0 : ℤ) c := by
    rw [HahnSeries.single_mul_single, add_zero, one_mul]
  rw [h, map_mul, LaurentSeries.valuation_single_zpow, valued_single_zero_of_ne_zero hc, mul_one]

theorem tateQ_ne_zero (p : ℕ) : tateQ K p ≠ 0 := HahnSeries.single_ne_zero one_ne_zero

theorem valued_tateQ (p : ℕ) : Valued.v (tateQ K p) = WithZero.exp (-(p : ℤ)) :=
  LaurentSeries.valuation_single_zpow K (p : ℤ)

theorem valued_tateQ_zpow_mul_single (p : ℕ) (n j : ℤ) {c : K} (hc : c ≠ 0) :
    Valued.v (tateQ K p ^ n * HahnSeries.single j c) = WithZero.exp (-((p : ℤ) * n + j)) := by
  rw [map_mul, map_zpow₀, valued_tateQ, valued_single_of_ne_zero j hc, ← WithZero.exp_zsmul, ← WithZero.exp_add]
  congr 1
  simp only [smul_eq_mul]
  ring

theorem tateQ_zpow_mul_single_ne_one_of_pos {p j : ℕ} (hj : 0 < j) (hjp : j < p) {c : K} (hc : c ≠ 0)
    (n : ℤ) : tateQ K p ^ n * HahnSeries.single (j : ℤ) c ≠ 1 := by
  intro h
  have hv := valued_tateQ_zpow_mul_single p n (j : ℤ) hc
  rw [h, map_one, eq_comm, WithZero.exp_eq_one, neg_eq_zero] at hv
  rcases le_or_gt 0 n with hn | hn
  · have : (0 : ℤ) ≤ (p : ℤ) * n := mul_nonneg (by positivity) hn
    omega
  · have : (p : ℤ) * n ≤ -(p : ℤ) := by nlinarith
    omega

theorem tateQ_zpow_mul_single_zero_ne_one {p : ℕ} [NeZero p] {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) (n : ℤ) :
    tateQ K p ^ n * HahnSeries.single (0 : ℤ) c ≠ 1 := by
  intro h
  have hv := valued_tateQ_zpow_mul_single p n 0 hc0
  rw [h, map_one, eq_comm, WithZero.exp_eq_one, neg_eq_zero, add_zero, mul_eq_zero] at hv
  rcases hv with hp | hn
  · exact (NeZero.ne p) (by exact_mod_cast hp)
  · subst hn
    rw [zpow_zero, one_mul] at h
    apply hc1
    have := congrArg (fun f : LaurentSeries K => f.coeff (0 : ℤ)) h
    simpa using this

end Kit

section Platform

attribute [local instance] rankOneLaurent w4bNormed

variable {K : Type*} [Field K]

example : IsUltrametricDist (LaurentSeries K) := inferInstance
example : CompleteSpace (LaurentSeries K) := inferInstance
example : (w4bNormed K).toField = (inferInstance : Field (LaurentSeries K)) := rfl

theorem charZero_laurentSeries [CharZero K] : CharZero (LaurentSeries K) :=
  charZero_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective

theorem nnnorm_lt_one_iff_valued (x : LaurentSeries K) : ‖x‖₊ < 1 ↔ Valued.v x < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]
  exact Valued.toNormedField.norm_lt_one_iff

theorem exp_neg_lt_one {m : ℤ} (hm : 0 < m) : WithZero.exp (-m) < (1 : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
  omega

theorem nnnorm_tateQ_lt_one (p : ℕ) [NeZero p] : ‖tateQ K p‖₊ < 1 := by
  rw [nnnorm_lt_one_iff_valued, valued_tateQ]
  exact exp_neg_lt_one (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p))

theorem nnnorm_tateQ_mul_single_lt_one (p : ℕ) [NeZero p] (j : ℕ) {c : K} (hc : c ≠ 0) :
    ‖tateQ K p * HahnSeries.single (j : ℤ) c‖₊ < 1 := by
  rw [nnnorm_lt_one_iff_valued]
  have := valued_tateQ_zpow_mul_single (K := K) p 1 (j : ℤ) hc
  rw [zpow_one] at this
  rw [this]
  exact exp_neg_lt_one (by have := Nat.pos_of_ne_zero (NeZero.ne p); omega)

theorem nnnorm_tateQ_mul_single_inv_lt_one (p : ℕ) [NeZero p] {j : ℕ} (hjp : j < p) {c : K} (hc : c ≠ 0) :
    ‖tateQ K p * (HahnSeries.single (j : ℤ) c)⁻¹‖₊ < 1 := by
  rw [nnnorm_lt_one_iff_valued, HahnSeries.inv_single]
  have := valued_tateQ_zpow_mul_single (K := K) p 1 (-(j : ℤ)) (inv_ne_zero hc)
  rw [zpow_one] at this
  rw [this]
  exact exp_neg_lt_one (by omega)

end Platform

section OfPowerSeriesInt

variable (K : Type*) [Field K]

theorem ofPowerSeries_coeff_neg (f : PowerSeries K) (m : ℤ) (hm : m < 0) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff m = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨n, hn⟩
  have : (n : ℤ) = m := hn
  omega

private theorem _root_.ModularCurve.ofPowerSeries_coeff_int (f : PowerSeries K) (m : ℤ) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff m
      = if 0 ≤ m then PowerSeries.coeff m.toNat f else 0 := by
  split_ifs with h
  · conv_lhs => rw [show m = ((m.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm]
    exact HahnSeries.ofPowerSeries_apply_coeff f m.toNat
  · exact ofPowerSeries_coeff_neg K f m (not_le.mp h)

p2m_export "ModularCurve" "ofPowerSeries_coeff_int"
end OfPowerSeriesInt

section GeomHeads

variable (K : Type*) [CommRing K]

def headX (j : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.mk fun n => if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0

def headY (j : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.mk fun n => if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0

theorem coeff_headX (j : ℕ) (c : K) (n : ℕ) :
    PowerSeries.coeff n (headX K j c) = if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0 :=
  PowerSeries.coeff_mk _ _

theorem coeff_headY (j : ℕ) (c : K) (n : ℕ) :
    PowerSeries.coeff n (headY K j c) = if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0 :=
  PowerSeries.coeff_mk _ _

end GeomHeads

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

namespace W4B
namespace B2

section Inline
variable (K : Type*) [Field K]

abbrev Qp (p : ℕ) : LaurentSeries K := HahnSeries.single (p : ℤ) (1 : K)

theorem ofPowerSeries_coeff_neg (f : PowerSeries K) (m : ℤ) (hm : m < 0) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff m = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨n, hn⟩
  have : (n : ℤ) = m := hn
  omega

theorem ofPowerSeries_coeff_int (f : PowerSeries K) (m : ℤ) :
    (HahnSeries.ofPowerSeries ℤ K f).coeff m
      = if 0 ≤ m then PowerSeries.coeff m.toNat f else 0 := by
  split_ifs with h
  · conv_lhs => rw [show m = ((m.toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm]
    exact HahnSeries.ofPowerSeries_apply_coeff f m.toNat
  · exact ofPowerSeries_coeff_neg K f m (not_le.mp h)

def lambertTerm (p : ℕ) (c : ℕ → ℕ) (n : ℕ) : LaurentSeries K :=
  (c n : LaurentSeries K) * ((Qp K p) ^ n / (1 - (Qp K p) ^ n))

end Inline
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

end W4B.B2
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

namespace W4B
private theorem _root_.W4B.tsum_of_coeff_lt_eq_zero {K : Type*} [Field K] {δ : ℕ} (hδ : 0 < δ) (f : ℕ → LaurentSeries K) (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0) (g : LaurentSeries K) (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) : ∑' N, f N = g :=
  ModularCurve.tsum_of_coeff_lt_eq_zero hδ f hf g hg

end W4B
p2m_export "" "W4B.tsum_of_coeff_lt_eq_zero"
namespace W4Bdev
private theorem _root_.W4Bdev.coeff_slotSubst_tateUnivX {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivX) = (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) * ((if n = p * M + j * e then (c : K) ^ e else 0) + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0) - (if n = p * M then 2 else 0)) :=
  ModularCurve.coeff_slotSubst_tateUnivX p c j hj hjp n

end W4Bdev
p2m_export "" "W4Bdev.coeff_slotSubst_tateUnivX"
namespace W4Bdev
private theorem _root_.W4Bdev.coeff_slotSubst_tateUnivY {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) : PowerSeries.coeff n (slotSubst K p c j tateUnivY) = (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0) + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0) - (if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0) + (if n = p * M then (e : K) else 0)) :=
  ModularCurve.coeff_slotSubst_tateUnivY p c j hj hjp n

end W4Bdev
p2m_export "" "W4Bdev.coeff_slotSubst_tateUnivY"
namespace W4Bdev
private theorem _root_.W4Bdev.slotSubst_gen_injective : Function.Injective (slotSubst (LaurentSeries ℚ) 2
      (Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)) 1) :=
  ModularCurve.slotSubst_gen_injective

end W4Bdev
p2m_export "" "W4Bdev.slotSubst_gen_injective"
namespace W4B.B2
private theorem _root_.W4B.B2.tsum_lambertTerm_eq (K : Type*) [Field K] (p : ℕ) [NeZero p] (c : ℕ → ℕ) :
    ∑' n, W4B.B2.lambertTerm K p c n = qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ))) :=
  ModularCurve.tsum_lambertTerm_eq K p c

end W4B.B2
p2m_export "" "W4B.B2.tsum_lambertTerm_eq"

theorem W4B.B2.natCast_b_eq_tateB (n : ℕ) : ((TateCurve.b n : ℕ) : ℤ) = ModularCurve.tateB n := by
  have h12 : (12 : ℤ) ≠ 0 := by norm_num
  have hL : ((TateCurve.b n : ℕ) : ℤ) * 12 = 5 * (n : ℤ) ^ 3 + 7 * (n : ℤ) ^ 5 := by
    exact_mod_cast TateCurve.b_mul_twelve n
  have hR : ModularCurve.tateB n * 12 = 5 * (n : ℤ) ^ 3 + 7 * (n : ℤ) ^ 5 := by
    linarith [ModularCurve.twelve_mul_tateB n]
  exact mul_right_cancel₀ h12 (hL.trans hR.symm)

namespace ModularCurve
p2m_export "ModularCurve" "equation_tateBase_iff tateUnivX tateUnivY tateUnivA4 tateUnivA6 tateUnivCurve slotFamily slotSubst nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd toricPoint toricPoint_fst toricPoint_snd tateB twelve_mul_tateB tateA4 tateA6 tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY toricPoint_fst_coeff_zero toricPoint_fst_coeff_of_not_dvd toricPoint_fst_coeff_mul toricPoint_snd_coeff_zero toricPoint_snd_coeff_of_not_dvd toricPoint_snd_coeff_mul_eq_sum_divisors tsum_of_coeff_lt_eq_zero slotSubst_gen_injective single_div_one_sub_sq single_sq_div_one_sub_cube tsum_lambertTerm_eq"
p2m_open "ModularCurve"

section TieToric

attribute [local instance] rankOneLaurent w4bNormed

variable (K : Type*) [Field K]

theorem single_zero_eq_C (c : K) : HahnSeries.single (0 : ℤ) c = HahnSeries.C c := rfl

theorem xfun_single_zero (c : K) :
    TateCurve.xfun (HahnSeries.single (0 : ℤ) c) = HahnSeries.single (0 : ℤ) (c / (1 - c) ^ 2) := by
  have h1 : (1 : LaurentSeries K) - HahnSeries.C c = HahnSeries.C (1 - c) := by
    rw [map_sub, map_one]
  rw [single_zero_eq_C, single_zero_eq_C, TateCurve.xfun, h1, ← map_pow, ← map_div₀]

theorem yfun_single_zero (c : K) :
    TateCurve.yfun (HahnSeries.single (0 : ℤ) c)
      = HahnSeries.single (0 : ℤ) (c ^ 2 / (1 - c) ^ 3) := by
  have h1 : (1 : LaurentSeries K) - HahnSeries.C c = HahnSeries.C (1 - c) := by
    rw [map_sub, map_one]
  rw [single_zero_eq_C, single_zero_eq_C, TateCurve.yfun, h1, ← map_pow, ← map_pow, ← map_div₀]

theorem xDivTerm_single_zero (c : K) (e : ℕ) :
    TateCurve.xDivTerm (HahnSeries.single (0 : ℤ) c) e
      = HahnSeries.single (0 : ℤ) ((e : K) * (c ^ e + c⁻¹ ^ e - 2)) := by
  simp only [single_zero_eq_C, TateCurve.xDivTerm, map_mul, map_add, map_sub, map_pow,
    map_inv₀, map_natCast, map_ofNat]

theorem yDivTerm_single_zero (c : K) (e : ℕ) :
    TateCurve.yDivTerm (HahnSeries.single (0 : ℤ) c) e
      = HahnSeries.single (0 : ℤ)
          (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) := by
  simp only [single_zero_eq_C, TateCurve.yDivTerm, map_mul, map_add, map_sub, map_pow,
    map_inv₀, map_natCast]

theorem xCoeff_single_zero (c : K) (M : ℕ) :
    TateCurve.xCoeff (HahnSeries.single (0 : ℤ) c) M
      = HahnSeries.single (0 : ℤ) (∑ e ∈ M.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2)) := by
  rw [TateCurve.xCoeff]
  simp only [single_zero_eq_C]
  rw [map_sum (HahnSeries.C : K →+* HahnSeries ℤ K) _ M.divisors]
  exact Finset.sum_congr rfl fun e _ => xDivTerm_single_zero K c e

theorem yCoeff_single_zero (c : K) (M : ℕ) :
    TateCurve.yCoeff (HahnSeries.single (0 : ℤ) c) M
      = HahnSeries.single (0 : ℤ) (∑ e ∈ M.divisors,
          (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K))) := by
  rw [TateCurve.yCoeff]
  simp only [single_zero_eq_C]
  rw [map_sum (HahnSeries.C : K →+* HahnSeries ℤ K) _ M.divisors]
  exact Finset.sum_congr rfl fun e _ => yDivTerm_single_zero K c e

theorem single_zero_mul_tateQ_pow_coeff (x : K) (p M' : ℕ) (m : ℤ) :
    (HahnSeries.single (0 : ℤ) x * (tateQ K p) ^ M').coeff m
      = if m = ((p * M' : ℕ) : ℤ) then x else 0 := by
  rw [tateQ, HahnSeries.single_pow, one_pow, HahnSeries.single_mul_single, zero_add, mul_one,
    show M' • ((p : ℕ) : ℤ) = ((p * M' : ℕ) : ℤ) from by push_cast [nsmul_eq_mul]; ring,
    HahnSeries.coeff_single]
  split_ifs <;> rfl

theorem toric_tail_hf (p : ℕ) [NeZero p] (x : ℕ → K) :
    ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (p : ℤ) →
      (HahnSeries.single (0 : ℤ) (x (N + 1)) * (tateQ K p) ^ (N + 1)).coeff m = 0 := by
  intro N m hm
  rw [single_zero_mul_tateQ_pow_coeff, if_neg]
  intro hcon
  have h1 : N * p ≤ p * (N + 1) := by
    rw [Nat.mul_succ, Nat.mul_comm N p]
    exact Nat.le_add_right _ _
  have h2 : ((N * p : ℕ) : ℤ) ≤ ((p * (N + 1) : ℕ) : ℤ) := Int.ofNat_le.mpr h1
  push_cast at h2
  omega

theorem toric_tail_hg (p : ℕ) [NeZero p] (x : ℕ → K) (x0 : K) (A : LaurentSeries K)
    (hA0 : A.coeff 0 = x0)
    (hAneg : ∀ m : ℕ, A.coeff (Int.negSucc m) = 0)
    (hAmul : ∀ {M : ℕ}, M ≠ 0 → A.coeff ((p * M : ℕ) : ℤ) = x M)
    (hAnd : ∀ {m : ℕ}, ¬ p ∣ m → A.coeff (m : ℤ) = 0) :
    ∀ m : ℤ, (A - HahnSeries.single (0 : ℤ) x0).coeff m
      = ∑ N ∈ Finset.range (m.toNat / p + 1),
          (HahnSeries.single (0 : ℤ) (x (N + 1)) * (tateQ K p) ^ (N + 1)).coeff m := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  intro m
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_single,
    Finset.sum_congr rfl fun N _ => single_zero_mul_tateQ_pow_coeff K (x (N + 1)) p (N + 1) m]
  rcases m with m | m
  · simp only [Int.ofNat_eq_natCast]
    by_cases hm0 : m = 0
    · subst hm0
      simp only [Nat.cast_zero, if_true]
      rw [hA0, sub_self]
      rw [show (0 : ℤ).toNat = 0 from rfl, Nat.zero_div, Finset.sum_range_one,
        if_neg (fun h : (0 : ℤ) = ((p * (0 + 1) : ℕ) : ℤ) => NeZero.ne p (by omega))]
    · by_cases hpm : p ∣ m
      · obtain ⟨M, rfl⟩ := hpm
        have hM0 : M ≠ 0 := fun h => hm0 (by rw [h, Nat.mul_zero])
        have hpM : p * M ≠ 0 := Nat.mul_ne_zero hp.ne' hM0
        rw [hAmul hM0, if_neg (fun h => hpM (by exact_mod_cast h)), sub_zero,
          Int.toNat_natCast, Nat.mul_div_cancel_left M hp]
        have hM1 : M - 1 + 1 = M := by omega
        rw [Finset.sum_eq_single (M - 1)]
        · rw [hM1, if_pos rfl]
        · intro N hN hne
          rw [if_neg]
          intro hcon
          have hMe : p * M = p * (N + 1) := by exact_mod_cast hcon
          have := Nat.eq_of_mul_eq_mul_left hp hMe
          omega
        · intro hM1m
          exact absurd (Finset.mem_range.mpr (by omega)) hM1m
      · rw [hAnd hpm, if_neg (fun h : (m : ℤ) = 0 => hm0 (by exact_mod_cast h)), sub_zero]
        symm
        apply Finset.sum_eq_zero
        intro N _
        rw [if_neg]
        intro hcon
        exact hpm ⟨N + 1, by exact_mod_cast hcon⟩
  · rw [hAneg m, if_neg (by omega : ¬ Int.negSucc m = 0), sub_zero]
    symm
    apply Finset.sum_eq_zero
    intro N _
    rw [if_neg]
    omega

theorem tie_toricPoint_fst (p : ℕ) [NeZero p] (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    TateCurve.pointX (tateQ K p) (HahnSeries.single (0 : ℤ) c) = (toricPoint K p c).1 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hts : (∑' N : ℕ, TateCurve.xCoeff (HahnSeries.single (0 : ℤ) c) (N + 1)
        * (tateQ K p) ^ (N + 1))
      = (toricPoint K p c).1 - TateCurve.xfun (HahnSeries.single (0 : ℤ) c) := by
    refine W4B.tsum_of_coeff_lt_eq_zero hp _ (fun N m hm => ?_) _ (fun m => ?_)
    · rw [xCoeff_single_zero]
      exact toric_tail_hf K p (fun M => ∑ e ∈ M.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2)) N m hm
    · rw [(Finset.sum_congr rfl fun N _ => by rw [xCoeff_single_zero] :
          ∑ N ∈ Finset.range (m.toNat / p + 1),
            (TateCurve.xCoeff (HahnSeries.single (0 : ℤ) c) (N + 1) * (tateQ K p) ^ (N + 1)).coeff m
          = ∑ N ∈ Finset.range (m.toNat / p + 1),
            (HahnSeries.single (0 : ℤ) (∑ e ∈ (N + 1).divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2))
              * (tateQ K p) ^ (N + 1)).coeff m),
        xfun_single_zero]
      exact toric_tail_hg K p _ _ _ (toricPoint_fst_coeff_zero K p c)
        (fun m => by rw [toricPoint_fst, ofPowerSeries_coeff_int,
          if_neg (show ¬ (0 : ℤ) ≤ Int.negSucc m by omega)])
        (fun {M} hM0 => toricPoint_fst_coeff_mul K p hp c hM0)
        (fun {m} hpm => toricPoint_fst_coeff_of_not_dvd K p c hpm) m
  have hqX := TateCurve.pointX_qExpansion (tateQ_ne_zero p) (nnnorm_tateQ_lt_one p)
    (HahnSeries.single_ne_zero hc0) (tateQ_zpow_mul_single_zero_ne_one hc0 hc1)
    (nnnorm_tateQ_mul_single_lt_one p 0 hc0) (nnnorm_tateQ_mul_single_inv_lt_one p hp hc0)
  rw [hqX, hts, add_comm, sub_add_cancel]

theorem tie_toricPoint_snd (p : ℕ) [NeZero p] (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    TateCurve.pointY (tateQ K p) (HahnSeries.single (0 : ℤ) c) = (toricPoint K p c).2 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hts : (∑' N : ℕ, TateCurve.yCoeff (HahnSeries.single (0 : ℤ) c) (N + 1)
        * (tateQ K p) ^ (N + 1))
      = (toricPoint K p c).2 - TateCurve.yfun (HahnSeries.single (0 : ℤ) c) := by
    refine W4B.tsum_of_coeff_lt_eq_zero hp _ (fun N m hm => ?_) _ (fun m => ?_)
    · rw [yCoeff_single_zero]
      exact toric_tail_hf K p (fun M => ∑ e ∈ M.divisors,
        (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K))) N m hm
    · rw [(Finset.sum_congr rfl fun N _ => by rw [yCoeff_single_zero] :
          ∑ N ∈ Finset.range (m.toNat / p + 1),
            (TateCurve.yCoeff (HahnSeries.single (0 : ℤ) c) (N + 1) * (tateQ K p) ^ (N + 1)).coeff m
          = ∑ N ∈ Finset.range (m.toNat / p + 1),
            (HahnSeries.single (0 : ℤ) (∑ e ∈ (N + 1).divisors,
                (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)))
              * (tateQ K p) ^ (N + 1)).coeff m),
        yfun_single_zero]
      exact toric_tail_hg K p _ _ _ (toricPoint_snd_coeff_zero K p c)
        (fun m => by rw [toricPoint_snd, ofPowerSeries_coeff_int,
          if_neg (show ¬ (0 : ℤ) ≤ Int.negSucc m by omega)])
        (fun {M} hM0 => toricPoint_snd_coeff_mul_eq_sum_divisors K p hp c hM0)
        (fun {m} hpm => toricPoint_snd_coeff_of_not_dvd K p c hpm) m
  have hqY := TateCurve.pointY_qExpansion (tateQ_ne_zero p) (nnnorm_tateQ_lt_one p)
    (HahnSeries.single_ne_zero hc0) (tateQ_zpow_mul_single_zero_ne_one hc0 hc1)
    (nnnorm_tateQ_mul_single_lt_one p 0 hc0) (nnnorm_tateQ_mul_single_inv_lt_one p hp hc0)
  rw [hqY, hts, add_comm, sub_add_cancel]

end TieToric
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

section TieNonToric

attribute [local instance] rankOneLaurent w4bNormed

variable (K : Type*) [Field K]

theorem xfun_single_eq (j : ℕ) (hj : 0 < j) (c : K) :
    TateCurve.xfun (HahnSeries.single (j : ℤ) c)
      = HahnSeries.ofPowerSeries ℤ K (headX K j c) := by
  rw [TateCurve.xfun]; exact single_div_one_sub_sq K j hj c

theorem yfun_single_eq (j : ℕ) (hj : 0 < j) (c : K) :
    TateCurve.yfun (HahnSeries.single (j : ℤ) c)
      = HahnSeries.ofPowerSeries ℤ K (headY K j c) := by
  rw [TateCurve.yfun]; exact single_sq_div_one_sub_cube K j hj c

theorem single_pow' (j : ℕ) (c : K) (e : ℕ) :
    (HahnSeries.single (j : ℤ) c) ^ e = HahnSeries.single ((j * e : ℕ) : ℤ) (c ^ e) := by
  rw [HahnSeries.single_pow]; congr 1; push_cast [nsmul_eq_mul]; ring

theorem single_inv_pow' (j : ℕ) (c : Kˣ) (e : ℕ) :
    (HahnSeries.single (j : ℤ) (c : K))⁻¹ ^ e
      = HahnSeries.single (-((j * e : ℕ) : ℤ)) (((c⁻¹ : Kˣ) : K) ^ e) := by
  rw [HahnSeries.inv_single, HahnSeries.single_pow]
  congr 1
  · push_cast [nsmul_eq_mul]; ring
  · rw [Units.val_inv_eq_inv_val, inv_pow]

theorem tateQ_pow_eq_single (p M : ℕ) :
    (tateQ K p) ^ M = HahnSeries.single ((p * M : ℕ) : ℤ) (1 : K) := by
  rw [tateQ, HahnSeries.single_pow, one_pow]; congr 1; push_cast [nsmul_eq_mul]; ring

theorem two_eq_single_zero_two : (2 : LaurentSeries K) = HahnSeries.single (0 : ℤ) (2 : K) := by
  rw [show (2 : LaurentSeries K) = ((2 : ℕ) : LaurentSeries K) from by norm_num,
    ← HahnSeries.single_zero_natCast]
  norm_num

theorem coeff_xCoeff_single_mul_tateQ_pow (p : ℕ) (c : Kˣ) (j : ℕ) (M' : ℕ) (m : ℤ) :
    (TateCurve.xCoeff (HahnSeries.single (j : ℤ) (c : K)) M' * (tateQ K p) ^ M').coeff m
      = ∑ e ∈ M'.divisors, (e : K) *
          ((if m = ((p * M' + j * e : ℕ) : ℤ) then (c : K) ^ e else 0)
            + (if m + ((j * e : ℕ) : ℤ) = ((p * M' : ℕ) : ℤ) then ((c⁻¹ : Kˣ) : K) ^ e else 0)
            - (if m = ((p * M' : ℕ) : ℤ) then 2 else 0)) := by
  rw [TateCurve.xCoeff, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [TateCurve.xDivTerm, single_pow' K j (c : K) e, single_inv_pow' K j c e, tateQ_pow_eq_single,
    two_eq_single_zero_two, ← HahnSeries.single_zero_natCast, mul_assoc,
    HahnSeries.coeff_single_zero_mul, sub_mul, add_mul,
    HahnSeries.single_mul_single, HahnSeries.single_mul_single, HahnSeries.single_mul_single,
    HahnSeries.coeff_sub, HahnSeries.coeff_add,
    HahnSeries.coeff_single, HahnSeries.coeff_single, HahnSeries.coeff_single]
  simp only [mul_one, zero_add, Nat.cast_add, Nat.cast_mul]
  split_ifs with h1 h2 h3 h4 h5 h6 <;>
    (try rfl) <;> exfalso <;> omega

theorem coeff_yCoeff_single_mul_tateQ_pow (p : ℕ) (c : Kˣ) (j : ℕ) (M' : ℕ) (m : ℤ) :
    (TateCurve.yCoeff (HahnSeries.single (j : ℤ) (c : K)) M' * (tateQ K p) ^ M').coeff m
      = ∑ e ∈ M'.divisors,
          ((if m = ((p * M' + j * e : ℕ) : ℤ) then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
            - (if m + ((j * e : ℕ) : ℤ) = ((p * M' : ℕ) : ℤ)
                then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0)
            + (if m = ((p * M' : ℕ) : ℤ) then (e : K) else 0)) := by
  rw [TateCurve.yCoeff, Finset.sum_mul, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  have pascal : (((e + 1).choose 2 : ℕ) : K) = ((e.choose 2 : ℕ) : K) + (e : K) := by
    have h : (e + 1).choose 2 = e + e.choose 2 := by
      simpa [Nat.choose_one_right] using Nat.choose_succ_succ' e 1
    rw [h]; push_cast; ring
  rw [TateCurve.yDivTerm, single_pow' K j (c : K) e, single_inv_pow' K j c e, tateQ_pow_eq_single,
    ← HahnSeries.single_zero_natCast, ← HahnSeries.single_zero_natCast]
  simp only [mul_sub, add_mul, sub_mul, HahnSeries.single_mul_single,
    HahnSeries.coeff_add, HahnSeries.coeff_sub, HahnSeries.coeff_single,
    mul_one, zero_add, Nat.cast_add, Nat.cast_mul, pascal]
  split_ifs <;> (try ring) <;> exfalso <;> omega

theorem nonToric_x_tail_hf (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * ((1 : ℕ) : ℤ) →
      (TateCurve.xCoeff (HahnSeries.single (j : ℤ) (c : K)) (N + 1)
        * (tateQ K p) ^ (N + 1)).coeff m = 0 := by
  intro N m hm
  simp only [Nat.cast_one, mul_one] at hm
  rw [coeff_xCoeff_single_mul_tateQ_pow]
  refine Finset.sum_eq_zero fun e he => ?_
  have heN : e ≤ N + 1 := Nat.le_of_dvd (Nat.succ_pos N) (Nat.mem_divisors.mp he).1
  have hpN : ((p * (N + 1) : ℕ) : ℤ) = (p : ℤ) * ((N : ℤ) + 1) := by push_cast; ring
  have hjpe : ((j * e : ℕ) : ℤ) = (j : ℤ) * (e : ℤ) := by push_cast; ring
  have hpNje : ((p * (N + 1) + j * e : ℕ) : ℤ) = (p : ℤ) * ((N : ℤ) + 1) + (j : ℤ) * (e : ℤ) := by
    push_cast; ring
  have hb1 : (N : ℤ) < (p : ℤ) * ((N : ℤ) + 1) := by
    nlinarith [(Nat.cast_lt (α := ℤ)).mpr (hj.trans hjp)]
  have hb2 : (N : ℤ) < (p : ℤ) * ((N : ℤ) + 1) - (j : ℤ) * (e : ℤ) := by
    have h1 : (j : ℤ) * (e : ℤ) ≤ (j : ℤ) * ((N : ℤ) + 1) := by
      have h := (Nat.cast_le (α := ℤ)).mpr heN
      nlinarith [(Nat.cast_nonneg (α := ℤ) j)]
    have h2 : (p : ℤ) * ((N : ℤ) + 1) - (j : ℤ) * ((N : ℤ) + 1) ≥ (N : ℤ) + 1 := by
      have hpj : (p : ℤ) - (j : ℤ) ≥ 1 := by
        have := (Nat.cast_lt (α := ℤ)).mpr hjp; omega
      nlinarith [(Nat.cast_nonneg (α := ℤ) N)]
    linarith
  rw [if_neg, if_neg, if_neg]
  · ring
  · rw [hpN]; exact fun h => absurd h (by linarith)
  · rw [hjpe, hpN]; exact fun h => absurd h (by linarith)
  · rw [hpNje]; exact fun h => absurd h (by linarith)

theorem nonToric_y_tail_hf (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * ((1 : ℕ) : ℤ) →
      (TateCurve.yCoeff (HahnSeries.single (j : ℤ) (c : K)) (N + 1)
        * (tateQ K p) ^ (N + 1)).coeff m = 0 := by
  intro N m hm
  simp only [Nat.cast_one, mul_one] at hm
  rw [coeff_yCoeff_single_mul_tateQ_pow]
  refine Finset.sum_eq_zero fun e he => ?_
  have heN : e ≤ N + 1 := Nat.le_of_dvd (Nat.succ_pos N) (Nat.mem_divisors.mp he).1
  have hpN : ((p * (N + 1) : ℕ) : ℤ) = (p : ℤ) * ((N : ℤ) + 1) := by push_cast; ring
  have hjpe : ((j * e : ℕ) : ℤ) = (j : ℤ) * (e : ℤ) := by push_cast; ring
  have hpNje : ((p * (N + 1) + j * e : ℕ) : ℤ) = (p : ℤ) * ((N : ℤ) + 1) + (j : ℤ) * (e : ℤ) := by
    push_cast; ring
  have hb1 : (N : ℤ) < (p : ℤ) * ((N : ℤ) + 1) := by
    nlinarith [(Nat.cast_lt (α := ℤ)).mpr (hj.trans hjp)]
  have hb2 : (N : ℤ) < (p : ℤ) * ((N : ℤ) + 1) - (j : ℤ) * (e : ℤ) := by
    have h1 : (j : ℤ) * (e : ℤ) ≤ (j : ℤ) * ((N : ℤ) + 1) := by
      have h := (Nat.cast_le (α := ℤ)).mpr heN
      nlinarith [(Nat.cast_nonneg (α := ℤ) j)]
    have h2 : (p : ℤ) * ((N : ℤ) + 1) - (j : ℤ) * ((N : ℤ) + 1) ≥ (N : ℤ) + 1 := by
      have hpj : (p : ℤ) - (j : ℤ) ≥ 1 := by
        have := (Nat.cast_lt (α := ℤ)).mpr hjp; omega
      nlinarith [(Nat.cast_nonneg (α := ℤ) N)]
    linarith
  rw [if_neg, if_neg, if_neg]
  · ring
  · rw [hpN]; exact fun h => absurd h (by linarith)
  · rw [hjpe, hpN]; exact fun h => absurd h (by linarith)
  · rw [hpNje]; exact fun h => absurd h (by linarith)

theorem sum_range_shift_of_ends (F : ℕ → K) (n : ℕ) (h0 : F 0 = 0) (htop : F (n + 1) = 0) :
    ∑ M ∈ Finset.range (n + 1), F M = ∑ N ∈ Finset.range (n + 1), F (N + 1) := by
  have h2 : ∑ M ∈ Finset.range (n + 2), F M = ∑ M ∈ Finset.range (n + 1), F M := by
    rw [Finset.sum_range_succ, htop, add_zero]
  rw [← h2, Finset.sum_range_succ', h0, add_zero]

theorem nonToric_x_tail_hg (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ∀ m : ℤ,
      ((nonToricPoint K p c j).1 - TateCurve.xfun (HahnSeries.single (j : ℤ) (c : K))).coeff m
        = ∑ N ∈ Finset.range (m.toNat / 1 + 1),
            (TateCurve.xCoeff (HahnSeries.single (j : ℤ) (c : K)) (N + 1)
              * (tateQ K p) ^ (N + 1)).coeff m := by
  intro m
  rcases m with n | n
  · simp only [Int.ofNat_eq_natCast]
    rw [HahnSeries.coeff_sub, nonToricPoint_fst, xfun_single_eq K j hj (c : K),
      W4B.B2.ofPowerSeries_coeff_int, W4B.B2.ofPowerSeries_coeff_int, if_pos (Int.natCast_nonneg n),
      if_pos (Int.natCast_nonneg n), Int.toNat_natCast,
      W4Bdev.coeff_slotSubst_tateUnivX p c j hj hjp n, coeff_headX, add_sub_cancel_left,
      Nat.div_one,
      Finset.sum_congr rfl fun N _ =>
        coeff_xCoeff_single_mul_tateQ_pow K p c j (N + 1) ((n : ℕ) : ℤ)]
    have hp1 : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
    have htop : ∑ e ∈ (n + 1).divisors, (e : K) *
        ((if n = p * (n + 1) + j * e then (c : K) ^ e else 0)
          + (if n + j * e = p * (n + 1) then ((c⁻¹ : Kˣ) : K) ^ e else 0)
          - (if n = p * (n + 1) then 2 else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro e hd
      have he' : e ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) (Nat.mem_divisors.mp hd).1
      have h3 : j * e ≤ j * (n + 1) := Nat.mul_le_mul_left j he'
      have h4 : (j + 1) * (n + 1) ≤ p * (n + 1) :=
        Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hjp)
      have h5 : (j + 1) * (n + 1) = j * (n + 1) + (n + 1) := by ring
      have h6 : 1 * (n + 1) ≤ p * (n + 1) := Nat.mul_le_mul_right (n + 1) hp1
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
    have h0 : ∑ e ∈ (0 : ℕ).divisors, (e : K) *
        ((if n = p * 0 + j * e then (c : K) ^ e else 0)
          + (if n + j * e = p * 0 then ((c⁻¹ : Kˣ) : K) ^ e else 0)
          - (if n = p * 0 then 2 else 0)) = 0 := by
      simp [Nat.divisors_zero]
    refine Eq.trans (sum_range_shift_of_ends K
      (fun M => ∑ e ∈ M.divisors, (e : K) *
        ((if n = p * M + j * e then (c : K) ^ e else 0)
          + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0)
          - (if n = p * M then 2 else 0))) n h0 htop) ?_
    refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun e he => ?_
    simp only [← Nat.cast_add, Nat.cast_inj]
  · rw [HahnSeries.coeff_sub, nonToricPoint_fst, xfun_single_eq K j hj (c : K),
      W4B.B2.ofPowerSeries_coeff_int, W4B.B2.ofPowerSeries_coeff_int,
      if_neg (by omega : ¬ (0 : ℤ) ≤ Int.negSucc n),
      if_neg (by omega : ¬ (0 : ℤ) ≤ Int.negSucc n), sub_zero,
      show (Int.negSucc n).toNat = 0 from rfl, Nat.zero_div, Finset.sum_range_one,
      coeff_xCoeff_single_mul_tateQ_pow K p c j 1 (Int.negSucc n)]
    symm
    apply Finset.sum_eq_zero
    intro e he
    have he1 : e = 1 := by simpa [Nat.divisors_one] using he
    subst he1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

theorem nonToric_y_tail_hg (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    ∀ m : ℤ,
      ((nonToricPoint K p c j).2 - TateCurve.yfun (HahnSeries.single (j : ℤ) (c : K))).coeff m
        = ∑ N ∈ Finset.range (m.toNat / 1 + 1),
            (TateCurve.yCoeff (HahnSeries.single (j : ℤ) (c : K)) (N + 1)
              * (tateQ K p) ^ (N + 1)).coeff m := by
  intro m
  rcases m with n | n
  · simp only [Int.ofNat_eq_natCast]
    rw [HahnSeries.coeff_sub, nonToricPoint_snd, yfun_single_eq K j hj (c : K),
      W4B.B2.ofPowerSeries_coeff_int, W4B.B2.ofPowerSeries_coeff_int, if_pos (Int.natCast_nonneg n),
      if_pos (Int.natCast_nonneg n), Int.toNat_natCast,
      W4Bdev.coeff_slotSubst_tateUnivY p c j hj hjp n, coeff_headY, add_sub_cancel_left,
      Nat.div_one,
      Finset.sum_congr rfl fun N _ =>
        coeff_yCoeff_single_mul_tateQ_pow K p c j (N + 1) ((n : ℕ) : ℤ)]
    have hp1 : 1 ≤ p := Nat.pos_of_ne_zero (NeZero.ne p)
    have htop : ∑ e ∈ (n + 1).divisors,
        ((if n = p * (n + 1) + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
          - (if n + j * e = p * (n + 1)
              then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0)
          + (if n = p * (n + 1) then (e : K) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro e hd
      have he' : e ≤ n + 1 := Nat.le_of_dvd (Nat.succ_pos n) (Nat.mem_divisors.mp hd).1
      have h3 : j * e ≤ j * (n + 1) := Nat.mul_le_mul_left j he'
      have h4 : (j + 1) * (n + 1) ≤ p * (n + 1) :=
        Nat.mul_le_mul_right (n + 1) (Nat.succ_le_of_lt hjp)
      have h5 : (j + 1) * (n + 1) = j * (n + 1) + (n + 1) := by ring
      have h6 : 1 * (n + 1) ≤ p * (n + 1) := Nat.mul_le_mul_right (n + 1) hp1
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
    have h0 : ∑ e ∈ (0 : ℕ).divisors,
        ((if n = p * 0 + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
          - (if n + j * e = p * 0
              then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0)
          + (if n = p * 0 then (e : K) else 0)) = 0 := by
      simp [Nat.divisors_zero]
    refine Eq.trans (sum_range_shift_of_ends K
      (fun M => ∑ e ∈ M.divisors,
        ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
          - (if n + j * e = p * M
              then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e else 0)
          + (if n = p * M then (e : K) else 0))) n h0 htop) ?_
    refine Finset.sum_congr rfl fun N _ => Finset.sum_congr rfl fun e he => ?_
    simp only [← Nat.cast_add, Nat.cast_inj]
  · rw [HahnSeries.coeff_sub, nonToricPoint_snd, yfun_single_eq K j hj (c : K),
      W4B.B2.ofPowerSeries_coeff_int, W4B.B2.ofPowerSeries_coeff_int,
      if_neg (by omega : ¬ (0 : ℤ) ≤ Int.negSucc n),
      if_neg (by omega : ¬ (0 : ℤ) ≤ Int.negSucc n), sub_zero,
      show (Int.negSucc n).toNat = 0 from rfl, Nat.zero_div, Finset.sum_range_one,
      coeff_yCoeff_single_mul_tateQ_pow K p c j 1 (Int.negSucc n)]
    symm
    apply Finset.sum_eq_zero
    intro e he
    have he1 : e = 1 := by simpa [Nat.divisors_one] using he
    subst he1
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    ring

theorem tie_nonToricPoint_fst (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointX (tateQ K p) (HahnSeries.single (j : ℤ) (c : K)) = (nonToricPoint K p c j).1 := by
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hts :=
    W4B.tsum_of_coeff_lt_eq_zero Nat.one_pos _ (nonToric_x_tail_hf K p c j hj hjp) _
      (nonToric_x_tail_hg K p c j hj hjp)
  have hqX := TateCurve.pointX_qExpansion (tateQ_ne_zero p) (nnnorm_tateQ_lt_one p)
    (HahnSeries.single_ne_zero hc0) (tateQ_zpow_mul_single_ne_one_of_pos hj hjp hc0)
    (nnnorm_tateQ_mul_single_lt_one p j hc0) (nnnorm_tateQ_mul_single_inv_lt_one p hjp hc0)
  rw [hqX, hts, add_comm, sub_add_cancel]

theorem tie_nonToricPoint_snd (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointY (tateQ K p) (HahnSeries.single (j : ℤ) (c : K)) = (nonToricPoint K p c j).2 := by
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  have hts :=
    W4B.tsum_of_coeff_lt_eq_zero Nat.one_pos _ (nonToric_y_tail_hf K p c j hj hjp) _
      (nonToric_y_tail_hg K p c j hj hjp)
  have hqY := TateCurve.pointY_qExpansion (tateQ_ne_zero p) (nnnorm_tateQ_lt_one p)
    (HahnSeries.single_ne_zero hc0) (tateQ_zpow_mul_single_ne_one_of_pos hj hjp hc0)
    (nnnorm_tateQ_mul_single_lt_one p j hc0) (nnnorm_tateQ_mul_single_inv_lt_one p hjp hc0)
  rw [hqY, hts, add_comm, sub_add_cancel]

end TieNonToric
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

section Dock

attribute [local instance] rankOneLaurent w4bNormed

variable (K : Type*) [Field K]

theorem coeffSum_tateQ_eq_tsum_lambertTerm (p : ℕ) (c : ℕ → ℕ) :
    TateCurve.coeffSum c (tateQ K p) = ∑' n, W4B.B2.lambertTerm K p c n := rfl

theorem tie_a₄ (p : ℕ) [NeZero p] :
    TateCurve.a₄ (tateQ K p) = qExpand K p (laurentOfInt K tateA4) := by
  show -(TateCurve.coeffSum (fun n => 5 * n ^ 3) (tateQ K p)) = _
  rw [coeffSum_tateQ_eq_tsum_lambertTerm, W4B.B2.tsum_lambertTerm_eq, tateA4, ← map_neg, ← map_neg]
  congr 2

theorem tie_a₆ (p : ℕ) [NeZero p] :
    TateCurve.a₆ (tateQ K p) = qExpand K p (laurentOfInt K tateA6) := by
  show -(TateCurve.coeffSum TateCurve.b (tateQ K p)) = _
  rw [coeffSum_tateQ_eq_tsum_lambertTerm, W4B.B2.tsum_lambertTerm_eq, tateA6, ← map_neg, ← map_neg]
  simp only [W4B.B2.natCast_b_eq_tateB]
  congr 2

variable [CharZero K]

private theorem toricPoint_equation (p : ℕ) [NeZero p] (c : K) (hc0 : c ≠ 0) (hc1 : c ≠ 1) :
    (tateBase K p).toAffine.Equation (toricPoint K p c).1 (toricPoint K p c).2 := by
  haveI : CharZero (LaurentSeries K) := charZero_laurentSeries
  rw [equation_tateBase_iff, ← tie_a₄ K p, ← tie_a₆ K p, ← tie_toricPoint_fst K p c hc0 hc1,
    ← tie_toricPoint_snd K p c hc0 hc1]
  exact TateCurve.equation_pointX_pointY (tateQ_ne_zero p) (nnnorm_tateQ_lt_one p)
    (HahnSeries.single_ne_zero hc0) (tateQ_zpow_mul_single_zero_ne_one hc0 hc1)

private theorem nonToricPoint_equation (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    (tateBase K p).toAffine.Equation (nonToricPoint K p c j).1 (nonToricPoint K p c j).2 := by
  haveI : CharZero (LaurentSeries K) := charZero_laurentSeries
  rw [equation_tateBase_iff, ← tie_a₄ K p, ← tie_a₆ K p, ← tie_nonToricPoint_fst K p c j hj hjp,
    ← tie_nonToricPoint_snd K p c j hj hjp]
  exact TateCurve.equation_pointX_pointY (tateQ_ne_zero p) (nnnorm_tateQ_lt_one p)
    (HahnSeries.single_ne_zero c.ne_zero) (tateQ_zpow_mul_single_ne_one_of_pos hj hjp c.ne_zero)

end Dock
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

section UnivGlue

theorem tateBase_eq_map_slotHom (K : Type*) [CommRing K] (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ)
    (hj : 0 < j) (hjp : j < p) :
    tateBase K p = tateUnivCurve.map (slotHom K p c j hj hjp) :=
  (tateUnivCurve_map_slotHom K p c j hj hjp).symm

def genericUnit : (LaurentSeries ℚ)ˣ :=
  Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)

theorem slotHom_generic_injective :
    Function.Injective (slotHom (LaurentSeries ℚ) 2 genericUnit 1 one_pos one_lt_two) := by
  intro f g h
  rw [slotHom_apply, slotHom_apply] at h
  exact W4Bdev.slotSubst_gen_injective (HahnSeries.ofPowerSeries_injective h)

private theorem tateUniv_equation : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY := by
  haveI : CharZero (LaurentSeries ℚ) := charZero_laurentSeries
  have h := nonToricPoint_equation (LaurentSeries ℚ) 2 genericUnit 1 one_pos one_lt_two
  rw [tateBase_eq_map_slotHom (LaurentSeries ℚ) 2 genericUnit 1 one_pos one_lt_two,
    nonToricPoint_fst, nonToricPoint_snd,
    ← slotHom_apply (LaurentSeries ℚ) 2 genericUnit 1 one_pos one_lt_two,
    ← slotHom_apply (LaurentSeries ℚ) 2 genericUnit 1 one_pos one_lt_two] at h
  exact (WeierstrassCurve.Affine.map_equation _ slotHom_generic_injective _ _).mp h

end UnivGlue
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_tateUniv_equation.ModularCurve"

#check @ModularCurve.toricPoint_equation
#check @ModularCurve.nonToricPoint_equation
#check @ModularCurve.tateUniv_equation
#check @ModularCurve.tie_a₄
#check @ModularCurve.tie_a₆
#check @ModularCurve.tie_toricPoint_fst
#check @ModularCurve.tie_toricPoint_snd
#check @ModularCurve.tie_nonToricPoint_fst
#check @ModularCurve.tie_nonToricPoint_snd
#check @ModularCurve.tateBase_eq_map_slotHom
#check @ModularCurve.slotHom_generic_injective

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_tateUniv_equation.ModularCurve in

theorem solution : tateUnivCurve.toAffine.Equation tateUnivX tateUnivY :=
  ModularCurve.tateUniv_equation

#print axioms solution

end S_ModularCurve_tateUniv_equation
end P2MW
export P2MW.S_ModularCurve_tateUniv_equation (solution)
