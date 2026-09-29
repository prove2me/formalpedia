-- Prove2me | solution 1 for ModularCurve.toricPoint_snd_coeff_mul_eq_sum_divisors
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/890fbacc-7f4a-589d-b2cf-2bb6366b6b96

import Definitions.Def_ModularCurve_TateSlots
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX tateUnivY tateUnivA4 tateUnivA6 tateUnivCurve slotFamily slotSubst tateBase toricPoint toricPoint_fst toricPoint_snd tateA4 tateA6 tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg"
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

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

open WithZero Filter Finset Topology

namespace W4B

variable {K : Type*} [Field K]

theorem hasSum_of_coeff_lt_eq_zero {δ : ℕ} (hδ : 0 < δ)
    (f : ℕ → LaurentSeries K)
    (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0)
    (g : LaurentSeries K)
    (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) :
    HasSum f g := by
  have key : ∀ (k : ℕ) (s : Finset ℕ), Finset.range (k + 1) ⊆ s →
      Valued.v ((∑ N ∈ s, f N) - g) ≤ exp (-(k : ℤ)) := by
    intro k s hs
    refine (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).mpr fun m hm => ?_
    rw [HahnSeries.coeff_sub, HahnSeries.coeff_sum, hg m, sub_eq_zero]
    have hmk : m.toNat ≤ k := by omega
    refine (Finset.sum_subset (fun N hN => hs ?_) (fun N _ hN => hf N m ?_)).symm
    · rw [Finset.mem_range] at hN ⊢
      exact hN.trans_le (Nat.add_le_add_right ((Nat.div_le_self _ _).trans hmk) 1)
    · rw [Finset.mem_range, not_lt] at hN
      have h3 : m.toNat < N * δ := (Nat.div_lt_iff_lt_mul hδ).mp (Nat.lt_of_succ_le hN)
      calc (m : ℤ) ≤ (m.toNat : ℤ) := Int.self_le_toNat m
        _ < ((N * δ : ℕ) : ℤ) := by exact_mod_cast h3
        _ = (N : ℤ) * (δ : ℤ) := by push_cast; ring
  show Tendsto (fun s : Finset ℕ => ∑ N ∈ s, f N) atTop (𝓝 g)
  rw [← tendsto_sub_nhds_zero_iff,
    (Valued.hasBasis_nhds_zero (LaurentSeries K) ℤᵐ⁰).tendsto_right_iff]
  intro γ _
  have hγ0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ 0 := by
    simp
  obtain ⟨k, hk⟩ := WithZero.exists_exp_neg_natCast_lt hγ0
  refine Filter.eventually_atTop.mpr ⟨Finset.range (k + 1), fun s hs => ?_⟩
  simp only [Set.mem_setOf_eq, Valuation.restrict_lt_iff_lt_embedding]
  exact (key k s hs).trans_lt hk

theorem summable_of_coeff_lt_eq_zero {δ : ℕ} (hδ : 0 < δ)
    (f : ℕ → LaurentSeries K)
    (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0)
    (g : LaurentSeries K)
    (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) :
    Summable f :=
  ⟨g, hasSum_of_coeff_lt_eq_zero hδ f hf g hg⟩

#synth T2Space (LaurentSeries ℚ)

private theorem tsum_of_coeff_lt_eq_zero {δ : ℕ} (hδ : 0 < δ)
    (f : ℕ → LaurentSeries K)
    (hf : ∀ N : ℕ, ∀ m : ℤ, m < (N : ℤ) * (δ : ℤ) → (f N).coeff m = 0)
    (g : LaurentSeries K)
    (hg : ∀ m : ℤ, g.coeff m = ∑ N ∈ Finset.range (m.toNat / δ + 1), (f N).coeff m) :
    ∑' N, f N = g :=
  (hasSum_of_coeff_lt_eq_zero hδ f hf g hg).tsum_eq

end W4B
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

namespace W4B
namespace B2

section GeomPS
variable (K : Type*) [CommRing K]

def geomPS (d : ℕ) : PowerSeries K := PowerSeries.mk fun m => if d ∣ m then 1 else 0

theorem coeff_geomPS (d m : ℕ) : PowerSeries.coeff m (geomPS K d) = if d ∣ m then 1 else 0 :=
  PowerSeries.coeff_mk m _

private theorem dvd_sub_iff_of_le {d m : ℕ} (h : d ≤ m) : d ∣ (m - d) ↔ d ∣ m := by
  constructor
  · intro hd; have := hd.add (dvd_refl d); rwa [Nat.sub_add_cancel h] at this
  · intro hd; exact Nat.dvd_sub hd (dvd_refl d)

theorem one_sub_X_pow_mul_geomPS (d : ℕ) (hd : 0 < d) :
    (1 - (PowerSeries.X : PowerSeries K) ^ d) * geomPS K d = 1 := by
  ext m
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_geomPS, coeff_geomPS,
    PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hd.not_ge]
  · rw [if_neg hm.ne']
    rcases le_or_gt d m with hdm | hdm
    · simp only [if_pos hdm, dvd_sub_iff_of_le hdm]
      split_ifs <;> ring
    · rw [if_neg hdm.not_ge, if_neg (fun h => hdm.not_ge (Nat.le_of_dvd hm h))]
      ring

theorem coeff_X_pow_mul_geomPS (d : ℕ) (m : ℕ) :
    PowerSeries.coeff m ((PowerSeries.X : PowerSeries K) ^ d * geomPS K d)
      = if d ∣ m ∧ d ≤ m then 1 else 0 := by
  rw [coeff_X_pow_mul', coeff_geomPS]
  rcases le_or_gt d m with hdm | hdm
  · rw [if_pos hdm]
    simp only [dvd_sub_iff_of_le hdm, hdm, and_true]
  · rw [if_neg hdm.not_ge, if_neg (fun h => hdm.not_ge h.2)]

end GeomPS
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

section GeomLS
variable (K : Type*) [Field K]

abbrev Qp (p : ℕ) : LaurentSeries K := HahnSeries.single (p : ℤ) (1 : K)

theorem Qp_pow_eq_ofPowerSeries (p n : ℕ) :
    (Qp K p) ^ n = HahnSeries.ofPowerSeries ℤ K ((PowerSeries.X) ^ (p * n)) := by
  rw [HahnSeries.ofPowerSeries_X_pow, Qp]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, HahnSeries.single_mul_single, one_mul]
    push_cast; ring_nf

theorem one_sub_Qp_pow_ne_zero (p n : ℕ) (hpn : 0 < p * n) :
    (1 : LaurentSeries K) - (Qp K p) ^ n ≠ 0 := by
  intro h
  have hc : ((1 : LaurentSeries K) - (Qp K p) ^ n).coeff 0 = 0 := by rw [h]; rfl
  rw [Qp_pow_eq_ofPowerSeries, HahnSeries.ofPowerSeries_X_pow, HahnSeries.coeff_sub,
    HahnSeries.coeff_one, if_pos rfl, HahnSeries.coeff_single,
    if_neg (by exact_mod_cast hpn.ne), sub_zero] at hc
  exact one_ne_zero hc

theorem Qp_pow_div_one_sub_eq (p n : ℕ) (hpn : 0 < p * n) :
    (Qp K p) ^ n / (1 - (Qp K p) ^ n)
      = HahnSeries.ofPowerSeries ℤ K ((PowerSeries.X) ^ (p * n) * geomPS K (p * n)) := by
  rw [div_eq_iff (one_sub_Qp_pow_ne_zero K p n hpn), Qp_pow_eq_ofPowerSeries,
    show (1 : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K 1 from (map_one _).symm,
    ← map_sub, ← map_mul]
  congr 1
  rw [mul_assoc, mul_comm (geomPS K (p * n)), one_sub_X_pow_mul_geomPS K (p * n) hpn, mul_one]

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

theorem coeff_Qp_pow_div_one_sub (p n : ℕ) [NeZero p] (hn : 0 < n) (m : ℤ) :
    ((Qp K p) ^ n / (1 - (Qp K p) ^ n)).coeff m
      = if ((p * n : ℤ) ∣ m ∧ (p * n : ℤ) ≤ m) then 1 else 0 := by
  have hpn : 0 < p * n := Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne p)) hn
  rw [Qp_pow_div_one_sub_eq K p n hpn, ofPowerSeries_coeff_int, coeff_X_pow_mul_geomPS]
  rcases lt_or_ge m 0 with hm | hm
  · rw [if_neg (not_le.mpr hm), if_neg]
    rintro ⟨-, h⟩
    exact absurd (h.trans hm.le) (by exact_mod_cast hpn.not_ge)
  · rw [if_pos hm]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨⟨k, hk⟩, h2⟩
      refine ⟨⟨(k : ℤ), ?_⟩, by omega⟩
      have : m = ((p * n * k : ℕ) : ℤ) := by rw [← hk, Int.toNat_of_nonneg hm]
      push_cast at this; linarith
    · rintro ⟨⟨k, hk⟩, h2⟩
      have hk0 : 0 ≤ k := by
        rcases lt_or_ge k 0 with hk0 | hk0
        · exfalso
          have : m < 0 := hk ▸ mul_neg_of_pos_of_neg (by exact_mod_cast hpn) hk0
          omega
        · exact hk0
      refine ⟨⟨k.toNat, ?_⟩, by omega⟩
      have : m = ((p * n * k.toNat : ℕ) : ℤ) := by
        push_cast; rw [Int.toNat_of_nonneg hk0]; linarith
      omega

end GeomLS
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

section Lambert
variable (K : Type*) [Field K]

def lambertTerm (p : ℕ) (c : ℕ → ℕ) (n : ℕ) : LaurentSeries K :=
  (c n : LaurentSeries K) * ((Qp K p) ^ n / (1 - (Qp K p) ^ n))

theorem lambertTerm_zero (p : ℕ) (c : ℕ → ℕ) : lambertTerm K p c 0 = 0 := by
  simp [lambertTerm]

theorem coeff_lambertTerm (p : ℕ) [NeZero p] (c : ℕ → ℕ) (n : ℕ) (hn : 0 < n) (m : ℤ) :
    (lambertTerm K p c n).coeff m
      = if ((p * n : ℤ) ∣ m ∧ (p * n : ℤ) ≤ m) then (c n : K) else 0 := by
  rw [lambertTerm, ← HahnSeries.single_zero_natCast, HahnSeries.coeff_single_zero_mul,
    coeff_Qp_pow_div_one_sub K p n hn m]
  split_ifs <;> simp

theorem coeff_lambertTerm_eq_zero_of_lt (p : ℕ) [NeZero p] (c : ℕ → ℕ) (n : ℕ) (m : ℤ)
    (hm : m < (n : ℤ) * (p : ℤ)) : (lambertTerm K p c n).coeff m = 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [lambertTerm_zero]; rfl
  · rw [coeff_lambertTerm K p c n hn m, if_neg]
    rintro ⟨-, h2⟩
    have hc : (n : ℤ) * (p : ℤ) = ((p * n : ℕ) : ℤ) := by push_cast; ring
    omega

theorem coeff_qExpand_laurentOfInt (p : ℕ) [NeZero p] (φ : PowerSeries ℤ) (m : ℤ) :
    (qExpand K p (laurentOfInt K φ)).coeff m
      = if ((p : ℤ) ∣ m ∧ 0 ≤ m) then ((PowerSeries.coeff (m.toNat / p) φ : ℤ) : K) else 0 := by
  by_cases hdvd : (p : ℤ) ∣ m
  · obtain ⟨k, hk⟩ := hdvd
    have hp : 0 < (p : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne p)
    rw [hk, qExpand_coeff_mul, laurentOfInt_apply, ofPowerSeries_coeff_int, PowerSeries.coeff_map]
    congr 1
    · refine propext ⟨fun hk0 => ⟨⟨k, rfl⟩, by positivity⟩, fun ⟨_, hm0⟩ => ?_⟩
      exact (mul_nonneg_iff_of_pos_left hp).mp hm0
    · have hk' : ((p : ℤ) * k).toNat = p * k.toNat := by
        rcases le_or_gt 0 k with h | h
        · have heq : (p : ℤ) * k = ((p * k.toNat : ℕ) : ℤ) := by
            push_cast; rw [Int.toNat_of_nonneg h]
          omega
        · have hneg : (p : ℤ) * k < 0 := mul_neg_of_pos_of_neg hp h
          simp [Int.toNat_of_nonpos hneg.le, Int.toNat_of_nonpos h.le]
      rw [hk', Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne p))]
      rfl
  · rw [qExpand_coeff_of_not_dvd _ _ hdvd, if_neg (fun h => hdvd h.1)]

theorem range_dvd_sum_eq_divisors_sum (k : ℕ) (c : ℕ → ℕ) :
    (∑ N ∈ Finset.range (k + 1), if (N ∣ k ∧ 1 ≤ N) then (c N : K) else 0)
      = ∑ d ∈ k.divisors, (c d : K) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext N
  simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hd, h1⟩; exact ⟨hd, fun hk0 => by omega⟩
  · rintro ⟨hd, hk0⟩
    have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (fun h => hk0 (zero_dvd_iff.mp (h ▸ hd)))
    exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hd), hd, hN1⟩

private theorem tsum_lambertTerm_eq (p : ℕ) [NeZero p] (c : ℕ → ℕ) :
    ∑' n, lambertTerm K p c n
      = qExpand K p (laurentOfInt K (PowerSeries.mk fun m => ∑ d ∈ m.divisors, (c d : ℤ))) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  refine W4B.tsum_of_coeff_lt_eq_zero hp _ (coeff_lambertTerm_eq_zero_of_lt K p c) _ ?_
  intro m
  rw [coeff_qExpand_laurentOfInt, PowerSeries.coeff_mk]
  rcases lt_or_ge m 0 with hm | hm
  · rw [if_neg (fun h => absurd h.2 (not_le.mpr hm))]
    simp only [Int.toNat_of_nonpos hm.le, Nat.zero_div, zero_add, Finset.range_one,
      Finset.sum_singleton, lambertTerm_zero, HahnSeries.coeff_zero]
  · push_cast
    have step : ∀ N ∈ Finset.range (m.toNat / p + 1),
        (lambertTerm K p c N).coeff m
          = if (N ∣ m.toNat / p ∧ 1 ≤ N ∧ (p : ℤ) ∣ m) then (c N : K) else 0 := by
      intro N hN
      rcases Nat.eq_zero_or_pos N with rfl | hN1
      · simp [lambertTerm_zero]
      · rw [coeff_lambertTerm K p c N hN1]
        refine if_congr ?_ rfl rfl
        constructor
        · rintro ⟨⟨k, hk⟩, h2⟩
          have hk0 : 0 ≤ k := by
            by_contra h; push Not at h
            have hneg : m < 0 := hk ▸ mul_neg_of_pos_of_neg
              (mul_pos (by exact_mod_cast hp) (by exact_mod_cast hN1)) h
            omega
          have hmN : m.toNat = p * N * k.toNat := by
            have heq : m = ((p * N * k.toNat : ℕ) : ℤ) := by
              push_cast; rw [Int.toNat_of_nonneg hk0]; linarith
            omega
          refine ⟨⟨k.toNat, ?_⟩, hN1, ⟨(N : ℤ) * k, by rw [hk]; ring⟩⟩
          rw [hmN, Nat.mul_assoc, Nat.mul_div_cancel_left _ hp]
        · rintro ⟨⟨k, hk⟩, -, ⟨k', hk'⟩⟩
          have hk'0 : 0 ≤ k' := by
            by_contra h; push Not at h
            have : m < 0 := hk' ▸ mul_neg_of_pos_of_neg (by exact_mod_cast hp) h
            omega
          have hpd : p ∣ m.toNat := ⟨k'.toNat, by
            have heq : m = ((p * k'.toNat : ℕ) : ℤ) := by
              push_cast; rw [Int.toNat_of_nonneg hk'0]; linarith
            omega⟩
          have hkm : m.toNat = p * (N * k) := by
            rw [← Nat.div_mul_cancel hpd, hk, Nat.mul_comm]
          refine ⟨⟨(k : ℤ), ?_⟩, ?_⟩
          · have heq : m = ((p * N * k : ℕ) : ℤ) := by
              rw [← Int.toNat_of_nonneg hm, hkm]; push_cast; ring
            push_cast at heq ⊢; linarith
          · have hk1 : 1 ≤ k := by
              rcases Nat.eq_zero_or_pos k with rfl | h
              · exfalso
                simp only [mul_zero] at hkm
                rw [Finset.mem_range] at hN
                omega
              · exact h
            have hle : (p * N : ℤ) ≤ ((p * (N * k) : ℕ) : ℤ) := by
              push_cast; nlinarith
            rw [← hkm, Int.toNat_of_nonneg hm] at hle
            linarith
    rw [Finset.sum_congr rfl step]
    by_cases hdvd : (p : ℤ) ∣ m
    · rw [if_pos ⟨hdvd, hm⟩]
      simp only [hdvd, and_true]
      exact (range_dvd_sum_eq_divisors_sum K (m.toNat / p) c).symm
    · rw [if_neg (fun h => hdvd h.1)]
      exact (Finset.sum_eq_zero fun N _ => if_neg (fun h => hdvd h.2.2)).symm

end Lambert
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

end W4B.B2
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "tateUnivX tateUnivY tateUnivA4 tateUnivA6 tateUnivCurve slotFamily slotSubst tateBase toricPoint toricPoint_fst toricPoint_snd tateA4 tateA6 tatePowerSeries_a₁ tatePowerSeries_a₂ tatePowerSeries_a₃ laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd ofPowerSeries_coeff_of_neg"
p2m_open "ModularCurve"

section OfPowerSeriesInt

variable (K : Type*) [Field K]

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

end OfPowerSeriesInt
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

section ToricFaces

variable (K : Type*) [Field K] (p : ℕ)

private theorem toricPoint_fst_coeff_zero (c : K) : (toricPoint K p c).1.coeff 0 = c / (1 - c) ^ 2 := by
  rw [toricPoint_fst, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_mk]
  simp

private theorem toricPoint_snd_coeff_zero (c : K) : (toricPoint K p c).2.coeff 0 = c ^ 2 / (1 - c) ^ 3 := by
  rw [toricPoint_snd, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_mk]
  simp

end ToricFaces
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

section ToricCoeffs

variable (K : Type*) [Field K] (p : ℕ)

theorem toricPoint_fst_coeff_natCast (c : K) {m : ℕ} (hm : m ≠ 0) :
    (toricPoint K p c).1.coeff (m : ℤ) =
      (∑ d ∈ m.divisors, if p ∣ d then ((m / d : ℕ) : K) * (c ^ (m / d) + c⁻¹ ^ (m / d)) else 0)
        - 2 * (if p ∣ m then ((∑ e ∈ (m / p).divisors, (e : ℕ)) : K) else 0) := by
  simp only [toricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_neg hm]

theorem toricPoint_snd_coeff_natCast (c : K) {m : ℕ} (hm : m ≠ 0) :
    (toricPoint K p c).2.coeff (m : ℤ) =
      (∑ d ∈ m.divisors, if p ∣ d then
          ((m / d).choose 2 : K) * c ^ (m / d) - ((m / d + 1).choose 2 : K) * c⁻¹ ^ (m / d) else 0)
        + (if p ∣ m then ((∑ e ∈ (m / p).divisors, (e : ℕ)) : K) else 0) := by
  simp only [toricPoint_snd, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, if_neg hm]

private theorem toricPoint_fst_coeff_of_not_dvd (c : K) {m : ℕ} (hpm : ¬ p ∣ m) :
    (toricPoint K p c).1.coeff (m : ℤ) = 0 := by
  have hm : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  rw [toricPoint_fst_coeff_natCast K p c hm, if_neg hpm, mul_zero, sub_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [if_neg]
  exact fun hpd => hpm (hpd.trans (Nat.mem_divisors.mp hd).1)

private theorem toricPoint_snd_coeff_of_not_dvd (c : K) {m : ℕ} (hpm : ¬ p ∣ m) :
    (toricPoint K p c).2.coeff (m : ℤ) = 0 := by
  have hm : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  rw [toricPoint_snd_coeff_natCast K p c hm, if_neg hpm, add_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [if_neg]
  exact fun hpd => hpm (hpd.trans (Nat.mem_divisors.mp hd).1)

theorem sum_divisors_mul_ite_dvd {β : Type*} [AddCommMonoid β] (hp : 0 < p) (M : ℕ) (F : ℕ → β) :
    (∑ d ∈ (p * M).divisors, if p ∣ d then F d else 0) = ∑ d' ∈ M.divisors, F (p * d') := by
  rw [← Finset.sum_filter]
  have hset : (p * M).divisors.filter (fun d => p ∣ d) = M.divisors.image (fun d' => p * d') := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd, hpM⟩, d', rfl⟩
      exact ⟨d', ⟨(Nat.mul_dvd_mul_iff_left hp).mp hd, fun h => hpM (by rw [h, mul_zero])⟩, rfl⟩
    · rintro ⟨d', ⟨hd', hM⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left p hd', mul_ne_zero hp.ne' hM⟩, d', rfl⟩
  rw [hset, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hp h

private theorem toricPoint_fst_coeff_mul (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) :
    (toricPoint K p c).1.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2) := by
  have hpM : p * M ≠ 0 := mul_ne_zero hp.ne' hM
  rw [toricPoint_fst_coeff_natCast K p c hpM, sum_divisors_mul_ite_dvd p hp M, if_pos (dvd_mul_right p M),
    Nat.mul_div_cancel_left M hp]
  simp_rw [Nat.mul_div_mul_left _ _ hp]
  rw [Nat.sum_div_divisors M (fun e => ((e : ℕ) : K) * (c ^ e + c⁻¹ ^ e)), Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

theorem toricPoint_snd_coeff_mul (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) :
    (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) =
      ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * c ^ e - (((e + 1).choose 2 : ℕ) : K) * c⁻¹ ^ e + (e : K)) := by
  have hpM : p * M ≠ 0 := mul_ne_zero hp.ne' hM
  rw [toricPoint_snd_coeff_natCast K p c hpM, sum_divisors_mul_ite_dvd p hp M, if_pos (dvd_mul_right p M),
    Nat.mul_div_cancel_left M hp]
  simp_rw [Nat.mul_div_mul_left _ _ hp]
  rw [Nat.sum_div_divisors M (fun e => (((e : ℕ).choose 2 : ℕ) : K) * c ^ e - (((e + 1).choose 2 : ℕ) : K) * c⁻¹ ^ e),
    ← Finset.sum_add_distrib]

private theorem toricPoint_snd_coeff_mul' (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) :
    (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) =
      ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) := by
  rw [toricPoint_snd_coeff_mul K p hp c hM]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Nat.choose_succ_succ' e 1, Nat.choose_one_right, Nat.cast_add]
  ring

example : (toricPoint ℚ 3 (-1)).1.coeff 0 = -1 / 4 := by
  rw [toricPoint_fst_coeff_zero]; norm_num

example : (toricPoint ℚ 3 (-1)).2.coeff 0 = 1 / 8 := by
  rw [toricPoint_snd_coeff_zero]; norm_num

example : (toricPoint ℚ 3 (-1)).1.coeff 3 = -4 := by
  rw [show (3 : ℤ) = ((3 * 1 : ℕ) : ℤ) by norm_num, toricPoint_fst_coeff_mul ℚ 3 (by norm_num) (-1) one_ne_zero,
    Nat.divisors_one, Finset.sum_singleton]
  norm_num

example : (toricPoint ℚ 3 (-1)).1.coeff 6 = -4 := by
  rw [show (6 : ℤ) = ((3 * 2 : ℕ) : ℤ) by norm_num, toricPoint_fst_coeff_mul ℚ 3 (by norm_num) (-1) two_ne_zero,
    Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by decide)]
  norm_num

example : (toricPoint ℚ 3 (-1)).2.coeff 3 = 2 := by
  rw [show (3 : ℤ) = ((3 * 1 : ℕ) : ℤ) by norm_num, toricPoint_snd_coeff_mul ℚ 3 (by norm_num) (-1) one_ne_zero,
    Nat.divisors_one, Finset.sum_singleton]
  norm_num

example : (toricPoint ℚ 3 (-1)).2.coeff 6 = 2 := by
  rw [show (6 : ℤ) = ((3 * 2 : ℕ) : ℤ) by norm_num, toricPoint_snd_coeff_mul ℚ 3 (by norm_num) (-1) two_ne_zero,
    Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by decide)]
  norm_num [Nat.choose]

example : (toricPoint ℚ 3 (-1)).1.coeff 4 = 0 :=
  toricPoint_fst_coeff_of_not_dvd ℚ 3 (-1) (m := 4) (by decide)

end ToricCoeffs
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

namespace W4Bdev

section Abstract

variable {K : Type*} [CommRing K] (c : Kˣ)

theorem hasSubst_slotFamily_two : MvPowerSeries.HasSubst (slotFamily K 2 c 1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
    fin_cases s <;> simp [slotFamily, PowerSeries.C, PowerSeries.X])

theorem prod_slotFamily_two (d : Fin 2 →₀ ℕ) :
    (d.prod fun s e => (slotFamily K 2 c 1 s) ^ e)
      = PowerSeries.C ((c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1) * PowerSeries.X ^ (d 0 + d 1) := by
  rw [Finsupp.prod_pow, Fin.prod_univ_two]
  simp only [slotFamily, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_pow, mul_pow, ← map_pow, ← map_pow,
    mul_mul_mul_comm, ← map_mul, ← _root_.pow_add]

variable (φ : MvPowerSeries (Fin 2) ℤ)

theorem coeff_slotSubst_two (n : ℕ) :
    PowerSeries.coeff n (slotSubst K 2 c 1 φ)
      = ∑ᶠ d' : Fin 2 →₀ ℕ, MvPowerSeries.coeff d' φ •
          (if n = d' 0 + d' 1 then (c : K) ^ d' 0 * ((c⁻¹ : Kˣ) : K) ^ d' 1 else 0) := by
  simp only [slotSubst]
  rw [PowerSeries.coeff_def Finsupp.single_eq_same,
    MvPowerSeries.coeff_subst (hasSubst_slotFamily_two c)]
  congr 1
  funext d'
  rw [prod_slotFamily_two, ← PowerSeries.coeff_def Finsupp.single_eq_same,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]

theorem support_coeff_slotSubst_two (n : ℕ) :
    (Function.support fun d' : Fin 2 →₀ ℕ => MvPowerSeries.coeff d' φ •
      (if n = d' 0 + d' 1 then (c : K) ^ d' 0 * ((c⁻¹ : Kˣ) : K) ^ d' 1 else 0)).Finite := by
  have hfun : (fun d' : Fin 2 →₀ ℕ => MvPowerSeries.coeff d' φ •
        (if n = d' 0 + d' 1 then (c : K) ^ d' 0 * ((c⁻¹ : Kˣ) : K) ^ d' 1 else 0))
      = fun d' : Fin 2 →₀ ℕ => MvPowerSeries.coeff d' φ •
          MvPowerSeries.coeff (Finsupp.single () n)
            (d'.prod fun s e => (slotFamily K 2 c 1 s) ^ e) := by
    funext d'
    rw [prod_slotFamily_two, ← PowerSeries.coeff_def Finsupp.single_eq_same,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [hfun]
  exact MvPowerSeries.coeff_subst_finite (hasSubst_slotFamily_two c) φ (Finsupp.single () n)

theorem slotSubst_two_zero : slotSubst K 2 c 1 (0 : MvPowerSeries (Fin 2) ℤ) = 0 := by
  simp only [slotSubst]
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_slotFamily_two c), map_zero]

end Abstract
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve"

def genR : (LaurentSeries ℚ)ˣ :=
  Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)

@[scoped simp] theorem genR_val : (genR : LaurentSeries ℚ) = HahnSeries.single (1 : ℤ) (1 : ℚ) := rfl

@[scoped simp] theorem genR_inv_val :
    ((genR⁻¹ : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ) = HahnSeries.single (-1 : ℤ) (1 : ℚ) := by
  simp [genR, HahnSeries.inv_single]

theorem genR_pow_mul_inv_pow (i j : ℕ) :
    (genR : LaurentSeries ℚ) ^ i * ((genR⁻¹ : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ) ^ j
      = HahnSeries.single ((i : ℤ) - (j : ℤ)) (1 : ℚ) := by
  rw [genR_val, genR_inv_val, HahnSeries.single_pow, HahnSeries.single_pow, one_pow, one_pow,
    HahnSeries.single_mul_single, one_mul, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_neg_one,
    ← sub_eq_add_neg]

theorem coeff_coeff_slotSubst_gen (φ : MvPowerSeries (Fin 2) ℤ) (d : Fin 2 →₀ ℕ) :
    ((PowerSeries.coeff (d 0 + d 1)) (slotSubst (LaurentSeries ℚ) 2 genR 1 φ)).coeff
        ((d 0 : ℤ) - (d 1 : ℤ))
      = ((MvPowerSeries.coeff d φ : ℤ) : ℚ) := by
  have hmap : ∀ F : (Fin 2 →₀ ℕ) → LaurentSeries ℚ, (Function.support F).Finite →
      (finsum F).coeff ((d 0 : ℤ) - (d 1 : ℤ)) = ∑ᶠ d', (F d').coeff ((d 0 : ℤ) - (d 1 : ℤ)) :=
    fun F hF => (AddMonoidHom.mk' (fun x : LaurentSeries ℚ => x.coeff ((d 0 : ℤ) - (d 1 : ℤ)))
      (fun a b => by simp [HahnSeries.coeff_add])).map_finsum hF
  rw [coeff_slotSubst_two genR φ (d 0 + d 1),
    hmap _ (support_coeff_slotSubst_two genR φ (d 0 + d 1))]
  refine (finsum_eq_single _ d fun d' hd' => ?_).trans ?_
  · rcases eq_or_ne (d 0 + d 1) (d' 0 + d' 1) with h1 | h1
    · rw [if_pos h1, HahnSeries.coeff_smul, genR_pow_mul_inv_pow, HahnSeries.coeff_single,
        if_neg (fun hdiff => hd' (by
          have e0 : d' 0 = d 0 := by omega
          have e1 : d' 1 = d 1 := by omega
          ext i
          fin_cases i
          · exact e0
          · exact e1)), smul_zero]
    · rw [if_neg h1, smul_zero, HahnSeries.coeff_zero]
  · rw [if_pos rfl, HahnSeries.coeff_smul, genR_pow_mul_inv_pow, HahnSeries.coeff_single_same,
      zsmul_eq_mul, mul_one]

private theorem slotSubst_gen_injective :
    Function.Injective (slotSubst (LaurentSeries ℚ) 2 genR 1) := by
  intro φ ψ h
  ext d
  have h2 := congrArg
    (fun F => ((PowerSeries.coeff (d 0 + d 1)) F).coeff ((d 0 : ℤ) - (d 1 : ℤ))) h
  simp only [coeff_coeff_slotSubst_gen] at h2
  exact_mod_cast h2

theorem slotSubst_gen_eq_zero_iff (φ : MvPowerSeries (Fin 2) ℤ) :
    slotSubst (LaurentSeries ℚ) 2 genR 1 φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    apply slotSubst_gen_injective
    rw [h, slotSubst_two_zero]
  · rintro rfl
    exact slotSubst_two_zero genR

end W4Bdev
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

namespace W4Bdev

section EngineAux1

variable (K : Type*) [CommRing K]

theorem coeff_monomial_pair (a b : K) (k q m l n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.C a * PowerSeries.X ^ k) ^ m * (PowerSeries.C b * PowerSeries.X ^ q) ^ l)
      = if n = k * m + q * l then a ^ m * b ^ l else 0 := by
  have h : (PowerSeries.C a * PowerSeries.X ^ k) ^ m * (PowerSeries.C b * PowerSeries.X ^ q) ^ l
      = PowerSeries.C (a ^ m * b ^ l) * PowerSeries.X ^ (k * m + q * l) := by
    rw [mul_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, map_mul, _root_.pow_add]; ring
  rw [h, PowerSeries.coeff_C_mul_X_pow]

theorem coeff_prod_slotFamily (p : ℕ) (c : Kˣ) (k : ℕ) (d : Fin 2 →₀ ℕ) (n : ℕ) :
    PowerSeries.coeff n (d.prod fun s e => slotFamily K p c k s ^ e) =
      if n = k * d 0 + (p - k) * d 1 then (c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1 else 0 := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  exact coeff_monomial_pair K (c : K) ((c⁻¹ : Kˣ) : K) k (p - k) (d 0) (d 1) n

theorem coeff_slotSubst_finsum (p : ℕ) (c : Kˣ) (k : ℕ) (hk : 0 < k) (hkp : k < p)
    (f : MvPowerSeries (Fin 2) ℤ) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c k f) =
      ∑ᶠ d : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff d f : ℤ) : K) *
        (if n = k * d 0 + (p - k) * d 1 then (c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1 else 0) := by
  have h := MvPowerSeries.coeff_subst (hasSubst_slotFamily K p c k hk hkp) f (Finsupp.single () n)
  rw [slotSubst]
  show MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst (slotFamily K p c k) f) = _
  rw [h]
  refine finsum_congr fun d => ?_
  show (MvPowerSeries.coeff d f : ℤ) • PowerSeries.coeff n (d.prod fun s e => slotFamily K p c k s ^ e) = _
  rw [coeff_prod_slotFamily, Algebra.smul_def, eq_intCast]

end EngineAux1
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

section Bridge

variable {K : Type*} [CommRing K]

theorem coe_pow_add_mul_inv_pow (c : Kˣ) (b e : ℕ) :
    (c : K) ^ (b + e) * ((c⁻¹ : Kˣ) : K) ^ b = (c : K) ^ e := by
  rw [pow_add, mul_comm ((c : K) ^ b), mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]

theorem coe_pow_mul_inv_pow_add (c : Kˣ) (b e : ℕ) :
    (c : K) ^ b * ((c⁻¹ : Kˣ) : K) ^ (b + e) = ((c⁻¹ : Kˣ) : K) ^ e := by
  rw [pow_add, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

theorem coe_pow_mul_inv_pow_self (c : Kˣ) (b : ℕ) :
    (c : K) ^ b * ((c⁻¹ : Kˣ) : K) ^ b = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

def pairF (ab : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1 + Finsupp.single 1 ab.2

@[scoped simp] theorem pairF_apply_zero (ab : ℕ × ℕ) : pairF ab 0 = ab.1 := by
  simp [pairF]

@[scoped simp] theorem pairF_apply_one (ab : ℕ × ℕ) : pairF ab 1 = ab.2 := by
  simp [pairF]

theorem eq_pairF (d : Fin 2 →₀ ℕ) : d = pairF (d 0, d 1) := by
  ext i
  fin_cases i <;> simp [pairF]

theorem coeff_slotSubst_eq_boxSum (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (φ : MvPowerSeries (Fin 2) ℤ) (E : ℕ → ℕ → ℤ)
    (hE : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d φ = E (d 0) (d 1)) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c j φ)
      = ∑ ab ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
          ((E ab.1 ab.2 : ℤ) : K) *
            (if n = j * ab.1 + (p - j) * ab.2
             then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0) := by
  rw [coeff_slotSubst_finsum K p c j hj hjp φ n]
  have hsupp : (Function.support fun d : Fin 2 →₀ ℕ =>
      ((MvPowerSeries.coeff d φ : ℤ) : K) *
        (if n = j * d 0 + (p - j) * d 1
         then (c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1 else 0))
      ⊆ ↑((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image pairF) := by
    intro d hd
    simp only [Function.mem_support] at hd
    have hcond : n = j * d 0 + (p - j) * d 1 := by
      by_contra hc
      simp [hc] at hd
    have hd0 : d 0 ≤ n := by
      have h1 : d 0 ≤ j * d 0 := Nat.le_mul_of_pos_left _ hj
      omega
    have hd1 : d 1 ≤ n := by
      have h1 : d 1 ≤ (p - j) * d 1 := Nat.le_mul_of_pos_left _ (by omega)
      omega
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(d 0, d 1), ?_, (eq_pairF d).symm⟩)
    simp [Finset.mem_product, hd0, hd1]
  have hinj : ∀ x ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      ∀ y ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), pairF x = pairF y → x = y := by
    intro x _ y _ h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp only [pairF_apply_zero, pairF_apply_one] at h0 h1
    exact Prod.ext h0 h1
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [hE (pairF ab)]
  simp

def tableEntry (Dterm U V : ℕ → ℤ) (a b : ℕ) : ℤ :=
  if a = b then ∑ e ∈ b.divisors, Dterm e
  else if b < a then (if a - b ∣ b then U (a - b) else 0)
  else (if b - a ∣ b then V (b - a) else 0)

theorem coeff_tateUnivX_eq (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d tateUnivX
      = tableEntry (fun e => -2 * e) (fun e => (e : ℤ)) (fun e => (e : ℤ)) (d 0) (d 1) := by
  rw [MvPowerSeries.coeff_apply]
  show (if d 0 = d 1 then -2 * ∑ e ∈ (d 1).divisors, (e : ℤ)
    else if d 1 < d 0 then (if d 0 - d 1 ∣ d 1 then ((d 0 - d 1 : ℕ) : ℤ) else 0)
    else (if d 1 - d 0 ∣ d 1 then ((d 1 - d 0 : ℕ) : ℤ) else 0)) = _
  rw [tableEntry, Finset.mul_sum]

theorem coeff_tateUnivY_eq (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d tateUnivY
      = tableEntry (fun e => (e : ℤ)) (fun e => (e.choose 2 : ℤ))
          (fun e => -(((e + 1).choose 2 : ℕ) : ℤ)) (d 0) (d 1) := by
  rw [MvPowerSeries.coeff_apply]
  rfl

theorem boxSum_eq_head_add_doubleSum (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (Dterm U V : ℕ → ℤ) (hU0 : U 0 = 0) (n : ℕ) :
    ∑ ab ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = (if j ∣ n then ((U (n / j) : ℤ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
            (((U e : ℤ) : K) * (c : K) ^ e * (if n = p * M + j * e then 1 else 0)
              + ((V e : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ e * (if n + j * e = p * M then 1 else 0)
              + ((Dterm e : ℤ) : K) * (if n = p * M then 1 else 0)) := by
  classical
  have hp2 : p = j + (p - j) := by omega

  have htgt : ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (((U e : ℤ) : K) * (c : K) ^ e * (if n = p * M + j * e then 1 else 0)
          + ((V e : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ e * (if n + j * e = p * M then 1 else 0)
          + ((Dterm e : ℤ) : K) * (if n = p * M then 1 else 0))
      = (∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
            if n = p * x.1 + j * x.2 then ((U x.2 : ℤ) : K) * (c : K) ^ x.2 else 0)
        + (∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
            if n + j * x.2 = p * x.1 then ((V x.2 : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ x.2 else 0)
        + (∑ M ∈ Finset.range (n + 1),
            (∑ e ∈ M.divisors, ((Dterm e : ℤ) : K)) * (if n = p * M then 1 else 0)) := by
    rw [Finset.sum_sigma, Finset.sum_sigma, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    dsimp only
    simp only [mul_ite, mul_one, mul_zero]

  rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) (fun ab => ab.2 < ab.1),
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ¬ ab.2 < ab.1)
      (fun ab => ab.1 = ab.2), Finset.filter_filter]
  have hsetD : ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      fun ab => ¬ ab.2 < ab.1 ∧ ab.1 = ab.2)
      = (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ab.1 = ab.2 :=
    Finset.filter_congr fun ab _ => by omega
  have hsetB : (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      fun ab => ¬ ab.2 < ab.1).filter fun ab => ¬ ab.1 = ab.2)
      = (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ab.1 < ab.2 := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun ab _ => by omega
  rw [hsetD, hsetB]

  have hD : ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => ab.1 = ab.2),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = ∑ M ∈ Finset.range (n + 1),
          (∑ e ∈ M.divisors, ((Dterm e : ℤ) : K)) * (if n = p * M then 1 else 0) := by
    refine Finset.sum_bij' (fun ab _ => ab.1) (fun M _ => ((M, M) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro ab hab
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
    · intro M hM
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hM, hM⟩, rfl⟩
    · intro ab hab
      exact Prod.ext rfl (Finset.mem_filter.mp hab).2
    · intro M _
      rfl
    · intro ab hab
      obtain ⟨-, heq⟩ := Finset.mem_filter.mp hab
      obtain ⟨a, b⟩ := ab
      obtain rfl : a = b := heq
      have hkey : j * a + (p - j) * a = p * a := by
        calc j * a + (p - j) * a = (j + (p - j)) * a := by ring
          _ = p * a := by rw [← hp2]
      rw [tableEntry, if_pos rfl, hkey, coe_pow_mul_inv_pow_self, Int.cast_sum, Finset.sum_mul]

  have hB : ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => ab.1 < ab.2),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = ∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
          if n + j * x.2 = p * x.1 then ((V x.2 : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ x.2 else 0 := by
    rw [← Finset.sum_filter_of_ne (p := fun ab : ℕ × ℕ => (ab.2 - ab.1) ∣ ab.2
        ∧ n + j * (ab.2 - ab.1) = p * ab.2) ?vanishB, Finset.filter_filter, ← Finset.sum_filter]
    case vanishB =>
      intro ab hab hne
      obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hab
      by_contra hcon
      rcases Decidable.not_and_iff_or_not.mp hcon with hnd | hnc
      · rw [tableEntry, if_neg (by omega), if_neg (by omega), if_neg hnd] at hne
        simp at hne
      · have hb : ab.2 = ab.1 + (ab.2 - ab.1) := by omega
        have hkey : j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1) = p * ab.2 := by
          calc j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1)
              = j * (ab.1 + (ab.2 - ab.1)) + (p - j) * ab.2 := by ring
            _ = j * ab.2 + (p - j) * ab.2 := by rw [← hb]
            _ = (j + (p - j)) * ab.2 := by ring
            _ = p * ab.2 := by rw [← hp2]
        rw [if_neg (fun hcond : n = j * ab.1 + (p - j) * ab.2 => hnc (by omega))] at hne
        simp at hne
    refine Finset.sum_bij' (fun ab _ => (⟨ab.2, ab.2 - ab.1⟩ : Σ _ : ℕ, ℕ))
      (fun x _ => ((x.1 - x.2, x.1) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro ab hab
      obtain ⟨hmem, hlt, hdvd, hcond⟩ := Finset.mem_filter.mp hab
      obtain ⟨-, hb⟩ := Finset.mem_product.mp hmem
      have hdm : ab.2 - ab.1 ∈ (ab.2).divisors := Nat.mem_divisors.mpr ⟨hdvd, by omega⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hb, hdm⟩, hcond⟩
    · intro x hx
      obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hx
      obtain ⟨hM, he⟩ := Finset.mem_sigma.mp hmem
      have hMn := Finset.mem_range.mp hM
      obtain ⟨hdvd, hM0⟩ := Nat.mem_divisors.mp he
      have hepos : 0 < x.2 := Nat.pos_of_mem_divisors he
      have heM : x.2 ≤ x.1 := Nat.le_of_dvd (by omega) hdvd
      have hsub : x.1 - (x.1 - x.2) = x.2 := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega,
        by rw [hsub]; exact hdvd, by rw [hsub]; exact hcond⟩
    · intro ab hab
      dsimp only
      obtain ⟨-, hlt, -, -⟩ := Finset.mem_filter.mp hab
      exact Prod.ext (by omega) rfl
    · intro x hx
      dsimp only
      obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, he⟩ := Finset.mem_sigma.mp hmem
      have hepos : 0 < x.2 := Nat.pos_of_mem_divisors he
      have hM0 : x.1 ≠ 0 := (Nat.mem_divisors.mp he).2
      have heM : x.2 ≤ x.1 := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp he).1
      exact Sigma.ext rfl (by simp only [heq_eq_eq]; omega)
    · intro ab hab
      obtain ⟨-, hlt, hdvd, hcond⟩ := Finset.mem_filter.mp hab
      have hb : ab.2 = ab.1 + (ab.2 - ab.1) := by omega
      have hkey : j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1) = p * ab.2 := by
        calc j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1)
            = j * (ab.1 + (ab.2 - ab.1)) + (p - j) * ab.2 := by ring
          _ = j * ab.2 + (p - j) * ab.2 := by rw [← hb]
          _ = (j + (p - j)) * ab.2 := by ring
          _ = p * ab.2 := by rw [← hp2]
      rw [tableEntry, if_neg (by omega), if_neg (by omega), if_pos hdvd,
        if_pos (show n = j * ab.1 + (p - j) * ab.2 by omega),
        show ((c⁻¹ : Kˣ) : K) ^ ab.2 = ((c⁻¹ : Kˣ) : K) ^ (ab.1 + (ab.2 - ab.1)) from by
          rw [← hb],
        coe_pow_mul_inv_pow_add]

  have hA : ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => ab.2 < ab.1),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = (if j ∣ n then ((U (n / j) : ℤ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
            if n = p * x.1 + j * x.2 then ((U x.2 : ℤ) : K) * (c : K) ^ x.2 else 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ab.2 < ab.1)
        (fun ab => ab.2 = 0), Finset.filter_filter, Finset.filter_filter]
    congr 1
    ·
      trans (∑ a ∈ (Finset.range (n + 1)).filter (fun a => 0 < a),
        ((U a : ℤ) : K) * (if n = j * a then (c : K) ^ a else 0))
      · refine Finset.sum_bij' (fun ab _ => ab.1) (fun a _ => ((a, 0) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
        · intro ab hab
          obtain ⟨hmem, hlt, hb0⟩ := Finset.mem_filter.mp hab
          exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).1, by omega⟩
        · intro a ha
          obtain ⟨hmem, hpos⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨hmem, Finset.mem_range.mpr (by omega)⟩, by omega, rfl⟩
        · intro ab hab
          obtain ⟨-, -, hb0⟩ := Finset.mem_filter.mp hab
          exact Prod.ext rfl hb0.symm
        · intro a _
          rfl
        · intro ab hab
          obtain ⟨-, hlt, hb0⟩ := Finset.mem_filter.mp hab
          obtain ⟨a, b⟩ := ab
          obtain rfl : b = 0 := hb0
          rw [tableEntry, if_neg (by omega), if_pos (show (0:ℕ) < a by omega), Nat.sub_zero,
            if_pos (dvd_zero a), mul_zero, add_zero, pow_zero, mul_one]
      · by_cases hdvd : j ∣ n
        · rw [if_pos hdvd, Finset.sum_eq_single (n / j)]
          · rw [if_pos (Nat.mul_div_cancel' hdvd).symm]
          · intro b hb hne
            rw [if_neg, mul_zero]
            intro hcon
            exact hne (by rw [hcon, Nat.mul_div_cancel_left b hj])
          · intro hns
            rcases Nat.eq_zero_or_pos (n / j) with h0 | hpos
            · rw [h0, hU0]
              simp
            · exact absurd (Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_self n j)), hpos⟩) hns
        · rw [if_neg hdvd]
          apply Finset.sum_eq_zero
          intro b _
          rw [if_neg (fun h : n = j * b => hdvd ⟨b, h⟩), mul_zero]
    ·
      rw [← Finset.sum_filter_of_ne (p := fun ab : ℕ × ℕ => (ab.1 - ab.2) ∣ ab.2
          ∧ n = p * ab.2 + j * (ab.1 - ab.2)) ?vanishA, Finset.filter_filter, ← Finset.sum_filter]
      case vanishA =>
        intro ab hab hne
        obtain ⟨-, hlt, hb0⟩ := Finset.mem_filter.mp hab
        by_contra hcon
        rcases Decidable.not_and_iff_or_not.mp hcon with hnd | hnc
        · rw [tableEntry, if_neg (by omega), if_pos hlt, if_neg hnd] at hne
          simp at hne
        · have ha : ab.1 = ab.2 + (ab.1 - ab.2) := by omega
          have hkey : j * ab.1 + (p - j) * ab.2 = p * ab.2 + j * (ab.1 - ab.2) := by
            calc j * ab.1 + (p - j) * ab.2
                = j * (ab.2 + (ab.1 - ab.2)) + (p - j) * ab.2 := by rw [← ha]
              _ = (j + (p - j)) * ab.2 + j * (ab.1 - ab.2) := by ring
              _ = p * ab.2 + j * (ab.1 - ab.2) := by rw [← hp2]
          rw [if_neg (fun hcond : n = j * ab.1 + (p - j) * ab.2 => hnc (by omega))] at hne
          simp at hne
      refine Finset.sum_bij' (fun ab _ => (⟨ab.2, ab.1 - ab.2⟩ : Σ _ : ℕ, ℕ))
        (fun x _ => ((x.1 + x.2, x.1) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
      · intro ab hab
        obtain ⟨hmem, ⟨hlt, hb0⟩, hdvd, hcond⟩ := Finset.mem_filter.mp hab
        obtain ⟨-, hb⟩ := Finset.mem_product.mp hmem
        refine Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hb, ?_⟩, hcond⟩
        exact Nat.mem_divisors.mpr ⟨hdvd, hb0⟩
      · intro x hx
        obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hx
        obtain ⟨hM, he⟩ := Finset.mem_sigma.mp hmem
        have hMn := Finset.mem_range.mp hM
        obtain ⟨hdvd, hM0⟩ := Nat.mem_divisors.mp he
        have hepos : 0 < x.2 := Nat.pos_of_mem_divisors he
        have hjx : x.2 ≤ j * x.2 := Nat.le_mul_of_pos_left _ hj
        have hpx : x.1 ≤ p * x.1 := Nat.le_mul_of_pos_left _ (by omega)
        have hsub : x.1 + x.2 - x.1 = x.2 := by omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
          ⟨by omega, by omega⟩, by rw [hsub]; exact hdvd, by rw [hsub]; exact hcond⟩
      · intro ab hab
        dsimp only
        obtain ⟨-, ⟨hlt, -⟩, -, -⟩ := Finset.mem_filter.mp hab
        exact Prod.ext (by omega) rfl
      · intro x _
        dsimp only
        exact Sigma.ext rfl (by simp only [heq_eq_eq]; omega)
      · intro ab hab
        obtain ⟨-, ⟨hlt, -⟩, hdvd, hcond⟩ := Finset.mem_filter.mp hab
        have ha : ab.1 = ab.2 + (ab.1 - ab.2) := by omega
        have hkey : j * ab.1 + (p - j) * ab.2 = p * ab.2 + j * (ab.1 - ab.2) := by
          calc j * ab.1 + (p - j) * ab.2
              = j * (ab.2 + (ab.1 - ab.2)) + (p - j) * ab.2 := by rw [← ha]
            _ = (j + (p - j)) * ab.2 + j * (ab.1 - ab.2) := by ring
            _ = p * ab.2 + j * (ab.1 - ab.2) := by rw [← hp2]
        rw [tableEntry, if_neg (by omega), if_pos hlt, if_pos hdvd, hkey, if_pos hcond,
          show (c : K) ^ ab.1 = (c : K) ^ (ab.2 + (ab.1 - ab.2)) from by rw [← ha],
          coe_pow_add_mul_inv_pow]
  rw [hD, hB, hA, htgt]
  ring

private theorem coeff_slotSubst_tateUnivX (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c j tateUnivX)
      = (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) *
            ((if n = p * M + j * e then (c : K) ^ e else 0)
              + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0)
              - (if n = p * M then 2 else 0)) := by
  rw [coeff_slotSubst_eq_boxSum p c j hj hjp tateUnivX _ coeff_tateUnivX_eq n,
    boxSum_eq_head_add_doubleSum p c j hj hjp (fun e => -2 * e) (fun e => (e : ℤ))
      (fun e => (e : ℤ)) (by simp) n]
  congr 1
  · split_ifs with h
    · norm_cast
    · rfl
  · refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    push_cast
    split_ifs <;> ring

private theorem coeff_slotSubst_tateUnivY (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c j tateUnivY)
      = (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
            ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
              - (if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e
                 else 0)
              + (if n = p * M then (e : K) else 0)) := by
  rw [coeff_slotSubst_eq_boxSum p c j hj hjp tateUnivY _ coeff_tateUnivY_eq n,
    boxSum_eq_head_add_doubleSum p c j hj hjp (fun e => (e : ℤ)) (fun e => (e.choose 2 : ℤ))
      (fun e => -(((e + 1).choose 2 : ℕ) : ℤ)) (by simp) n]
  congr 1
  · split_ifs with h
    · push_cast
      ring
    · rfl
  · refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    push_cast
    split_ifs <;> ring

end Bridge
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

end W4Bdev
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

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

theorem coeff_headX_mul (j : ℕ) (hj : 0 < j) (c : K) (m : ℕ) :
    PowerSeries.coeff (j * m) (headX K j c) = (m : K) * c ^ m := by
  rw [coeff_headX, if_pos (dvd_mul_right j m), Nat.mul_div_cancel_left m hj]

theorem coeff_headY_mul (j : ℕ) (hj : 0 < j) (c : K) (m : ℕ) :
    PowerSeries.coeff (j * m) (headY K j c) = ((m.choose 2 : ℕ) : K) * c ^ m := by
  rw [coeff_headY, if_pos (dvd_mul_right j m), Nat.mul_div_cancel_left m hj]

theorem coeff_headX_of_not_dvd (j : ℕ) (c : K) {n : ℕ} (h : ¬ j ∣ n) :
    PowerSeries.coeff n (headX K j c) = 0 := by
  rw [coeff_headX, if_neg h]

theorem coeff_headY_of_not_dvd (j : ℕ) (c : K) {n : ℕ} (h : ¬ j ∣ n) :
    PowerSeries.coeff n (headY K j c) = 0 := by
  rw [coeff_headY, if_neg h]

theorem not_dvd_sub_of_not_dvd {j n : ℕ} (h : ¬ j ∣ n) (t : ℕ) (ht : t * j ≤ n) : ¬ j ∣ n - t * j :=
  fun h' => h (by have := dvd_add h' (dvd_mul_left j t); rwa [Nat.sub_add_cancel ht] at this)

theorem headX_mul_eq (j : ℕ) (hj : 0 < j) (c : K) :
    headX K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 2 = PowerSeries.C c * PowerSeries.X ^ j := by
  have expand : headX K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 2 =
      headX K j c - PowerSeries.C (2 * c) * (headX K j c * PowerSeries.X ^ j) + PowerSeries.C (c ^ 2) * (headX K j c * PowerSeries.X ^ (2 * j)) := by
    rw [map_mul, map_pow, map_ofNat, pow_mul' PowerSeries.X 2 j]
    ring
  ext n
  rw [expand, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C_mul_X_pow]
  by_cases hjn : j ∣ n
  · obtain ⟨m, rfl⟩ := hjn
    rw [coeff_headX_mul K j hj c m]
    rcases Nat.lt_or_ge m 1 with hm | hm
    ·
      obtain rfl : m = 0 := by omega
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    ·
      obtain rfl : m = 1 := by omega
      rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), show j * 1 - j = j * 0 by omega,
        coeff_headX_mul K j hj c 0]
      simp
    ·
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      have h1 : j ≤ j * (k + 2) := Nat.le_mul_of_pos_right j (by omega)
      have h2 : 2 * j ≤ j * (k + 2) := by
        rw [Nat.mul_comm j (k + 2)]; exact Nat.mul_le_mul_right j (by omega)
      have h3 : ¬ j * (k + 2) = j := fun h =>
        absurd (Nat.eq_of_mul_eq_mul_left hj (h.trans (mul_one j).symm)) (by omega)
      have e1 : j * (k + 2) - j = j * (k + 1) := by
        rw [show k + 2 = (k + 1) + 1 from rfl, Nat.mul_succ, Nat.add_sub_cancel]
      have e2 : j * (k + 2) - 2 * j = j * k := by
        rw [Nat.mul_add, Nat.mul_comm j 2, Nat.add_sub_cancel]
      rw [if_pos h1, if_pos h2, if_neg h3, e1, e2, coeff_headX_mul K j hj c (k + 1), coeff_headX_mul K j hj c k]
      push_cast
      ring
  · have z0 := coeff_headX_of_not_dvd K j c hjn
    have z1 : (if j ≤ n then PowerSeries.coeff (n - j) (headX K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headX_of_not_dvd K j c (by simpa using not_dvd_sub_of_not_dvd hjn 1 (by simpa using h))
      · rfl
    have z2 : (if 2 * j ≤ n then PowerSeries.coeff (n - 2 * j) (headX K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headX_of_not_dvd K j c (not_dvd_sub_of_not_dvd hjn 2 h)
      · rfl
    rw [z0, z1, z2, if_neg (fun h => hjn ⟨1, by rw [h, mul_one]⟩)]
    ring

theorem headY_mul_eq (j : ℕ) (hj : 0 < j) (c : K) :
    headY K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 3 = (PowerSeries.C c * PowerSeries.X ^ j) ^ 2 := by
  have expand : headY K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 3 =
      headY K j c - PowerSeries.C (3 * c) * (headY K j c * PowerSeries.X ^ j) + PowerSeries.C (3 * c ^ 2) * (headY K j c * PowerSeries.X ^ (2 * j))
        - PowerSeries.C (c ^ 3) * (headY K j c * PowerSeries.X ^ (3 * j)) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_ofNat, pow_mul' PowerSeries.X 2 j,
      pow_mul' PowerSeries.X 3 j]
    ring
  have rhs : (PowerSeries.C c * PowerSeries.X ^ j) ^ 2 = PowerSeries.C (c ^ 2) * PowerSeries.X ^ (2 * j) := by
    rw [map_pow, pow_mul' PowerSeries.X 2 j]; ring
  ext n
  rw [expand, rhs, map_sub, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul_X_pow]
  by_cases hjn : j ∣ n
  · obtain ⟨m, rfl⟩ := hjn
    rw [coeff_headY_mul K j hj c m]
    rcases Nat.lt_or_ge m 1 with hm | hm
    · obtain rfl : m = 0 := by omega
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      rw [if_pos (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        show j * 1 - j = j * 0 by omega, coeff_headY_mul K j hj c 0]
      simp
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      have h2 : 2 * j ≤ j * 2 := by rw [Nat.mul_comm]
      rw [if_pos (by omega), if_pos h2, if_neg (by omega), if_pos (by rw [Nat.mul_comm]),
        show j * 2 - j = j * 1 by omega, show j * 2 - 2 * j = j * 0 by omega,
        coeff_headY_mul K j hj c 1, coeff_headY_mul K j hj c 0]
      norm_num [Nat.choose]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      have h1 : j ≤ j * (k + 3) := Nat.le_mul_of_pos_right j (by omega)
      have h2 : 2 * j ≤ j * (k + 3) := by
        rw [Nat.mul_comm j (k + 3)]; exact Nat.mul_le_mul_right j (by omega)
      have h3 : 3 * j ≤ j * (k + 3) := by
        rw [Nat.mul_comm j (k + 3)]; exact Nat.mul_le_mul_right j (by omega)
      have h4 : ¬ j * (k + 3) = 2 * j := fun h => by
        rw [Nat.mul_comm 2 j] at h
        exact absurd (Nat.eq_of_mul_eq_mul_left hj h) (by omega)
      have e1 : j * (k + 3) - j = j * (k + 2) := by
        rw [show k + 3 = (k + 2) + 1 from rfl, Nat.mul_succ, Nat.add_sub_cancel]
      have e2 : j * (k + 3) - 2 * j = j * (k + 1) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.mul_add, Nat.mul_comm j 2, Nat.add_sub_cancel]
      have e3 : j * (k + 3) - 3 * j = j * k := by
        rw [Nat.mul_add, Nat.mul_comm j 3, Nat.add_sub_cancel]
      rw [if_pos h1, if_pos h2, if_pos h3, if_neg h4, e1, e2, e3, coeff_headY_mul K j hj c (k + 2),
        coeff_headY_mul K j hj c (k + 1), coeff_headY_mul K j hj c k]
      have c3 : (k + 3).choose 2 = (k + 2) + (k + 2).choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ' (k + 2) 1
      have c2 : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ' (k + 1) 1
      have c1 : (k + 1).choose 2 = k + k.choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ' k 1
      rw [c3, c2, c1]
      push_cast
      ring
  · have z0 := coeff_headY_of_not_dvd K j c hjn
    have z1 : (if j ≤ n then PowerSeries.coeff (n - j) (headY K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headY_of_not_dvd K j c (by simpa using not_dvd_sub_of_not_dvd hjn 1 (by simpa using h))
      · rfl
    have z2 : (if 2 * j ≤ n then PowerSeries.coeff (n - 2 * j) (headY K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headY_of_not_dvd K j c (not_dvd_sub_of_not_dvd hjn 2 h)
      · rfl
    have z3 : (if 3 * j ≤ n then PowerSeries.coeff (n - 3 * j) (headY K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headY_of_not_dvd K j c (not_dvd_sub_of_not_dvd hjn 3 h)
      · rfl
    rw [z0, z1, z2, z3, if_neg (fun h => hjn ⟨2, by rw [h, Nat.mul_comm]⟩)]
    ring

end GeomHeads
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

section Laurent

variable (K : Type*) [Field K]

theorem single_eq_ofPowerSeries (j : ℕ) (c : K) :
    HahnSeries.single (j : ℤ) c = HahnSeries.ofPowerSeries ℤ K (PowerSeries.C c * PowerSeries.X ^ j) := by
  rw [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow]
  change _ = HahnSeries.single 0 c * HahnSeries.single (j : ℤ) 1
  rw [HahnSeries.single_mul_single, zero_add, mul_one]

theorem one_sub_single_eq_ofPowerSeries (j : ℕ) (c : K) :
    (1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c = HahnSeries.ofPowerSeries ℤ K (1 - PowerSeries.C c * PowerSeries.X ^ j) := by
  rw [map_sub, map_one, single_eq_ofPowerSeries]

theorem one_sub_single_ne_zero (j : ℕ) (hj : 0 < j) (c : K) :
    (1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : LaurentSeries K => x.coeff 0) h
  have hj0 : (0 : ℤ) ≠ (j : ℤ) := by exact_mod_cast hj.ne
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_one, HahnSeries.coeff_single, if_neg hj0,
    sub_zero, HahnSeries.coeff_zero] at h0
  exact one_ne_zero h0

private theorem single_div_one_sub_sq (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 2 =
      HahnSeries.ofPowerSeries ℤ K (headX K j c) := by
  rw [div_eq_iff (pow_ne_zero 2 (one_sub_single_ne_zero K j hj c)), one_sub_single_eq_ofPowerSeries,
    single_eq_ofPowerSeries, ← map_pow, ← map_mul, headX_mul_eq K j hj c]

private theorem single_sq_div_one_sub_cube (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c ^ 2 / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 3 =
      HahnSeries.ofPowerSeries ℤ K (headY K j c) := by
  rw [div_eq_iff (pow_ne_zero 3 (one_sub_single_ne_zero K j hj c)), one_sub_single_eq_ofPowerSeries,
    single_eq_ofPowerSeries, ← map_pow, ← map_pow, ← map_mul, headY_mul_eq K j hj c]

theorem single_div_one_sub_sq_coeff (j : ℕ) (hj : 0 < j) (c : K) (n : ℕ) :
    (HahnSeries.single (j : ℤ) c / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 2).coeff (n : ℤ) =
      if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0 := by
  rw [single_div_one_sub_sq K j hj c, HahnSeries.ofPowerSeries_apply_coeff, coeff_headX]

theorem single_sq_div_one_sub_cube_coeff (j : ℕ) (hj : 0 < j) (c : K) (n : ℕ) :
    (HahnSeries.single (j : ℤ) c ^ 2 / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 3).coeff (n : ℤ) =
      if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0 := by
  rw [single_sq_div_one_sub_cube K j hj c, HahnSeries.ofPowerSeries_apply_coeff, coeff_headY]

end Laurent
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

end
p2m_reactivate "P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve.W4Bdev"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors.ModularCurve in

theorem solution (K : Type*) [Field K] (p : ℕ) (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) : (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) :=
  ModularCurve.toricPoint_snd_coeff_mul' K p hp c hM

#print axioms solution

end S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors
end P2MW
export P2MW.S_ModularCurve_toricPoint_snd_coeff_mul_eq_sum_divisors (solution)
