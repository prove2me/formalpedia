-- Prove2me | solution 1 for ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/75b938e7-dcc1-5be9-88e2-0e33e653785d

import Mathlib
import Definitions.Def_LaurentSeries_XAdic
import Definitions.Def_TateCurve_PointSeries
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivX
import Theorems.Thm_ModularCurve_coeff_slotSubst_tateUnivY
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst

set_option autoImplicit false

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

theorem norm_le_norm_X_pow_iff (x : LaurentSeries F) (D : ℕ) :
    ‖x‖ ≤ ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ D‖ ↔ ∀ n : ℤ, n < D → x.coeff n = 0 := by
  rw [Valued.toNormedField.norm_le_iff, ← HahnSeries.ofPowerSeries_X, LaurentSeries.valuation_X_pow,
    LaurentSeries.valuation_le_iff_coeff_lt_eq_zero]

theorem hasSum_of_coeff {α : Type*} (f : α → LaurentSeries F) (S : LaurentSeries F)
    (hfin : ∀ D : ℤ, Set.Finite {a : α | ∃ n < D, (f a).coeff n ≠ 0})
    (hcoeff : ∀ n : ℤ, S.coeff n = ∑ᶠ a, (f a).coeff n) :
    HasSum f S := by
  classical
  rw [HasSum, SummationFilter.unconditional_filter, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨D, hD⟩ : ∃ D : ℕ, ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F)‖ ^ D < ε :=
    exists_pow_lt_of_lt_one hε (LaurentSeries.XAdic.norm_X_lt_one F)
  refine ⟨(hfin D).toFinset, fun T hT => ?_⟩
  rw [dist_eq_norm]
  have hD' : ‖(HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ D‖ < ε := by rwa [norm_pow]
  refine lt_of_le_of_lt ?_ hD'
  rw [norm_le_norm_X_pow_iff]
  intro n hn
  have hsupp : (Function.support fun a => (f a).coeff n) ⊆ T := fun a ha =>
    hT ((hfin D).mem_toFinset.mpr ⟨n, hn, ha⟩)
  rw [HahnSeries.coeff_sub, HahnSeries.coeff_sum, hcoeff n, finsum_eq_sum_of_support_subset _ hsupp, sub_self]

theorem tsum_eq_of_coeff {α : Type*} (f : α → LaurentSeries F) (S : LaurentSeries F)
    (hfin : ∀ D : ℤ, Set.Finite {a : α | ∃ n < D, (f a).coeff n ≠ 0})
    (hcoeff : ∀ n : ℤ, S.coeff n = ∑ᶠ a, (f a).coeff n) :
    ∑' a, f a = S :=
  (hasSum_of_coeff f S hfin hcoeff).tsum_eq

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

variable (F) in

def expand (N : ℕ) (hN : 0 < N) : LaurentSeries F →+* LaurentSeries F :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast hN.ne'))
    (fun _ _ => mul_le_mul_iff_of_pos_left (by exact_mod_cast hN))

theorem expand_eq_qExpand (N : ℕ) [NeZero N] (hN : 0 < N) : expand F N hN = qExpand F N := rfl

theorem expand_coeff_mul (N : ℕ) (hN : 0 < N) (f : LaurentSeries F) (k : ℤ) :
    (expand F N hN f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff

theorem expand_coeff_of_not_dvd (N : ℕ) (hN : 0 < N) (f : LaurentSeries F) {i : ℤ}
    (hi : ¬ (N : ℤ) ∣ i) : (expand F N hN f).coeff i = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact hi ⟨m, rfl⟩

theorem expand_single (N : ℕ) (hN : 0 < N) (k : ℤ) (a : F) :
    expand F N hN (single k a) = single ((N : ℤ) * k) a :=
  HahnSeries.embDomain_single

theorem expand_C (N : ℕ) (hN : 0 < N) (a : F) : expand F N hN (HahnSeries.C a) = HahnSeries.C a :=
  HahnSeries.embDomainRingHom_C

theorem X_pow_eq_single (N : ℕ) :
    (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N = single (N : ℤ) 1 := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, HahnSeries.single_mul_single, mul_one]
    push_cast
    rfl

theorem expand_X (N : ℕ) (hN : 0 < N) :
    expand F N hN (single 1 1) = (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N := by
  rw [expand_single, mul_one, X_pow_eq_single]

theorem expand_X_pow (N : ℕ) (hN : 0 < N) (k : ℕ) :
    expand F N hN ((single (1 : ℤ) (1 : F)) ^ k) = (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ (N * k) := by
  rw [map_pow, expand_X, ← pow_mul]

theorem expand_ofPowerSeries_coeff (N : ℕ) (hN : 0 < N) (g : PowerSeries F) (i : ℤ) :
    (expand F N hN (ofPowerSeries ℤ F g)).coeff i
      = if (N : ℤ) ∣ i ∧ 0 ≤ i then PowerSeries.coeff (i / N).toNat g else 0 := by
  by_cases hdvd : (N : ℤ) ∣ i
  · obtain ⟨k, rfl⟩ := hdvd
    rw [expand_coeff_mul, PowerSeries.coeff_coe]
    have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
    rw [Int.mul_ediv_cancel_left _ hN0]
    by_cases hk : k < 0
    · rw [if_pos hk, if_neg]
      rintro ⟨-, h⟩
      have : 0 ≤ k := by
        rcases (mul_nonneg_iff_of_pos_left (show (0:ℤ) < N by exact_mod_cast hN)).mp h with h'
        exact h'
      omega
    · rw [if_neg hk, if_pos ⟨⟨k, rfl⟩, mul_nonneg (by positivity) (by omega)⟩, show k.natAbs = k.toNat by omega]
  · rw [expand_coeff_of_not_dvd N hN _ hdvd, if_neg (fun h => hdvd h.1)]

theorem hasSum_expand (p : ℕ) (hp : 0 < p) (g : ℕ → PowerSeries F)
    (hg : ∀ n, PowerSeries.coeff 0 (g n) = 0) (E : ℕ → LaurentSeries F) (hE0 : E 0 = 0)
    (hE : ∀ n, 0 < n → ∀ hn : 0 < p * n, E n = expand F (p * n) hn (ofPowerSeries ℤ F (g n))) :
    HasSum E (expand F p hp (ofPowerSeries ℤ F
      (PowerSeries.mk fun M => ∑ n ∈ M.divisors, PowerSeries.coeff (M / n) (g n)))) := by

  have hcoeffE : ∀ n i, (E n).coeff i ≠ 0 →
      0 < n ∧ ((p * n : ℕ) : ℤ) ∣ i ∧ 0 < i ∧ (E n).coeff i = PowerSeries.coeff (i / (p * n : ℕ)).toNat (g n) := by
    intro n i h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact absurd (by rw [hE0, HahnSeries.coeff_zero]) h
    have hpn : 0 < p * n := Nat.mul_pos hp hn
    rw [hE n hn hpn, expand_ofPowerSeries_coeff] at h ⊢
    split_ifs at h ⊢ with hc
    · refine ⟨hn, hc.1, ?_, rfl⟩
      rcases hc.2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply h
        subst heq
        rw [Int.zero_ediv, Int.toNat_zero]
        exact hg n
    · exact absurd rfl h
  apply hasSum_of_coeff
  · intro D
    refine (Set.finite_lt_nat D.toNat).subset ?_
    rintro n ⟨i, hi, hne⟩
    obtain ⟨hn, hdvd, hipos, -⟩ := hcoeffE n i hne
    have hle : ((p * n : ℕ) : ℤ) ≤ i := Int.le_of_dvd hipos hdvd
    show n < D.toNat
    have : (n : ℤ) ≤ p * n := by exact_mod_cast Nat.le_mul_of_pos_left n hp
    push_cast at hle
    omega
  · intro i
    rw [expand_ofPowerSeries_coeff]
    split_ifs with hc
    · obtain ⟨⟨k, rfl⟩, hk⟩ := hc
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
      have hk0 : 0 ≤ k := by
        rcases (mul_nonneg_iff_of_pos_left (show (0:ℤ) < p by exact_mod_cast hp)).mp hk with h'
        exact h'
      obtain ⟨M, rfl⟩ := Int.eq_ofNat_of_zero_le hk0
      rw [Int.mul_ediv_cancel_left _ hp0, Int.toNat_natCast, PowerSeries.coeff_mk]

      symm
      rw [finsum_eq_sum_of_support_subset (s := M.divisors)]
      · refine Finset.sum_congr rfl fun n hn => ?_
        obtain ⟨hnM, hM0⟩ := Nat.mem_divisors.mp hn
        have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hnM (Nat.pos_of_ne_zero hM0)
        have hpn : 0 < p * n := Nat.mul_pos hp hn0
        rw [hE n hn0 hpn, expand_ofPowerSeries_coeff, if_pos]
        · congr 1
          obtain ⟨m, rfl⟩ := hnM
          push_cast
          rw [show (p : ℤ) * ((n : ℤ) * m) = ((p : ℤ) * n) * m by ring,
            Int.mul_ediv_cancel_left _ (by positivity), Int.toNat_natCast, Nat.mul_div_cancel_left _ hn0]
        · refine ⟨?_, by positivity⟩
          obtain ⟨m, rfl⟩ := hnM
          exact ⟨m, by push_cast; ring⟩
      · intro n hn
        rw [Function.mem_support] at hn
        obtain ⟨hn0, hdvd, hipos, -⟩ := hcoeffE n _ hn
        rw [Finset.mem_coe, Nat.mem_divisors]
        refine ⟨?_, ?_⟩
        · have : ((p : ℤ) * n) ∣ (p : ℤ) * M := by push_cast at hdvd; exact hdvd
          exact_mod_cast Int.dvd_of_mul_dvd_mul_left hp0 this
        · rintro rfl
          simp at hipos
    ·
      symm
      apply finsum_eq_zero_of_forall_eq_zero
      intro n
      by_contra hne
      obtain ⟨hn0, hdvd, hipos, -⟩ := hcoeffE n i hne
      apply hc
      refine ⟨?_, hipos.le⟩
      exact (Int.dvd_mul_right (p : ℤ) n).trans (by push_cast at hdvd; exact hdvd)

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

theorem lambertSeries_mul_one_sub_X (a : F) :
    (PowerSeries.mk fun k => if k = 0 then (0 : F) else a) * (1 - PowerSeries.X) = PowerSeries.C a * PowerSeries.X := by
  ext k
  rw [mul_sub, mul_one, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases k with _ | k
  · simp
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_neg (Nat.succ_ne_zero k)]
    rcases k with _ | k
    · simp
    · rw [if_neg (Nat.succ_ne_zero k), if_neg (by omega)]
      simp

theorem X_pow_ne_one {N : ℕ} (hN : 0 < N) : (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N ≠ 1 := by
  intro h
  have := LaurentSeries.XAdic.norm_X_lt_one F
  have h1 : ‖(single (1 : ℤ) (1 : F) : LaurentSeries F) ^ N‖ = 1 := by rw [h, norm_one]
  rw [norm_pow] at h1
  exact absurd h1 (ne_of_lt (pow_lt_one₀ (norm_nonneg _) this hN.ne'))

theorem term_X_pow_eq_expand (p : ℕ) (hp : 0 < p) (c : ℕ → ℕ) (n : ℕ) (hn : 0 < n) (hpn : 0 < p * n) :
    TateCurve.term c ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) n
      = expand F (p * n) hpn (ofPowerSeries ℤ F (PowerSeries.mk fun k => if k = 0 then (0 : F) else (c n : F))) := by
  set φ : PowerSeries F →+* LaurentSeries F := (expand F (p * n) hpn).comp (ofPowerSeries ℤ F) with hφ
  have hX : φ PowerSeries.X = ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_X, expand_X, pow_mul]
  have h1 : (1 : LaurentSeries F) - ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n ≠ 0 := by
    rw [sub_ne_zero, ← pow_mul]
    exact (X_pow_ne_one (Nat.mul_pos hp hn)).symm
  have hC : φ (PowerSeries.C (c n : F)) = (c n : LaurentSeries F) := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C, expand_C, map_natCast]
  have key := congrArg φ (lambertSeries_mul_one_sub_X (c n : F))
  rw [map_mul, map_sub, map_one, map_mul, hX, hC] at key
  rw [TateCurve.term, mul_div_assoc']
  show _ = φ _
  exact (eq_div_of_mul_eq h1 key).symm

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

theorem coeffSum_X_pow (p : ℕ) (hp : 0 < p) (c : ℕ → ℕ) :
    TateCurve.coeffSum c ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      = expand F p hp (ofPowerSeries ℤ F (PowerSeries.mk fun M => ∑ n ∈ M.divisors, (c n : F))) := by
  have h := hasSum_expand p hp (fun n => PowerSeries.mk fun k => if k = 0 then (0 : F) else (c n : F))
    (fun n => by rw [PowerSeries.coeff_mk, if_pos rfl])
    (fun n => TateCurve.term c ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) n)
    (TateCurve.term_zero _ _)
    (fun n hn hpn => term_X_pow_eq_expand p hp c n hn hpn)
  have hmk : (PowerSeries.mk fun M => ∑ n ∈ M.divisors,
        PowerSeries.coeff (M / n) ((fun n => PowerSeries.mk fun k => if k = 0 then (0 : F) else (c n : F)) n))
      = PowerSeries.mk fun M => ∑ n ∈ M.divisors, (c n : F) := by
    ext M
    simp only [PowerSeries.coeff_mk]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hnM, hM0⟩ := Nat.mem_divisors.mp hn
    rw [if_neg]
    exact (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hnM)
      (Nat.pos_of_dvd_of_pos hnM (Nat.pos_of_ne_zero hM0))).ne'
  rw [TateCurve.coeffSum, h.tsum_eq, hmk]

theorem laurentOfInt_mk (f : ℕ → ℤ) :
    laurentOfInt F (PowerSeries.mk f) = ofPowerSeries ℤ F (PowerSeries.mk fun n => (f n : F)) := by
  rw [laurentOfInt_apply]
  congr 1

theorem a₄_X_pow (p : ℕ) [NeZero p] :
    TateCurve.a₄ ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) = (tateBase F p).a₄ := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  rw [TateCurve.a₄, coeffSum_X_pow p hp, tateBase, WeierstrassCurve.map_a₄, tateLaurent_a₄, tateA4,
    laurentOfInt_mk, ← expand_eq_qExpand p hp, ← map_neg, ← map_neg]
  congr 2
  ext M
  simp only [map_neg, PowerSeries.coeff_mk, Int.cast_neg, Int.cast_sum, Int.cast_mul, Int.cast_pow,
    Int.cast_ofNat, Int.cast_natCast, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem a₆_X_pow (p : ℕ) [NeZero p] :
    TateCurve.a₆ ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) = (tateBase F p).a₆ := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hb : ∀ n : ℕ, ((TateCurve.b n : ℕ) : ℤ) = tateB n := by
    intro n
    rw [TateCurve.b, tateB, Int.natCast_div]
    push_cast
    ring_nf
  rw [TateCurve.a₆, coeffSum_X_pow p hp, tateBase, WeierstrassCurve.map_a₆, tateLaurent_a₆, tateA6,
    laurentOfInt_mk, ← expand_eq_qExpand p hp, ← map_neg, ← map_neg]
  congr 2
  ext M
  simp only [map_neg, PowerSeries.coeff_mk, Int.cast_neg, Int.cast_sum, ← hb, Int.cast_natCast]

theorem curve_X_pow_eq_tateBase (p : ℕ) [NeZero p] :
    TateCurve.curve ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) = tateBase F p := by
  ext
  · rw [TateCurve.curve_a₁, tateBase, WeierstrassCurve.map_a₁]
    simp [tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  · rw [TateCurve.curve_a₂, tateBase, WeierstrassCurve.map_a₂]
    simp [tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  · rw [TateCurve.curve_a₃, tateBase, WeierstrassCurve.map_a₃]
    simp [tateLaurent, tatePowerSeries, WeierstrassCurve.map]
  · rw [TateCurve.curve_a₄, a₄_X_pow]
  · rw [TateCurve.curve_a₆, a₆_X_pow]

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

theorem coeff_one_sub_C_mul_X_mul (a : F) (f : PowerSeries F) (k : ℕ) :
    PowerSeries.coeff k ((1 - PowerSeries.C a * PowerSeries.X) * f)
      = PowerSeries.coeff k f - if k = 0 then 0 else a * PowerSeries.coeff (k - 1) f := by
  rw [sub_mul, one_mul, map_sub, mul_assoc, PowerSeries.coeff_C_mul]
  rcases k with _ | k
  · simp [PowerSeries.coeff_zero_X_mul]
  · rw [PowerSeries.coeff_succ_X_mul, if_neg (Nat.succ_ne_zero k), Nat.succ_sub_one]

theorem xSeries_identity (a : F) :
    (1 - PowerSeries.C a * PowerSeries.X) ^ 2 * (PowerSeries.mk fun k => (k : F) * a ^ k)
      = PowerSeries.C a * PowerSeries.X := by
  have h1 : (1 - PowerSeries.C a * PowerSeries.X) * (PowerSeries.mk fun k => (k : F) * a ^ k)
      = PowerSeries.mk fun k => if k = 0 then 0 else a ^ k := by
    ext k
    simp only [coeff_one_sub_C_mul_X_mul, PowerSeries.coeff_mk]
    rcases k with _ | k
    · simp
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_succ]
      push_cast
      ring
  rw [sq, mul_assoc, h1]
  ext k
  simp only [coeff_one_sub_C_mul_X_mul, PowerSeries.coeff_mk, PowerSeries.coeff_C_mul, PowerSeries.coeff_X]
  rcases k with _ | k
  · simp
  · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, Nat.succ_inj]
    rcases k with _ | k
    · simp
    · simp only [Nat.succ_ne_zero, if_false, pow_succ]
      ring

theorem one_sub_single_ne_zero {N : ℕ} (hN : 0 < N) (a : F) :
    (1 : LaurentSeries F) - single (N : ℤ) a ≠ 0 := by
  intro h
  have := congrArg (fun x : LaurentSeries F => x.coeff 0) h
  have hN' : (0 : ℤ) ≠ N := by exact_mod_cast hN.ne
  simp [HahnSeries.coeff_single_of_ne hN'] at this

theorem X_pow_pow_mul_C (p n : ℕ) (a : F) :
    ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a = single ((p * n : ℕ) : ℤ) a := by
  rw [← pow_mul, X_pow_eq_single, HahnSeries.C_apply, HahnSeries.single_mul_single, add_zero, one_mul]

theorem xfun_X_pow_mul_C (p : ℕ) (n : ℕ) (hpn : 0 < p * n) (a : F) :
    TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a)
      = expand F (p * n) hpn (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * a ^ k)) := by
  set φ : PowerSeries F →+* LaurentSeries F := (expand F (p * n) hpn).comp (ofPowerSeries ℤ F) with hφ
  have hX : φ PowerSeries.X = ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_X, expand_X, pow_mul]
  have hC : φ (PowerSeries.C a) = HahnSeries.C a := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C, expand_C]
  have h1 : (1 : LaurentSeries F) - ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a ≠ 0 := by
    rw [X_pow_pow_mul_C]; exact one_sub_single_ne_zero hpn a
  have key := congrArg φ (xSeries_identity a)
  simp only [map_mul, map_pow, map_sub, map_one, hX, hC] at key
  rw [TateCurve.xfun, eq_comm, eq_div_iff (pow_ne_zero 2 h1)]
  show φ _ * _ = _
  linear_combination key

theorem xTerm_natCast (q u : LaurentSeries F) (n : ℕ) :
    TateCurve.xTerm q u (n : ℤ) = TateCurve.xfun (q ^ n * u) := by
  rw [TateCurve.xTerm, zpow_natCast]

theorem xTerm_neg_succ (p : ℕ) (hp : 0 < p) (c : F) (hc : c ≠ 0) (n : ℕ) :
    TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C c) (-((n : ℤ) + 1))
      = TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹) := by
  have hw : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹ ≠ 0 := by
    rw [X_pow_pow_mul_C]; exact HahnSeries.single_ne_zero (inv_ne_zero hc)
  have hw1 : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹ ≠ 1 := by
    intro h
    apply one_sub_single_ne_zero (F := F) (Nat.mul_pos hp (Nat.succ_pos n)) c⁻¹
    rw [← X_pow_pow_mul_C, h, sub_self]
  have hz : (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [TateCurve.xTerm, hz, zpow_neg, zpow_natCast, ← TateCurve.xfun_inv hw hw1, mul_inv, map_inv₀, inv_inv]

variable (F) in

def xPos (p : ℕ) (hp : 0 < p) (a : F) : LaurentSeries F :=
  expand F p hp (ofPowerSeries ℤ F (PowerSeries.mk fun M => ∑ n ∈ M.divisors, ((M / n : ℕ) : F) * a ^ (M / n)))

theorem hasSum_xfun_pos (p : ℕ) (hp : 0 < p) (a : F) :
    HasSum (fun n : ℕ => if n = 0 then 0 else
      TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a)) (xPos F p hp a) := by
  have h := hasSum_expand p hp (fun _ => PowerSeries.mk fun k => (k : F) * a ^ k)
    (fun n => by simp)
    (fun n : ℕ => if n = 0 then 0 else
      TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a))
    (if_pos rfl)
    (fun n hn hpn => by simp only [hn.ne', if_false]; exact xfun_X_pow_mul_C p n hpn a)
  simpa only [xPos, PowerSeries.coeff_mk] using h

theorem hasSum_xTerm_toric (p : ℕ) (hp : 0 < p) (c : F) (hc : c ≠ 0) :
    HasSum (fun n : ℤ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C c) n)
      ((TateCurve.xfun (HahnSeries.C c : LaurentSeries F) + xPos F p hp c) + xPos F p hp c⁻¹) := by
  have hpos : HasSum (fun n : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      (HahnSeries.C c) (n : ℤ)) (TateCurve.xfun (HahnSeries.C c : LaurentSeries F) + xPos F p hp c) := by
    have hfun : (fun n : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C c) (n : ℤ)) = fun n => (if n = 0 then TateCurve.xfun (HahnSeries.C c : LaurentSeries F) else 0)
          + (if n = 0 then 0 else TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C c)) := by
      funext n
      rcases n with _ | n
      · simp
      · rw [xTerm_natCast, if_neg (Nat.succ_ne_zero n), if_neg (Nat.succ_ne_zero n), zero_add]
    rw [hfun]
    exact (hasSum_ite_eq 0 _).add (hasSum_xfun_pos p hp c)
  have hneg : HasSum (fun n : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      (HahnSeries.C c) (-((n : ℤ) + 1))) (xPos F p hp c⁻¹) := by
    have h3 := (hasSum_nat_add_iff' 1).mpr (hasSum_xfun_pos p hp c⁻¹)
    rw [Finset.sum_range_one] at h3
    simp only [if_true, sub_zero, Nat.succ_ne_zero, if_false] at h3
    have hfun : (fun n : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C c) (-((n : ℤ) + 1)))
        = fun n => TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹) := by
      funext n; exact xTerm_neg_succ p hp c hc n
    rw [hfun]
    exact h3
  exact HasSum.of_nat_of_neg_add_one hpos hneg

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

theorem s₁_X_pow (p : ℕ) (hp : 0 < p) :
    TateCurve.s₁ ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      = expand F p hp (ofPowerSeries ℤ F (PowerSeries.mk fun M => ∑ n ∈ M.divisors, (n : F))) := by
  rw [TateCurve.s₁, coeffSum_X_pow p hp]

theorem xfun_C (c : F) : TateCurve.xfun (HahnSeries.C c : LaurentSeries F) = HahnSeries.C (c / (1 - c) ^ 2) := by
  rw [TateCurve.xfun, map_div₀, map_pow, map_sub, map_one]

theorem C_eq_expand_ofPowerSeries_C (p : ℕ) (hp : 0 < p) (x : F) :
    (HahnSeries.C x : LaurentSeries F) = expand F p hp (ofPowerSeries ℤ F (PowerSeries.C x)) := by
  rw [HahnSeries.ofPowerSeries_C, expand_C]

theorem ofPowerSeries_eq_expand (p : ℕ) (hp : 0 < p) (f : PowerSeries F)
    (hf : ∀ m, ¬ p ∣ m → PowerSeries.coeff m f = 0) :
    ofPowerSeries ℤ F f = expand F p hp (ofPowerSeries ℤ F (PowerSeries.mk fun M => PowerSeries.coeff (p * M) f)) := by
  ext i
  rw [expand_ofPowerSeries_coeff, PowerSeries.coeff_coe]
  by_cases hi : i < 0
  · rw [if_pos hi, if_neg (fun h => by omega)]
  · rw [if_neg hi]
    push Not at hi
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    rw [Int.natAbs_natCast]
    by_cases hpm : p ∣ m
    · obtain ⟨M, rfl⟩ := hpm
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne'
      rw [if_pos ⟨⟨M, by push_cast; ring⟩, by positivity⟩, PowerSeries.coeff_mk]
      congr 2
      push_cast
      rw [Int.mul_ediv_cancel_left _ hp0, Int.toNat_natCast]
    · rw [hf m hpm, if_neg]
      rintro ⟨h, -⟩
      exact hpm (by exact_mod_cast h)

theorem sum_divisors_mul_ite {A : Type*} [AddCommMonoid A] (p : ℕ) (hp : 0 < p) (M : ℕ) (g : ℕ → A) :
    ∑ d ∈ (p * M).divisors, (if p ∣ d then g (p * M / d) else 0) = ∑ n ∈ M.divisors, g (M / n) := by
  classical
  rw [← Finset.sum_filter]
  have hset : (p * M).divisors.filter (fun d => p ∣ d)
      = M.divisors.map ⟨fun n => p * n, mul_right_injective₀ hp.ne'⟩ := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨hd, hpM⟩, ⟨n, rfl⟩⟩
      exact ⟨n, ⟨(Nat.mul_dvd_mul_iff_left hp).mp hd, fun h => hpM (by rw [h, mul_zero])⟩, rfl⟩
    · rintro ⟨n, ⟨hn, hM⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left p hn, Nat.mul_ne_zero hp.ne' hM⟩, Dvd.intro n rfl⟩
  rw [hset, Finset.sum_map]
  refine Finset.sum_congr rfl fun n hn => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.mul_div_mul_left _ _ hp]

set_option maxHeartbeats 3200000 in

theorem pointX_toric (p : ℕ) [NeZero p] (c : Fˣ) (hc : (c : F) ≠ 1) :
    TateCurve.pointX ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C (c : F))
      = (tateToricPoint F p c).1 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  have h1c : (1 : F) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  rw [tateToricPoint_fst, ofPowerSeries_eq_expand p hp _ ?side]
  case side =>
    intro m hpm
    have hm0 : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
    rw [PowerSeries.coeff_mk, if_neg hm0, if_neg hpm, mul_zero, sub_zero]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [if_neg]
    exact fun hpd => hpm (hpd.trans (Nat.dvd_of_mem_divisors hd))
  rw [TateCurve.pointX, (hasSum_xTerm_toric p hp (c : F) hc0).tsum_eq, s₁_X_pow p hp, xfun_C,
    C_eq_expand_ofPowerSeries_C p hp]

  set ψ : PowerSeries F →+* LaurentSeries F := (expand F p hp).comp (ofPowerSeries ℤ F) with hψ
  simp only [xPos]
  show ψ _ + ψ _ + ψ _ - 2 * ψ _ = ψ _
  rw [two_mul, ← map_add, ← map_add, ← map_add, ← map_sub]
  congr 1
  ext M
  simp only [map_add, map_sub, PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [Ring.inverse_eq_inv, div_eq_mul_inv]
  · have hpM : p * M ≠ 0 := Nat.mul_ne_zero hp.ne' hM.ne'
    rw [if_neg hM.ne', if_neg hpM, if_pos (Dvd.intro M rfl), Nat.mul_div_cancel_left _ hp,
      sum_divisors_mul_ite p hp M (fun k => ((k : ℕ) : F) * ((c : F) ^ k + ((c⁻¹ : Fˣ) : F) ^ k))]
    simp only [Units.val_inv_eq_inv_val, mul_add, Finset.sum_add_distrib, zero_add]
    ring

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

theorem ySeries_identity (a : F) :
    (1 - PowerSeries.C a * PowerSeries.X) ^ 3 * (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * a ^ k)
      = (PowerSeries.C a * PowerSeries.X) ^ 2 := by

  have h1 : (1 - PowerSeries.C a * PowerSeries.X) * (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * a ^ k)
      = PowerSeries.mk fun k => ((k - 1 : ℕ) : F) * a ^ k := by
    ext k
    simp only [coeff_one_sub_C_mul_X_mul, PowerSeries.coeff_mk]
    rcases k with _ | k
    · simp
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_succ, Nat.choose_succ_succ', Nat.choose_one_right,
        Nat.cast_add]
      ring

  have h2 : (1 - PowerSeries.C a * PowerSeries.X) * (PowerSeries.mk fun k => ((k - 1 : ℕ) : F) * a ^ k)
      = PowerSeries.mk fun k => if k ≤ 1 then 0 else a ^ k := by
    ext k
    simp only [coeff_one_sub_C_mul_X_mul, PowerSeries.coeff_mk]
    rcases k with _ | k
    · simp
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, pow_succ]
      rcases k with _ | k
      · simp
      · rw [if_neg (by omega), Nat.add_sub_cancel]
        push_cast
        ring

  have h3 : (1 - PowerSeries.C a * PowerSeries.X) * (PowerSeries.mk fun k => if k ≤ 1 then (0 : F) else a ^ k)
      = (PowerSeries.C a * PowerSeries.X) ^ 2 := by
    ext k
    rw [coeff_one_sub_C_mul_X_mul, PowerSeries.coeff_mk, mul_pow, ← map_pow, PowerSeries.coeff_C_mul_X_pow]
    rcases k with _ | k
    · simp
    · simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, PowerSeries.coeff_mk]
      rcases k with _ | k
      · simp
      · rw [if_neg (by omega)]
        rcases k with _ | k
        · simp [pow_succ]
        · rw [if_neg (by omega), if_neg (by omega), pow_succ]
          ring
  rw [pow_succ, mul_assoc, h1, sq, mul_assoc, h2, h3]

theorem yfun_X_pow_mul_C (p : ℕ) (n : ℕ) (hpn : 0 < p * n) (a : F) :
    TateCurve.yfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a)
      = expand F (p * n) hpn (ofPowerSeries ℤ F (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * a ^ k)) := by
  set φ : PowerSeries F →+* LaurentSeries F := (expand F (p * n) hpn).comp (ofPowerSeries ℤ F) with hφ
  have hX : φ PowerSeries.X = ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_X, expand_X, pow_mul]
  have hC : φ (PowerSeries.C a) = HahnSeries.C a := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C, expand_C]
  have h1 : (1 : LaurentSeries F) - ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a ≠ 0 := by
    rw [X_pow_pow_mul_C]; exact one_sub_single_ne_zero hpn a
  have key := congrArg φ (ySeries_identity a)
  simp only [map_mul, map_pow, map_sub, map_one, hX, hC] at key
  rw [TateCurve.yfun, eq_comm, eq_div_iff (pow_ne_zero 3 h1)]
  show φ _ * _ = _
  linear_combination key

theorem yTerm_natCast (q u : LaurentSeries F) (n : ℕ) :
    TateCurve.yTerm q u (n : ℤ) = TateCurve.yfun (q ^ n * u) := by
  rw [TateCurve.yTerm, zpow_natCast]

theorem yTerm_neg_succ (p : ℕ) (hp : 0 < p) (c : F) (hc : c ≠ 0) (n : ℕ) :
    TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C c) (-((n : ℤ) + 1))
      = -TateCurve.yfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹)
        - TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹) := by
  have hw : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹ ≠ 0 := by
    rw [X_pow_pow_mul_C]; exact HahnSeries.single_ne_zero (inv_ne_zero hc)
  have hw1 : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹ ≠ 1 := by
    intro h
    apply one_sub_single_ne_zero (F := F) (Nat.mul_pos hp (Nat.succ_pos n)) c⁻¹
    rw [← X_pow_pow_mul_C, h, sub_self]
  have hz : (-((n : ℤ) + 1)) = -(((n + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [TateCurve.yTerm, hz, zpow_neg, zpow_natCast, ← TateCurve.yfun_inv hw hw1, mul_inv, map_inv₀, inv_inv]

variable (F) in

def yPos (p : ℕ) (hp : 0 < p) (a : F) : LaurentSeries F :=
  expand F p hp (ofPowerSeries ℤ F
    (PowerSeries.mk fun M => ∑ n ∈ M.divisors, (((M / n).choose 2 : ℕ) : F) * a ^ (M / n)))

theorem hasSum_yfun_pos (p : ℕ) (hp : 0 < p) (a : F) :
    HasSum (fun n : ℕ => if n = 0 then 0 else
      TateCurve.yfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a)) (yPos F p hp a) := by
  have h := hasSum_expand p hp (fun _ => PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * a ^ k)
    (fun n => by simp)
    (fun n : ℕ => if n = 0 then 0 else
      TateCurve.yfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C a))
    (if_pos rfl)
    (fun n hn hpn => by simp only [hn.ne', if_false]; exact yfun_X_pow_mul_C p n hpn a)
  simpa only [yPos, PowerSeries.coeff_mk] using h

theorem hasSum_yTerm_toric (p : ℕ) (hp : 0 < p) (c : F) (hc : c ≠ 0) :
    HasSum (fun n : ℤ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C c) n)
      ((TateCurve.yfun (HahnSeries.C c : LaurentSeries F) + yPos F p hp c)
        + (-yPos F p hp c⁻¹ - xPos F p hp c⁻¹)) := by
  have hpos : HasSum (fun n : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      (HahnSeries.C c) (n : ℤ)) (TateCurve.yfun (HahnSeries.C c : LaurentSeries F) + yPos F p hp c) := by
    have hfun : (fun n : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C c) (n : ℤ)) = fun n => (if n = 0 then TateCurve.yfun (HahnSeries.C c : LaurentSeries F) else 0)
          + (if n = 0 then 0 else TateCurve.yfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ n * HahnSeries.C c)) := by
      funext n
      rcases n with _ | n
      · simp
      · rw [yTerm_natCast, if_neg (Nat.succ_ne_zero n), if_neg (Nat.succ_ne_zero n), zero_add]
    rw [hfun]
    exact (hasSum_ite_eq 0 _).add (hasSum_yfun_pos p hp c)
  have hneg : HasSum (fun n : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      (HahnSeries.C c) (-((n : ℤ) + 1))) (-yPos F p hp c⁻¹ - xPos F p hp c⁻¹) := by
    have hy := (hasSum_nat_add_iff' 1).mpr (hasSum_yfun_pos p hp c⁻¹)
    have hx := (hasSum_nat_add_iff' 1).mpr (hasSum_xfun_pos p hp c⁻¹)
    rw [Finset.sum_range_one] at hy hx
    simp only [if_true, sub_zero, Nat.succ_ne_zero, if_false] at hy hx
    have hfun : (fun n : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C c) (-((n : ℤ) + 1)))
        = fun n => -TateCurve.yfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹)
            - TateCurve.xfun (((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (n + 1) * HahnSeries.C c⁻¹) := by
      funext n; exact yTerm_neg_succ p hp c hc n
    rw [hfun]
    exact hy.neg.sub hx
  exact HasSum.of_nat_of_neg_add_one hpos hneg

theorem yfun_C (c : F) : TateCurve.yfun (HahnSeries.C c : LaurentSeries F) = HahnSeries.C (c ^ 2 / (1 - c) ^ 3) := by
  rw [TateCurve.yfun, map_div₀, map_pow, map_pow, map_sub, map_one]

set_option maxHeartbeats 3200000 in

theorem pointY_toric (p : ℕ) [NeZero p] (c : Fˣ) (hc : (c : F) ≠ 1) :
    TateCurve.pointY ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (HahnSeries.C (c : F))
      = (tateToricPoint F p c).2 := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  rw [tateToricPoint_snd, ofPowerSeries_eq_expand p hp _ ?side]
  case side =>
    intro m hpm
    have hm0 : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
    rw [PowerSeries.coeff_mk, if_neg hm0, if_neg hpm, add_zero]
    refine Finset.sum_eq_zero fun d hd => ?_
    rw [if_neg]
    exact fun hpd => hpm (hpd.trans (Nat.dvd_of_mem_divisors hd))
  rw [TateCurve.pointY, (hasSum_yTerm_toric p hp (c : F) hc0).tsum_eq, s₁_X_pow p hp, yfun_C,
    C_eq_expand_ofPowerSeries_C p hp]
  set ψ : PowerSeries F →+* LaurentSeries F := (expand F p hp).comp (ofPowerSeries ℤ F) with hψ
  simp only [xPos, yPos]
  show ψ _ + ψ _ + (-ψ _ - ψ _) + ψ _ = ψ _
  rw [← map_neg, ← map_sub, ← map_add, ← map_add, ← map_add]
  congr 1
  ext M
  simp only [map_add, map_sub, map_neg, PowerSeries.coeff_mk, PowerSeries.coeff_C]
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [Ring.inverse_eq_inv, div_eq_mul_inv]
  · have hpM : p * M ≠ 0 := Nat.mul_ne_zero hp.ne' hM.ne'
    rw [if_neg hM.ne', if_neg hpM, if_pos (Dvd.intro M rfl), Nat.mul_div_cancel_left _ hp,
      sum_divisors_mul_ite p hp M
        (fun k => (((k.choose 2 : ℕ) : F) * (c : F) ^ k - (((k + 1).choose 2 : ℕ) : F) * ((c⁻¹ : Fˣ) : F) ^ k))]
    simp only [Units.val_inv_eq_inv_val, Finset.sum_sub_distrib, zero_add, Nat.choose_succ_succ', Nat.choose_one_right,
      Nat.cast_add, add_mul, Finset.sum_add_distrib]
    ring

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

theorem hasSum_expand_gen (N : ℕ → ℕ) (hN : ∀ m, m < N m) (g : ℕ → PowerSeries F)
    (hg : ∀ m, PowerSeries.coeff 0 (g m) = 0) :
    HasSum (fun m => expand F (N m) (Nat.zero_lt_of_lt (hN m)) (ofPowerSeries ℤ F (g m)))
      (ofPowerSeries ℤ F (PowerSeries.mk fun n =>
        ∑ m ∈ Finset.range (n + 1), if N m ∣ n then PowerSeries.coeff (n / N m) (g m) else 0)) := by
  have hcoeffE : ∀ m (i : ℤ), (expand F (N m) (Nat.zero_lt_of_lt (hN m)) (ofPowerSeries ℤ F (g m))).coeff i ≠ 0 →
      ((N m : ℕ) : ℤ) ∣ i ∧ 0 < i := by
    intro m i h
    rw [expand_ofPowerSeries_coeff] at h
    split_ifs at h with hc
    · refine ⟨hc.1, ?_⟩
      rcases hc.2.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso; apply h
        subst heq
        rw [Int.zero_ediv, Int.toNat_zero]
        exact hg m
    · exact absurd rfl h
  apply hasSum_of_coeff
  · intro D
    refine (Set.finite_lt_nat D.toNat).subset ?_
    rintro m ⟨i, hi, hne⟩
    obtain ⟨hdvd, hipos⟩ := hcoeffE m i hne
    have hle : ((N m : ℕ) : ℤ) ≤ i := Int.le_of_dvd hipos hdvd
    have := hN m
    show m < D.toNat
    omega
  · intro i
    rw [PowerSeries.coeff_coe]
    split_ifs with hi
    · symm
      apply finsum_eq_zero_of_forall_eq_zero
      intro m
      by_contra hne
      have := (hcoeffE m i hne).2
      omega
    · push Not at hi
      obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi
      rw [Int.natAbs_natCast, PowerSeries.coeff_mk]
      symm
      rw [finsum_eq_sum_of_support_subset (s := Finset.range (n + 1))]
      · refine Finset.sum_congr rfl fun m _ => ?_
        rw [expand_ofPowerSeries_coeff]
        by_cases hdvd : N m ∣ n
        · rw [if_pos ⟨Int.natCast_dvd_natCast.mpr hdvd, by positivity⟩, if_pos hdvd]
          congr 2
          try rw [← Int.natCast_div, Int.toNat_natCast]
        · rw [if_neg (fun h => hdvd (Int.natCast_dvd_natCast.mp h.1)), if_neg hdvd]
      · intro m hm
        rw [Function.mem_support] at hm
        obtain ⟨hdvd, hipos⟩ := hcoeffE m _ hm
        have hle : ((N m : ℕ) : ℤ) ≤ n := Int.le_of_dvd hipos hdvd
        have := hN m
        simp only [Finset.coe_range, Set.mem_Iio]
        omega

theorem expand_X' (N : ℕ) (hN : 0 < N) :
    expand F N hN (single 1 1) = (single (N : ℤ) (1 : F) : LaurentSeries F) := by
  rw [expand_single, mul_one]

theorem xfun_single (N : ℕ) (hN : 0 < N) (a : F) :
    TateCurve.xfun (single (N : ℤ) a : LaurentSeries F)
      = expand F N hN (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * a ^ k)) := by
  set φ : PowerSeries F →+* LaurentSeries F := (expand F N hN).comp (ofPowerSeries ℤ F) with hφ
  have hX : φ PowerSeries.X = single (N : ℤ) 1 := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_X, expand_X']
  have hC : φ (PowerSeries.C a) = HahnSeries.C a := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C, expand_C]
  have hCX : HahnSeries.C a * single (N : ℤ) (1 : F) = single (N : ℤ) a := by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  have h1 : (1 : LaurentSeries F) - single (N : ℤ) a ≠ 0 := one_sub_single_ne_zero hN a
  have key := congrArg φ (xSeries_identity a)
  simp only [map_mul, map_pow, map_sub, map_one, hX, hC, hCX] at key
  rw [TateCurve.xfun, eq_comm, eq_div_iff (pow_ne_zero 2 h1)]
  show φ _ * _ = _
  linear_combination key

theorem yfun_single (N : ℕ) (hN : 0 < N) (a : F) :
    TateCurve.yfun (single (N : ℤ) a : LaurentSeries F)
      = expand F N hN (ofPowerSeries ℤ F (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * a ^ k)) := by
  set φ : PowerSeries F →+* LaurentSeries F := (expand F N hN).comp (ofPowerSeries ℤ F) with hφ
  have hX : φ PowerSeries.X = single (N : ℤ) 1 := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_X, expand_X']
  have hC : φ (PowerSeries.C a) = HahnSeries.C a := by
    rw [hφ, RingHom.comp_apply, HahnSeries.ofPowerSeries_C, expand_C]
  have hCX : HahnSeries.C a * single (N : ℤ) (1 : F) = single (N : ℤ) a := by
    rw [HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]
  have h1 : (1 : LaurentSeries F) - single (N : ℤ) a ≠ 0 := one_sub_single_ne_zero hN a
  have key := congrArg φ (ySeries_identity a)
  simp only [map_mul, map_pow, map_sub, map_one, hX, hC, hCX] at key
  rw [TateCurve.yfun, eq_comm, eq_div_iff (pow_ne_zero 3 h1)]
  show φ _ * _ = _
  linear_combination key

section Reindex

variable {A : Type*} [AddCommMonoid A] (p j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) (g : ℕ → A)
include hj hjp

theorem sum_sum_divisors_pos :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n = p * M + j * e then g e else 0)
      = ∑ m ∈ Finset.range (n + 1), (if 0 < m ∧ (p * m + j) ∣ n then g (n / (p * m + j)) else 0) := by
  classical
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp
  have hL : ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n = p * M + j * e then g e else 0)
      = ∑ x ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun x => x.2 ∈ x.1.divisors ∧ n = p * x.1 + j * x.2), g x.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors] at hM ⊢
    constructor
    · rintro ⟨⟨hd, hM0⟩, he⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd
      exact ⟨by omega, ⟨hd, hM0⟩, he⟩
    · rintro ⟨-, hd, he⟩
      exact ⟨hd, he⟩
  have hR : ∑ m ∈ Finset.range (n + 1), (if 0 < m ∧ (p * m + j) ∣ n then g (n / (p * m + j)) else 0)
      = ∑ m ∈ (Finset.range (n + 1)).filter (fun m => 0 < m ∧ (p * m + j) ∣ n), g (n / (p * m + j)) := by
    rw [Finset.sum_filter]
  rw [hL, hR]
  refine Finset.sum_nbij' (fun x => x.1 / x.2) (fun m => (m * (n / (p * m + j)), n / (p * m + j)))
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hMn, -⟩, ⟨⟨m, rfl⟩, hM0⟩, hn⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    have hmle : m ≤ e * m := Nat.le_mul_of_pos_left m he0
    rw [Nat.mul_div_cancel_left m he0]
    exact ⟨by omega, hm0, ⟨e, by rw [hn]; ring⟩⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hm ⊢
    obtain ⟨hmn, hm0, ⟨e, he⟩⟩ := hm
    have hN0 : 0 < p * m + j := by omega
    have he' : n / (p * m + j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    have hele : e ≤ n := by rw [he]; exact Nat.le_mul_of_pos_left e hN0
    have hpm : m ≤ p * m := Nat.le_mul_of_pos_left m hp
    have hmle : m * e ≤ n := by
      rw [he, mul_comm (p * m + j) e, mul_comm m e]
      exact Nat.mul_le_mul_left e (by omega)
    rw [he']
    exact ⟨⟨by omega, by omega⟩, ⟨Dvd.intro_left m rfl, Nat.mul_ne_zero hm0.ne' he0.ne'⟩, by rw [he]; ring⟩
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m, rfl⟩, hM0⟩, hn⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hN0 : 0 < p * m + j := by omega
    have hq : n / (p * m + j) = e := by
      rw [hn, show p * (e * m) + j * e = e * (p * m + j) by ring, Nat.mul_div_cancel e hN0]
    simp only [Nat.mul_div_cancel_left m he0, hq, mul_comm m e]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmn, hm0, ⟨e, he⟩⟩ := hm
    have hN0 : 0 < p * m + j := by omega
    have he' : n / (p * m + j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    simp only [he', Nat.mul_div_cancel m he0]
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m, rfl⟩, hM0⟩, hn⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hN0 : 0 < p * m + j := by omega
    simp only
    rw [Nat.mul_div_cancel_left m he0, hn, show p * (e * m) + j * e = e * (p * m + j) by ring,
      Nat.mul_div_cancel e hN0]

end Reindex

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

section Reindex2

variable {A : Type*} [AddCommMonoid A] (p j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) (g : ℕ → A)
include hj hjp

theorem sum_sum_divisors_neg (hn : 0 < n) :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n + j * e = p * M then g e else 0)
      = ∑ m ∈ Finset.range (n + 1), (if (p * (m + 1) - j) ∣ n then g (n / (p * (m + 1) - j)) else 0) := by
  classical
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp

  have hjle : ∀ m' : ℕ, 0 < m' → j ≤ p * m' := fun m' hm' =>
    (le_of_lt hjp).trans (Nat.le_mul_of_pos_right p hm')
  have hNpos : ∀ m' : ℕ, 0 < m' → 0 < p * m' - j := fun m' hm' => by
    have : j < p * m' := lt_of_lt_of_le hjp (Nat.le_mul_of_pos_right p hm')
    omega

  have hmN : ∀ m' : ℕ, 0 < m' → m' ≤ p * m' - j := fun m' hm' => by
    have h1 : j + 1 ≤ p := hjp
    have : (j + 1) * m' ≤ p * m' := Nat.mul_le_mul_right m' h1
    have : j * m' + m' ≤ p * m' := by rw [Nat.succ_mul] at this; omega
    have : j ≤ j * m' := Nat.le_mul_of_pos_right j hm'
    omega
  have hL : ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n + j * e = p * M then g e else 0)
      = ∑ x ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
          (fun x => x.2 ∈ x.1.divisors ∧ n + j * x.2 = p * x.1), g x.2 := by
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun M hM => ?_
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext e
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors] at hM ⊢
    constructor
    · rintro ⟨⟨hd, hM0⟩, he⟩
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hM0) hd
      exact ⟨by omega, ⟨hd, hM0⟩, he⟩
    · rintro ⟨-, hd, he⟩
      exact ⟨hd, he⟩
  have hR : ∑ m ∈ Finset.range (n + 1), (if (p * (m + 1) - j) ∣ n then g (n / (p * (m + 1) - j)) else 0)
      = ∑ m ∈ (Finset.range (n + 1)).filter (fun m => (p * (m + 1) - j) ∣ n), g (n / (p * (m + 1) - j)) := by
    rw [Finset.sum_filter]
  rw [hL, hR]

  have hsolve : ∀ e m' : ℕ, 0 < m' → n + j * e = p * (e * m') → n = e * (p * m' - j) := by
    intro e m' hm' h
    have := hjle m' hm'
    zify [this] at h ⊢
    linear_combination h
  refine Finset.sum_nbij' (fun x => x.1 / x.2 - 1)
    (fun m => ((m + 1) * (n / (p * (m + 1) - j)), n / (p * (m + 1) - j))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx ⊢
    obtain ⟨⟨hMn, -⟩, ⟨⟨m', rfl⟩, hM0⟩, hne⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    have hmle : m' ≤ e * m' := Nat.le_mul_of_pos_left m' he0
    rw [Nat.mul_div_cancel_left m' he0, Nat.sub_add_cancel hm']
    exact ⟨by omega, ⟨e, by rw [hsolve e m' hm' hne, mul_comm]⟩⟩
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hm ⊢
    obtain ⟨hmn, ⟨e, he⟩⟩ := hm
    have hN0 := hNpos (m + 1) (Nat.succ_pos m)
    have he' : n / (p * (m + 1) - j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    have hele : e ≤ n := by rw [he]; exact Nat.le_mul_of_pos_left e hN0
    have hMle : (m + 1) * e ≤ n := by
      rw [he, mul_comm (p * (m + 1) - j) e, mul_comm (m + 1) e]
      exact Nat.mul_le_mul_left e (hmN (m + 1) (Nat.succ_pos m))
    rw [he']
    refine ⟨⟨by omega, by omega⟩, ⟨Dvd.intro_left (m + 1) rfl, Nat.mul_ne_zero (Nat.succ_ne_zero m) he0.ne'⟩, ?_⟩
    have := hjle (m + 1) (Nat.succ_pos m)
    zify [this] at he ⊢
    linear_combination he
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m', rfl⟩, hM0⟩, hne⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    have hq : n / (p * m' - j) = e := by
      rw [hsolve e m' hm' hne, Nat.mul_div_cancel e (hNpos m' hm')]
    simp only [Nat.mul_div_cancel_left m' he0, Nat.sub_add_cancel hm', hq, mul_comm m' e]
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_range] at hm
    obtain ⟨hmn, ⟨e, he⟩⟩ := hm
    have hN0 := hNpos (m + 1) (Nat.succ_pos m)
    have he' : n / (p * (m + 1) - j) = e := by rw [he, Nat.mul_div_cancel_left e hN0]
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => by rw [h, mul_zero] at he; omega
    simp only [he', Nat.mul_div_cancel (m + 1) he0, Nat.add_sub_cancel]
  · rintro ⟨M, e⟩ hx
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Nat.mem_divisors] at hx
    obtain ⟨-, ⟨⟨m', rfl⟩, hM0⟩, hne⟩ := hx
    have he0 : 0 < e := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, zero_mul])
    have hm' : 0 < m' := Nat.pos_of_ne_zero fun h => hM0 (by rw [h, mul_zero])
    simp only
    rw [Nat.mul_div_cancel_left m' he0, Nat.sub_add_cancel hm', hsolve e m' hm' hne,
      Nat.mul_div_cancel e (hNpos m' hm')]

omit hj hjp in

theorem sum_sum_divisors_diag (hp : 0 < p) :
    ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (if n = p * M then g e else 0)
      = if p ∣ n then ∑ e ∈ (n / p).divisors, g e else 0 := by
  classical
  have h1 : ∀ M, ∑ e ∈ M.divisors, (if n = p * M then g e else 0)
      = if n = p * M then ∑ e ∈ M.divisors, g e else 0 := by
    intro M; split_ifs <;> simp
  simp_rw [h1]
  by_cases hpn : p ∣ n
  · obtain ⟨M₀, rfl⟩ := hpn
    rw [if_pos (Dvd.intro M₀ rfl), Nat.mul_div_cancel_left _ hp]
    have h2 : ∀ M, (p * M₀ = p * M) = (M₀ = M) := fun M => propext (Nat.mul_right_inj hp.ne')
    simp_rw [h2]
    rw [Finset.sum_ite_eq, if_pos]
    simp only [Finset.mem_range]
    have := Nat.le_mul_of_pos_left M₀ hp
    omega
  · rw [if_neg hpn]
    refine Finset.sum_eq_zero fun M _ => ?_
    rw [if_neg]
    rintro rfl
    exact hpn (Dvd.intro M rfl)

end Reindex2

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

section Slot

variable (p j : ℕ) (hj : 0 < j) (hjp : j < p) (c : F) (hc : c ≠ 0)
include hj hjp

omit hj hjp in
theorem C_mul_X_pow : HahnSeries.C c * (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j = single (j : ℤ) c := by
  rw [X_pow_eq_single, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add, mul_one]

omit hj hjp in
theorem X_pow_pow_mul_single (m : ℕ) :
    ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ m * single (j : ℤ) c = single ((p * m + j : ℕ) : ℤ) c := by
  rw [← pow_mul, X_pow_eq_single, HahnSeries.single_mul_single, one_mul]
  push_cast
  ring_nf

include hc in
omit hj hjp in
theorem single_inv : (single (j : ℤ) c : LaurentSeries F)⁻¹ = single (-(j : ℤ)) c⁻¹ := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [HahnSeries.single_mul_single, add_neg_cancel, mul_inv_cancel₀ hc]
  rfl

include hc in
theorem X_pow_pow_mul_single_inv (m : ℕ) :
    ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹
      = single ((p * (m + 1) - j : ℕ) : ℤ) c⁻¹ := by
  have hle : j ≤ p * (m + 1) := (le_of_lt hjp).trans (Nat.le_mul_of_pos_right p (Nat.succ_pos m))
  rw [single_inv j c hc, ← pow_mul, X_pow_eq_single, HahnSeries.single_mul_single, one_mul]
  push_cast [hle]
  ring_nf

theorem lt_expPos (m : ℕ) : m < p * m + j := by
  have : m ≤ p * m := Nat.le_mul_of_pos_left m (lt_of_le_of_lt (Nat.zero_le j) hjp)
  omega

theorem lt_expNeg (m : ℕ) : m < p * (m + 1) - j := by
  have h1 : (j + 1) * (m + 1) ≤ p * (m + 1) := Nat.mul_le_mul_right (m + 1) hjp
  have h2 : j ≤ j * (m + 1) := Nat.le_mul_of_pos_right j (Nat.succ_pos m)
  rw [Nat.succ_mul] at h1
  omega

include hc in
theorem xTerm_slot_natCast (m : ℕ) :
    TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ)
      = expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c ^ k)) := by
  rw [xTerm_natCast, X_pow_pow_mul_single, xfun_single]

include hc in
theorem xTerm_slot_neg (m : ℕ) :
    TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1))
      = expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c⁻¹ ^ k)) := by
  have hw : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 0 := by
    rw [X_pow_pow_mul_single_inv p j hj hjp c hc]; exact HahnSeries.single_ne_zero (inv_ne_zero hc)
  have hw1 : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 1 := by
    intro h
    apply one_sub_single_ne_zero (F := F) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹
    rw [← X_pow_pow_mul_single_inv p j hj hjp c hc, h, sub_self]
  have hz : (-((m : ℤ) + 1)) = -(((m + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [TateCurve.xTerm, hz, zpow_neg, zpow_natCast, ← inv_inv (single (j : ℤ) c), ← mul_inv,
    TateCurve.xfun_inv hw hw1, X_pow_pow_mul_single_inv p j hj hjp c hc,
    xfun_single _ (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))]

include hc in
theorem yTerm_slot_natCast (m : ℕ) :
    TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ)
      = expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * c ^ k)) := by
  rw [yTerm_natCast, X_pow_pow_mul_single, yfun_single]

include hc in
theorem yTerm_slot_neg (m : ℕ) :
    TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1))
      = expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
          (ofPowerSeries ℤ F (PowerSeries.mk fun k => -((((k + 1).choose 2 : ℕ) : F) * c⁻¹ ^ k))) := by
  have hw : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 0 := by
    rw [X_pow_pow_mul_single_inv p j hj hjp c hc]; exact HahnSeries.single_ne_zero (inv_ne_zero hc)
  have hw1 : ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) ^ (m + 1) * (single (j : ℤ) c)⁻¹ ≠ 1 := by
    intro h
    apply one_sub_single_ne_zero (F := F) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹
    rw [← X_pow_pow_mul_single_inv p j hj hjp c hc, h, sub_self]
  have hz : (-((m : ℤ) + 1)) = -(((m + 1 : ℕ) : ℤ)) := by push_cast; ring
  rw [TateCurve.yTerm, hz, zpow_neg, zpow_natCast, ← inv_inv (single (j : ℤ) c), ← mul_inv,
    TateCurve.yfun_inv hw hw1, X_pow_pow_mul_single_inv p j hj hjp c hc,
    yfun_single _ (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹, xfun_single _ (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m)) c⁻¹,
    ← map_neg, ← map_sub, ← map_neg, ← map_sub]
  congr 2
  ext k
  simp only [map_neg, map_sub, PowerSeries.coeff_mk, Nat.choose_succ_succ', Nat.choose_one_right, Nat.cast_add]
  ring

theorem s₁_X_pow' (hp : 0 < p) :
    TateCurve.s₁ ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
      = ofPowerSeries ℤ F (PowerSeries.mk fun n => if p ∣ n then ∑ e ∈ (n / p).divisors, (e : F) else 0) := by
  rw [s₁_X_pow p hp]
  symm
  rw [ofPowerSeries_eq_expand p hp (PowerSeries.mk fun n => if p ∣ n then ∑ e ∈ (n / p).divisors, (e : F) else 0)
    (fun m hm => by rw [PowerSeries.coeff_mk, if_neg hm])]
  congr 2
  ext M
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, PowerSeries.coeff_mk, if_pos (Dvd.intro M rfl),
    Nat.mul_div_cancel_left _ hp]

end Slot

end ModularCurve.BridgeX

end

noncomputable section

open HahnSeries Filter Topology
open scoped LaurentSeries.XAdic

namespace ModularCurve
p2m_export "ModularCurve" "nonToricPoint tateBase nonToricPoint_fst nonToricPoint_snd tateB tateA4 tateA6 tatePowerSeries laurentOfInt laurentOfInt_apply tateLaurent tateLaurent_a₄ tateLaurent_a₆ qExpand tateToricPoint tateToricPoint_fst tateToricPoint_snd coeff_slotSubst_tateUnivX coeff_slotSubst_tateUnivY"
namespace BridgeX
p2m_open "ModularCurve"

variable {F : Type*} [Field F]

section SlotMain

variable (p j : ℕ) (hj : 0 < j) (hjp : j < p) (c : F) (hc : c ≠ 0)
include hj hjp hc

theorem hasSum_xTerm_slot :
    HasSum (fun n : ℤ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) n)
      (ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * m + j) ∣ n then ((n / (p * m + j) : ℕ) : F) * c ^ (n / (p * m + j)) else 0)
        + ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * (m + 1) - j) ∣ n then ((n / (p * (m + 1) - j) : ℕ) : F) * c⁻¹ ^ (n / (p * (m + 1) - j)) else 0)) := by
  have hpos := hasSum_expand_gen (F := F) (fun m => p * m + j) (lt_expPos p j hj hjp)
    (fun _ => PowerSeries.mk fun k => (k : F) * c ^ k) (fun _ => by simp)
  have hneg := hasSum_expand_gen (F := F) (fun m => p * (m + 1) - j) (lt_expNeg p j hj hjp)
    (fun _ => PowerSeries.mk fun k => (k : F) * c⁻¹ ^ k) (fun _ => by simp)
  simp only [PowerSeries.coeff_mk] at hpos hneg
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · have hfun : (fun m : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ))
        = fun m => expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c ^ k)) := by
      funext m; exact xTerm_slot_natCast p j hj hjp c hc m
    rw [hfun]; exact hpos
  · have hfun : (fun m : ℕ => TateCurve.xTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1)))
        = fun m => expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => (k : F) * c⁻¹ ^ k)) := by
      funext m; exact xTerm_slot_neg p j hj hjp c hc m
    rw [hfun]; exact hneg

theorem hasSum_yTerm_slot :
    HasSum (fun n : ℤ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) n)
      (ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * m + j) ∣ n then (((n / (p * m + j)).choose 2 : ℕ) : F) * c ^ (n / (p * m + j)) else 0)
        + ofPowerSeries ℤ F (PowerSeries.mk fun n => ∑ m ∈ Finset.range (n + 1),
          if (p * (m + 1) - j) ∣ n then -(((((n / (p * (m + 1) - j)) + 1).choose 2 : ℕ) : F)
            * c⁻¹ ^ (n / (p * (m + 1) - j))) else 0)) := by
  have hpos := hasSum_expand_gen (F := F) (fun m => p * m + j) (lt_expPos p j hj hjp)
    (fun _ => PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * c ^ k) (fun _ => by simp)
  have hneg := hasSum_expand_gen (F := F) (fun m => p * (m + 1) - j) (lt_expNeg p j hj hjp)
    (fun _ => PowerSeries.mk fun k => -((((k + 1).choose 2 : ℕ) : F) * c⁻¹ ^ k)) (fun _ => by simp)
  simp only [PowerSeries.coeff_mk] at hpos hneg
  refine HasSum.of_nat_of_neg_add_one ?_ ?_
  · have hfun : (fun m : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (m : ℤ))
        = fun m => expand F (p * m + j) (Nat.zero_lt_of_lt (lt_expPos p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => ((k.choose 2 : ℕ) : F) * c ^ k)) := by
      funext m; exact yTerm_slot_natCast p j hj hjp c hc m
    rw [hfun]; exact hpos
  · have hfun : (fun m : ℕ => TateCurve.yTerm ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p) (single (j : ℤ) c) (-((m : ℤ) + 1)))
        = fun m => expand F (p * (m + 1) - j) (Nat.zero_lt_of_lt (lt_expNeg p j hj hjp m))
            (ofPowerSeries ℤ F (PowerSeries.mk fun k => -((((k + 1).choose 2 : ℕ) : F) * c⁻¹ ^ k))) := by
      funext m; exact yTerm_slot_neg p j hj hjp c hc m
    rw [hfun]; exact hneg

omit hc in

theorem sum_split_zero {A : Type*} [AddCommMonoid A] (n : ℕ) (v : ℕ → A) :
    ∑ m ∈ Finset.range (n + 1), (if (p * m + j) ∣ n then v (n / (p * m + j)) else 0)
      = (if j ∣ n then v (n / j) else 0)
        + ∑ m ∈ Finset.range (n + 1), (if 0 < m ∧ (p * m + j) ∣ n then v (n / (p * m + j)) else 0) := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ', mul_zero, zero_add]
  simp only [Nat.succ_pos, true_and, lt_self_iff_false, false_and, if_false, add_zero]
  rw [add_comm]

end SlotMain

set_option maxHeartbeats 3200000 in

theorem pointX_slot (p : ℕ) [NeZero p] (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointX ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (nonToricPoint F p c j).1 := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  rw [C_mul_X_pow, TateCurve.pointX, (hasSum_xTerm_slot p j hj hjp (c : F) hc0).tsum_eq, s₁_X_pow' p j hj hjp hp,
    nonToricPoint_fst, two_mul, ← map_add, ← map_add, ← map_sub]
  congr 1
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_mk, coeff_slotSubst_tateUnivX p c j hj hjp n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sum_split_zero p j hj hjp n (fun k => ((k : ℕ) : F) * (c : F) ^ k)]
    conv_rhs => simp only [mul_add, mul_sub, mul_ite, mul_zero, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum_sum_divisors_pos p j hj hjp n (fun e => (e : F) * (c : F) ^ e),
      sum_sum_divisors_neg p j hj hjp n (fun e => (e : F) * ((c⁻¹ : Fˣ) : F) ^ e) hn,
      sum_sum_divisors_diag p n (fun e => (e : F) * 2) hp]
    simp only [Units.val_inv_eq_inv_val, ← Finset.sum_mul]
    split_ifs <;> ring

set_option maxHeartbeats 3200000 in

theorem pointY_slot (p : ℕ) [NeZero p] (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointY ((single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (nonToricPoint F p c j).2 := by
  have hp : 0 < p := lt_of_le_of_lt (Nat.zero_le j) hjp
  have hc0 : (c : F) ≠ 0 := c.ne_zero
  rw [C_mul_X_pow, TateCurve.pointY, (hasSum_yTerm_slot p j hj hjp (c : F) hc0).tsum_eq, s₁_X_pow' p j hj hjp hp,
    nonToricPoint_snd, ← map_add, ← map_add]
  congr 1
  ext n
  simp only [map_add, PowerSeries.coeff_mk, coeff_slotSubst_tateUnivY p c j hj hjp n]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [sum_split_zero p j hj hjp n (fun k => (((k : ℕ).choose 2 : ℕ) : F) * (c : F) ^ k)]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [sum_sum_divisors_pos p j hj hjp n (fun e => ((e.choose 2 : ℕ) : F) * (c : F) ^ e),
      sum_sum_divisors_neg p j hj hjp n (fun e => (((e + 1).choose 2 : ℕ) : F) * ((c⁻¹ : Fˣ) : F) ^ e) hn,
      sum_sum_divisors_diag p n (fun e => (e : F)) hp]
    have hneg : ∑ m ∈ Finset.range (n + 1),
        (if p * (m + 1) - j ∣ n then -((((n / (p * (m + 1) - j) + 1).choose 2 : ℕ) : F) * (c : F)⁻¹ ^ (n / (p * (m + 1) - j))) else 0)
        = -∑ m ∈ Finset.range (n + 1),
        (if p * (m + 1) - j ∣ n then (((n / (p * (m + 1) - j) + 1).choose 2 : ℕ) : F) * (c : F)⁻¹ ^ (n / (p * (m + 1) - j)) else 0) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      split_ifs <;> simp
    simp only [Units.val_inv_eq_inv_val, hneg]
    split_ifs <;> ring

end ModularCurve.BridgeX

end

open scoped LaurentSeries.XAdic in
theorem solution (F : Type*) [Field F] (p : ℕ) [NeZero p]
    (c : Fˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    TateCurve.pointX ((HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ p)
        (HahnSeries.C (c : F) * (HahnSeries.single (1 : ℤ) (1 : F) : LaurentSeries F) ^ j)
      = (ModularCurve.nonToricPoint F p c j).1 :=
  ModularCurve.BridgeX.pointX_slot p c j hj hjp

end S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst
end P2MW
export P2MW.S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst (solution)
