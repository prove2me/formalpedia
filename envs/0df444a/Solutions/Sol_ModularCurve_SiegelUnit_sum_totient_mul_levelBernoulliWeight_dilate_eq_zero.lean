-- Prove2me | solution 1 for ModularCurve.SiegelUnit.sum_totient_mul_levelBernoulliWeight_dilate_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/c76043c4-4296-5774-b29d-5e83081e6ecf

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero

set_option autoImplicit false

open Finset

namespace Ws18BDist

def Bt (N t : ℤ) : ℤ := 6 * t ^ 2 - 6 * N * t + N ^ 2

theorem sum_range_Bt_aux (N p₀ g : ℤ) (M : ℕ) :
    ∑ j ∈ range M, Bt N (p₀ + g * j) =
      M * (6 * p₀ ^ 2 - 6 * N * p₀ + N ^ 2) + (6 * p₀ * g - 3 * N * g) * (M * (M - 1)) +
        g ^ 2 * ((M - 1) * M * (2 * M - 1)) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [sum_range_succ, ih, Bt]
      push_cast
      ring

theorem sum_range_Bt (p₀ g : ℤ) (M : ℕ) :
    ∑ j ∈ range M, Bt (g * M) (p₀ + g * j) = M * (6 * p₀ ^ 2 - 6 * g * p₀ + g ^ 2) := by
  rw [sum_range_Bt_aux]
  ring

theorem sum_zmod_eq_sum_range {β : Type*} [AddCommMonoid β] (N : ℕ) [NeZero N] (Φ : ZMod N → β) :
    ∑ s : ZMod N, Φ s = ∑ i ∈ range N, Φ (i : ZMod N) := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, (Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero (NeZero.ne N))).symm⟩
  rw [← Fin.sum_univ_eq_sum_range (fun i => Φ (i : ZMod (n + 1)))]
  refine Fintype.sum_congr _ _ fun s => ?_
  exact congrArg Φ (ZMod.natCast_zmod_val s).symm

theorem periodic_shift {β : Type*} (M : ℕ) (h : ℕ → β) (hper : ∀ n, h (n + M) = h n) (k n : ℕ) :
    h (k * M + n) = h n := by
  induction k with
  | zero => simp
  | succ k ihk => rw [Nat.succ_mul, show k * M + M + n = (k * M + n) + M by ring, hper, ihk]

theorem sum_range_mul_of_periodic {β : Type*} [AddCommMonoid β] (M g : ℕ) (h : ℕ → β)
    (hper : ∀ n, h (n + M) = h n) : ∑ n ∈ range (g * M), h n = g • ∑ n ∈ range M, h n := by
  induction g with
  | zero => simp
  | succ g ih =>
      rw [Nat.succ_mul, sum_range_add, ih, succ_nsmul]
      congr 1
      exact sum_congr rfl fun n _ => periodic_shift M h hper g n

theorem emod_progression (p₀ g k : ℤ) (M : ℕ) (hp₀ : 0 ≤ p₀) (hp₀g : p₀ < g) (hM : 0 < M) :
    (p₀ + g * k) % (g * M) = p₀ + g * (k % M) := by
  have hg : 0 < g := lt_of_le_of_lt hp₀ hp₀g
  have hM' : (0 : ℤ) < M := by exact_mod_cast hM
  have hk : k = M * (k / M) + k % M := (Int.mul_ediv_add_emod k M).symm
  have hsplit : p₀ + g * k = (p₀ + g * (k % M)) + (g * M) * (k / M) := by
    conv_lhs => rw [hk]
    ring
  rw [hsplit, Int.add_mul_emod_self_left]
  apply Int.emod_eq_of_lt
  · have := Int.emod_nonneg k (ne_of_gt hM')
    positivity
  · have h1 : k % M ≤ M - 1 := by have := Int.emod_lt_of_pos k hM'; omega
    calc p₀ + g * (k % M) ≤ p₀ + g * (M - 1) := by gcongr
      _ < g + g * (M - 1) := by linarith
      _ = g * M := by ring

theorem sum_range_affine_unit (M : ℕ) (hM : 0 < M) (c u : ℤ) (hu : IsCoprime u M) (φ : ℤ → ℤ) :
    ∑ n ∈ range M, φ ((c + n * u) % M) = ∑ n ∈ range M, φ n := by
  haveI : NeZero M := ⟨Nat.pos_iff_ne_zero.mp hM⟩

  have hL : ∀ n : ℕ, φ ((c + n * u) % M) = (fun σ : ZMod M => φ (σ.val : ℤ)) ((c : ZMod M) + (n : ZMod M) * (u : ZMod M)) := by
    intro n
    simp only
    congr 1
    rw [show ((c : ZMod M) + (n : ZMod M) * (u : ZMod M)) = ((c + n * u : ℤ) : ZMod M) by push_cast; ring,
      ZMod.val_intCast]
  have hR : ∀ n ∈ range M, φ n = (fun σ : ZMod M => φ (σ.val : ℤ)) (n : ZMod M) := by
    intro n hn
    simp only
    rw [ZMod.val_natCast_of_lt (mem_range.mp hn)]

  have hunit : IsUnit (u : ZMod M) := by
    obtain ⟨a, b, hab⟩ := hu
    refine isUnit_iff_exists_inv.mpr ⟨(a : ZMod M), ?_⟩
    have := congrArg (fun z : ℤ => (z : ZMod M)) hab
    push_cast at this
    rw [ZMod.natCast_self, mul_zero, add_zero, mul_comm] at this
    exact this
  let e : ZMod M ≃ ZMod M := (hunit.unit.mulRight).trans (Equiv.addLeft (c : ZMod M))
  set ψ : ZMod M → ℤ := fun σ => φ (σ.val : ℤ) with hψ
  calc ∑ n ∈ range M, φ ((c + n * u) % M)
      = ∑ n ∈ range M, ψ ((c : ZMod M) + (n : ZMod M) * (u : ZMod M)) := sum_congr rfl fun n _ => hL n
    _ = ∑ σ : ZMod M, ψ ((c : ZMod M) + σ * (u : ZMod M)) :=
        (sum_zmod_eq_sum_range M (fun σ => ψ ((c : ZMod M) + σ * (u : ZMod M)))).symm
    _ = ∑ σ : ZMod M, ψ σ := Fintype.sum_equiv e _ _ fun σ => by simp [e]
    _ = ∑ n ∈ range M, ψ (n : ZMod M) := sum_zmod_eq_sum_range M ψ
    _ = ∑ n ∈ range M, φ n := sum_congr rfl fun n hn => (hR n hn).symm

theorem sum_zmod_comp_val_affine (N g M : ℕ) [NeZero N] (hN : N = g * M) (hg : 0 < g) (hM : 0 < M)
    (p r : ℤ) (hgr : (g : ℤ) ∣ r) (hcop : IsCoprime (r / g) (M : ℤ)) (F : ℤ → ℤ) :
    ∑ s : ZMod N, F ((((p : ZMod N) + s * (r : ZMod N)).val : ℤ)) =
      g * ∑ n ∈ range M, F (p % g + g * n) := by
  obtain ⟨r', hr'⟩ := hgr
  have hr'eq : r / g = r' := by rw [hr', Int.mul_ediv_cancel_left _ (by exact_mod_cast hg.ne')]
  rw [hr'eq] at hcop

  rw [sum_zmod_eq_sum_range N]
  set h : ℕ → ℤ := fun n => F ((((p : ZMod N) + (n : ZMod N) * (r : ZMod N)).val : ℤ)) with hh
  have hper : ∀ n : ℕ, h (n + M) = h n := by
    intro n
    simp only [hh]
    congr 3
    push_cast
    have hMr : (M : ZMod N) * (r : ZMod N) = 0 := by
      rw [hr', show ((g * r' : ℤ) : ZMod N) = (g : ZMod N) * (r' : ZMod N) by push_cast; ring, ← mul_assoc,
        show (M : ZMod N) * (g : ZMod N) = ((g * M : ℕ) : ZMod N) by push_cast; ring, ← hN, ZMod.natCast_self,
        zero_mul]
    rw [add_mul, hMr, add_zero]
  rw [show range N = range (g * M) by rw [hN], sum_range_mul_of_periodic M g h hper, nsmul_eq_mul]
  congr 1

  have hp : p = g * (p / g) + p % g := (Int.mul_ediv_add_emod p g).symm
  have hval : ∀ n : ℕ, h n = F (p % g + g * ((p / g + n * r') % M)) := by
    intro n
    simp only [hh]
    rw [show ((p : ZMod N) + (n : ZMod N) * (r : ZMod N)) = ((p + n * r : ℤ) : ZMod N) by push_cast; ring,
      ZMod.val_intCast, hN]
    push_cast
    have : p + n * r = p % g + g * (p / g + n * r') := by rw [hr']; linear_combination hp
    rw [this, emod_progression _ _ _ M (Int.emod_nonneg p (by exact_mod_cast hg.ne'))
      (Int.emod_lt_of_pos p (by exact_mod_cast hg)) hM]
  rw [sum_congr rfl fun n _ => hval n]
  exact sum_range_affine_unit M hM (p / g) r' hcop (fun k => F (p % g + g * k))

theorem gcd_bookkeeping (N : ℕ) (hN : N ≠ 0) (r : ℤ) :
    ((Int.gcd r N : ℤ) ∣ r) ∧ (Int.gcd r N ∣ N) ∧ 0 < Int.gcd r N ∧
      IsCoprime (r / Int.gcd r N) ((N / Int.gcd r N : ℕ) : ℤ) := by
  set g := Int.gcd r N with hgdef
  have h1 : (g : ℤ) ∣ r := Int.gcd_dvd_left _ _
  have h2' : (g : ℤ) ∣ (N : ℤ) := Int.gcd_dvd_right _ _
  have h2 : g ∣ N := by exact_mod_cast h2'
  have hgpos : 0 < g := Int.gcd_pos_iff.mpr (Or.inr (by exact_mod_cast hN))
  refine ⟨h1, h2, hgpos, ?_⟩
  rw [Int.isCoprime_iff_gcd_eq_one]
  have hdiv : ((N / g : ℕ) : ℤ) = (N : ℤ) / g := by
    rw [Int.natCast_div]
  rw [hdiv]
  exact Int.gcd_div_gcd_div_gcd hgpos

theorem sum_zmod_Bt (N : ℕ) [NeZero N] (p r : ℤ) :
    ∑ s : ZMod N, Bt N ((((p : ZMod N) + s * (r : ZMod N)).val : ℤ)) =
      N * (6 * (p % Int.gcd r N) ^ 2 - 6 * (Int.gcd r N) * (p % Int.gcd r N) + (Int.gcd r N) ^ 2) := by
  have hN : N ≠ 0 := NeZero.ne N
  obtain ⟨hgr, hgN, hgpos, hcop⟩ := gcd_bookkeeping N hN r
  set g := Int.gcd r N with hgdef
  obtain ⟨M, hM⟩ := hgN
  have hMpos : 0 < M := Nat.pos_of_ne_zero (by rintro rfl; exact hN (by rw [hM, mul_zero]))
  have hNg : N / g = M := by rw [hM, Nat.mul_div_cancel_left _ hgpos]
  rw [hNg] at hcop
  rw [sum_zmod_comp_val_affine N g M hM hgpos hMpos p r hgr hcop (Bt N)]
  rw [show (N : ℤ) = (g : ℤ) * (M : ℤ) by rw [hM]; push_cast; ring, sum_range_Bt]
  ring

end Ws18BDist

namespace Ws18BDeg

open Ws18BDist

def J2 (n : ℕ) : ℤ := ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) • (x.2 : ℤ) ^ 2

theorem sum_divisors_J2 (n : ℕ) (hn : 0 < n) : ∑ i ∈ n.divisors, J2 i = (n : ℤ) ^ 2 :=
  (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (f := J2) (g := fun n => (n : ℤ) ^ 2)).mpr
    (fun _ _ => rfl) n hn

theorem filter_dvd_divisors (n s : ℕ) (hn : n ≠ 0) :
    n.divisors.filter (· ∣ s) = (Nat.gcd s n).divisors := by
  ext i
  simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
  constructor
  · rintro ⟨⟨hin, -⟩, his⟩
    exact ⟨⟨his, hin⟩, Nat.gcd_ne_zero_right hn⟩
  · rintro ⟨⟨his, hin⟩, -⟩
    exact ⟨⟨hin, hn⟩, his⟩

theorem sum_moebius_gcd_sq (s N : ℕ) (hN : 0 < N) (hs : ¬ N ∣ s) :
    ∑ x ∈ N.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) • (Nat.gcd s x.2 : ℤ) ^ 2 = 0 := by
  let F : ℕ → ℤ := fun n => if n ∣ s then J2 n else 0
  have key : ∀ n > 0, ∑ i ∈ n.divisors, F i = (Nat.gcd s n : ℤ) ^ 2 := by
    intro n hn
    simp only [F]
    rw [← Finset.sum_filter, filter_dvd_divisors n s hn.ne', sum_divisors_J2 _ (Nat.gcd_pos_of_pos_right _ hn)]
  have := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (f := F) (g := fun n => (Nat.gcd s n : ℤ) ^ 2)).mp
    key N hN
  rw [this]
  simp [F, hs]

theorem sum_moebius_mul_div_eq_totient (g : ℕ) (hg : 0 < g) :
    ∑ a ∈ g.divisors, (ArithmeticFunction.moebius a : ℤ) * (g / a : ℕ) = (Nat.totient g : ℤ) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq (f := fun n => (Nat.totient n : ℤ))
    (g := fun n => (n : ℤ))).mp (fun n _ => by exact_mod_cast Nat.sum_totient n) g hg
  rw [← h, Nat.sum_divisorsAntidiagonal (f := fun a b => (ArithmeticFunction.moebius a : ℤ) • (b : ℤ))]
  simp

theorem weight_eq_sum (N : ℕ) (hN : 0 < N) (r : ℕ) :
    ((N / Nat.gcd r N : ℕ) : ℤ) * (Nat.totient (Nat.gcd r N) : ℤ) =
      ∑ a ∈ N.divisors, if a ∣ r then (ArithmeticFunction.moebius a : ℤ) * (N / a : ℕ) else 0 := by
  set g := Nat.gcd r N with hgdef
  have hgN : g ∣ N := Nat.gcd_dvd_right r N
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right r hN
  obtain ⟨M, hM⟩ := hgN
  have hNg : N / g = M := by rw [hM, Nat.mul_div_cancel_left _ hgpos]
  rw [← Finset.sum_filter, filter_dvd_divisors N r hN.ne', ← hgdef, hNg, ← sum_moebius_mul_div_eq_totient g hgpos,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  obtain ⟨hag, -⟩ := Nat.mem_divisors.mp ha
  obtain ⟨b, hb⟩ := hag
  have hapos : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hb; omega)
  have h1 : g / a = b := by rw [hb, Nat.mul_div_cancel_left _ hapos]
  have h2 : N / a = M * b := by rw [hM, hb, show a * b * M = a * (M * b) by ring, Nat.mul_div_cancel_left _ hapos]
  rw [h1, h2]
  push_cast
  ring

theorem filter_dvd_range (a L : ℕ) (ha : 0 < a) :
    (Finset.range (a * L)).filter (a ∣ ·) = (Finset.range L).map ⟨(a * ·), mul_right_injective₀ ha.ne'⟩ := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map, Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hn, ⟨j, rfl⟩⟩
    exact ⟨j, Nat.lt_of_mul_lt_mul_left hn, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨Nat.mul_lt_mul_of_pos_left hj ha, dvd_mul_right a j⟩

theorem sum_zmod_ite_dvd (N a L : ℕ) [NeZero N] (hN : N = a * L) (G : ZMod N → ℤ) :
    ∑ r : ZMod N, (if a ∣ r.val then G r else 0) = ∑ j ∈ Finset.range L, G ((a * j : ℕ) : ZMod N) := by
  subst hN
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne (0 * L) (by rw [zero_mul]))
  rw [sum_zmod_eq_sum_range (a * L)]
  have h1 : ∀ n ∈ Finset.range (a * L), (if a ∣ (n : ZMod (a * L)).val then G n else 0) = if a ∣ n then G n else 0 := by
    intro n hn
    rw [ZMod.val_natCast_of_lt (Finset.mem_range.mp hn)]
  rw [Finset.sum_congr rfl h1, ← Finset.sum_filter, filter_dvd_range a L ha, Finset.sum_map]
  rfl

theorem sum_range_Bt_mul_mod (L : ℕ) (hL : 0 < L) (s : ℕ) :
    ∑ j ∈ Finset.range L, Bt L (((j * s) % L : ℕ) : ℤ) = L * (Nat.gcd s L : ℤ) ^ 2 := by
  haveI : NeZero L := ⟨hL.ne'⟩
  have h := sum_zmod_Bt L 0 s
  rw [sum_zmod_eq_sum_range L] at h
  have hg : (Int.gcd (s : ℤ) (L : ℤ) : ℤ) = (Nat.gcd s L : ℤ) := by rw [Int.gcd_natCast_natCast]
  simp only [Int.cast_zero, zero_add, Int.cast_natCast, EuclideanDomain.zero_mod, hg] at h
  rw [← Finset.sum_congr rfl (fun j hj => ?_)] at h
  · rw [h]; ring
  · congr 2
    rw [← Nat.cast_mul, ZMod.val_natCast]

theorem inner_sum (N a L : ℕ) [NeZero N] (hN : N = a * L) (s : ZMod N) :
    ∑ j ∈ Finset.range L, Bt N (((s * ((a * j : ℕ) : ZMod N)).val : ℤ)) =
      (a : ℤ) ^ 2 * (L * (Nat.gcd s.val L : ℤ) ^ 2) := by
  subst hN
  have ha : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne (0 * L) (by rw [zero_mul]))
  have hL : 0 < L := Nat.pos_of_ne_zero (by rintro rfl; exact NeZero.ne (a * 0) (by rw [mul_zero]))
  rw [← sum_range_Bt_mul_mod L hL s.val, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hval : (s * ((a * j : ℕ) : ZMod (a * L))).val = a * ((j * s.val) % L) := by
    rw [ZMod.val_mul, ZMod.val_natCast, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod,
      show s.val * (a * j) = a * (j * s.val) by ring, Nat.mul_mod_mul_left]
  rw [hval, Bt, Bt]
  push_cast
  ring

theorem sum_zmod_weight_Bt (N : ℕ) [NeZero N] (s : ZMod N) (hs : s ≠ 0) :
    ∑ r : ZMod N, (((N / Nat.gcd r.val N : ℕ) : ℤ) * (Nat.totient (Nat.gcd r.val N) : ℤ)) *
      Bt N (((s * r).val : ℤ)) = 0 := by
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)

  have hw : ∀ r : ZMod N, (((N / Nat.gcd r.val N : ℕ) : ℤ) * (Nat.totient (Nat.gcd r.val N) : ℤ)) *
      Bt N (((s * r).val : ℤ)) =
      ∑ a ∈ N.divisors, if a ∣ r.val then (ArithmeticFunction.moebius a : ℤ) * (N / a : ℕ) * Bt N (((s * r).val : ℤ)) else 0 := by
    intro r
    rw [weight_eq_sum N hN r.val, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  rw [Fintype.sum_congr _ _ hw, Finset.sum_comm]

  have hterm : ∀ a ∈ N.divisors,
      ∑ r : ZMod N, (if a ∣ r.val then (ArithmeticFunction.moebius a : ℤ) * (N / a : ℕ) * Bt N (((s * r).val : ℤ)) else 0) =
        (N : ℤ) ^ 2 * ((ArithmeticFunction.moebius a : ℤ) • (Nat.gcd s.val (N / a) : ℤ) ^ 2) := by
    intro a ha
    obtain ⟨⟨L, hL⟩, -⟩ := Nat.mem_divisors.mp ha
    have hapos : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_mul] at hL; exact (NeZero.ne N) hL)
    have hNa : N / a = L := by rw [hL, Nat.mul_div_cancel_left _ hapos]
    have h1 : ∑ r : ZMod N, (if a ∣ r.val then (ArithmeticFunction.moebius a : ℤ) * (N / a : ℕ) * Bt N (((s * r).val : ℤ)) else 0) =
        (ArithmeticFunction.moebius a : ℤ) * (N / a : ℕ) * ∑ r : ZMod N, (if a ∣ r.val then Bt N (((s * r).val : ℤ)) else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      split_ifs <;> simp
    rw [h1, sum_zmod_ite_dvd N a L hL, inner_sum N a L hL s, hNa]
    have hNz : (N : ℤ) = (a : ℤ) * (L : ℤ) := by exact_mod_cast hL
    rw [smul_eq_mul, hNz]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum,
    ← Nat.sum_divisorsAntidiagonal (f := fun a b => (ArithmeticFunction.moebius a : ℤ) • (Nat.gcd s.val b : ℤ) ^ 2),
    sum_moebius_gcd_sq s.val N hN ?_, mul_zero]

  intro hdvd
  have h0 : s.val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt s)
  exact hs ((ZMod.val_eq_zero s).mp h0)

end Ws18BDeg

open Ws18BDist Ws18BDeg in
theorem solution (N : ℕ) [NeZero N]
    (s : ZMod N) (hs : s ≠ 0) :
    ∑ r : ZMod N,
        (((N / Nat.gcd r.val N) * Nat.totient (Nat.gcd r.val N) : ℕ) : ℤ) *
          (6 * (((s * r).val : ℕ) : ℤ) ^ 2 - 6 * (N : ℤ) * (((s * r).val : ℕ) : ℤ) + (N : ℤ) ^ 2) = 0 := by
  calc _ = ∑ r : ZMod N, (((N / Nat.gcd r.val N : ℕ) : ℤ) * (Nat.totient (Nat.gcd r.val N) : ℤ)) *
        Bt N (((s * r).val : ℤ)) :=
        Finset.sum_congr rfl fun r _ => by simp only [Bt]; push_cast; ring
    _ = 0 := sum_zmod_weight_Bt N s hs

end S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero
end P2MW
export P2MW.S_ModularCurve_SiegelUnit_sum_totient_mul_levelBernoulliWeight_dilate_eq_zero (solution)
