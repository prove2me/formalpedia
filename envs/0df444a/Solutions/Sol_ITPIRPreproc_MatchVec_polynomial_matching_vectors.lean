-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.polynomial_matching_vectors
-- status  : ACCEPTED   (prove)
-- author  : @Jesko
-- created : 2026-11-13T17:16:35.660496+00:00
-- url     : https://prove2.me/submissions/e07dc67a-1462-43bb-bc60-7237862508a3

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic
import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialConstruction

set_option backward.isDefEq.respectTransparency false

open Finset Function

namespace PIRMVPolynomial

theorem difference_prime_power (p a : ℕ) [Fact p.Prime] (f : ℕ → ZMod p) :
    (fwdDiff (1 : ℕ))^[p ^ a] f = fun n => f (n + p ^ a) - f n := by
  letI : CharP (Module.End ℤ (ℕ → ZMod p)) p := by
    constructor
    intro k
    constructor
    · intro hk
      have he := congrArg (fun T : Module.End ℤ (ℕ → ZMod p) => T (fun _ => 1) 0) hk
      have hz : (k : ZMod p) = 0 := by simpa [Module.End.natCast_apply] using he
      exact (CharP.cast_eq_zero_iff (ZMod p) p k).mp hz
    · intro hk
      have hz : (k : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p k).mpr hk
      ext g n
      simp [Module.End.natCast_apply, nsmul_eq_mul, hz]
  have hd : fwdDiff_aux.fwdDiffₗ ℕ (ZMod p) 1 =
      fwdDiff_aux.shiftₗ ℕ (ZMod p) 1 - 1 := by
    simp [fwdDiff_aux.shiftₗ]
  have he := sub_pow_char_pow_of_commute p a
    (Commute.one_right (fwdDiff_aux.shiftₗ ℕ (ZMod p) 1))
  rw [← hd] at he
  ext n
  have hv := congrArg (fun T : Module.End ℤ (ℕ → ZMod p) => T f n) he
  simp only [LinearMap.sub_apply, Pi.sub_apply, one_pow, Module.End.one_apply,
    fwdDiff_aux.shiftₗ_pow_apply, nsmul_eq_mul, Nat.cast_id, mul_one] at hv
  simpa only [Module.End.pow_apply, fwdDiff_aux.coe_fwdDiffₗ] using hv

theorem difference_periodic (p a : ℕ) [Fact p.Prime] (f : ℕ → ZMod p)
    (hper : ∀ n, f (n + p ^ a) = f n) :
    (fwdDiff (1 : ℕ))^[p ^ a] f = 0 := by
  rw [difference_prime_power]
  ext n
  simp [hper]

theorem difference_periodic_ge (p a t : ℕ) [Fact p.Prime] (f : ℕ → ZMod p)
    (hper : ∀ n, f (n + p ^ a) = f n) (ht : p ^ a ≤ t) :
    (fwdDiff (1 : ℕ))^[t] f = 0 := by
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [add_comm, Function.iterate_add_apply, difference_periodic p a f hper]
  ext n
  simp [fwdDiff_iter_eq_sum_shift]

theorem periodic_newton (p a : ℕ) [Fact p.Prime] (f : ℕ → ZMod p)
    (hper : ∀ n, f (n + p ^ a) = f n) (j : ℕ) :
    f j = ∑ t ∈ range (p ^ a), (j.choose t : ZMod p) *
      (fwdDiff (1 : ℕ))^[t] f 0 := by
  have hn := shift_eq_sum_fwdDiff_iter (1 : ℕ) f j 0
  simp only [nsmul_eq_mul, Nat.cast_id, Nat.mul_one, zero_add] at hn
  rw [hn]
  rcases le_total (j + 1) (p ^ a) with hj | hj
  · apply Finset.sum_subset (Finset.range_mono hj)
    intro t ht hnot
    have hgt : j < t := by simpa using hnot
    simp [Nat.choose_eq_zero_of_lt hgt]
  · symm
    apply Finset.sum_subset (Finset.range_mono hj)
    intro t ht hnot
    have hge : p ^ a ≤ t := by simpa using hnot
    rw [difference_periodic_ge p a t f hper hge]
    simp

end PIRMVPolynomial

namespace ITPIRPreproc.MatchVec.PolynomialConstruction

theorem map_difference {G H : Type*} [Ring G] [Ring H]
    (phi : G →+* H) (f : ℕ → G) (t n : ℕ) :
    phi ((fwdDiff (1 : ℕ))^[t] f n) =
      (fwdDiff (1 : ℕ))^[t] (fun j => phi (f j)) n := by
  simp [fwdDiff_iter_eq_sum_shift, map_sum]

theorem coefficient_eq_difference (ell a b t : ℕ) :
    coefficient ell a b t = (fwdDiff (1 : ℕ))^[t] (signal ell a b) 0 := by
  simp [coefficient, fwdDiff_iter_eq_sum_shift, zsmul_eq_mul, Int.cast_mul,
    Int.cast_pow]

theorem signal_red2 (ell a b j : ℕ) :
    red2 (signal ell a b j) =
      if j % 2^a = ell % 2^a then 1 else 0 := by
  simp only [signal, map_add, map_mul]
  split_ifs <;> norm_num only [map_ofNat, map_one, map_zero, mul_one, mul_zero,
    zero_mul, add_zero, zero_add] <;> decide

theorem signal_red3 (ell a b j : ℕ) :
    red3 (signal ell a b j) =
      if j % 3^b = ell % 3^b then 1 else 0 := by
  simp only [signal, map_add, map_mul]
  split_ifs <;> norm_num only [map_ofNat, map_one, map_zero, mul_one, mul_zero,
    zero_mul, add_zero, zero_add] <;> decide

theorem red_ext (x y : ZMod 6) (h2 : red2 x = red2 y) (h3 : red3 x = red3 y) :
    x = y := by
  apply (ZMod.chineseRemainder (by norm_num : Nat.Coprime 2 3)).injective
  exact Prod.ext h2 h3

theorem coefficient_vanish (ell a b t : ℕ) (ht : max (2^a) (3^b) ≤ t) :
    coefficient ell a b t = 0 := by
  rw [coefficient_eq_difference]
  apply red_ext
  · rw [map_zero, map_difference red2]
    simp_rw [signal_red2]
    have hp : ∀ n : ℕ,
        (if (n+2^a)%2^a = ell%2^a then (1 : ZMod 2) else 0) =
        (if n%2^a = ell%2^a then 1 else 0) := by intro n; simp
    have hz := PIRMVPolynomial.difference_periodic_ge 2 a t
      (fun j => if j%2^a = ell%2^a then (1 : ZMod 2) else 0) hp
      (le_trans (le_max_left _ _) ht)
    exact congrFun hz 0
  · rw [map_zero, map_difference red3]
    simp_rw [signal_red3]
    have hp : ∀ n : ℕ,
        (if (n+3^b)%3^b = ell%3^b then (1 : ZMod 3) else 0) =
        (if n%3^b = ell%3^b then 1 else 0) := by intro n; simp
    have hz := PIRMVPolynomial.difference_periodic_ge 3 b t
      (fun j => if j%3^b = ell%3^b then (1 : ZMod 3) else 0) hp
      (le_trans (le_max_right _ _) ht)
    exact congrFun hz 0

theorem signal_newton (ell a b j : ℕ) :
    signal ell a b j = ∑ t ∈ range (degree a b + 1),
      (j.choose t : ZMod 6) * coefficient ell a b t := by
  have hn := shift_eq_sum_fwdDiff_iter (1 : ℕ) (signal ell a b) j 0
  simp only [nsmul_eq_mul, Nat.cast_id, Nat.mul_one, zero_add,
    ← coefficient_eq_difference] at hn
  rw [hn]
  rcases le_total (j+1) (degree a b+1) with hj | hj
  · apply Finset.sum_subset (Finset.range_mono hj)
    intro t ht hnot
    have hgt : j < t := by simpa using hnot
    simp [Nat.choose_eq_zero_of_lt hgt]
  · symm
    apply Finset.sum_subset (Finset.range_mono hj)
    intro t ht hnot
    have hge : max (2^a) (3^b) ≤ t := by
      have : degree a b + 1 ≤ t := by simpa using hnot
      dsimp [degree] at this
      omega
    rw [coefficient_vanish ell a b t hge]
    simp

theorem signal_diagonal (ell a b : ℕ) : signal ell a b ell = 1 := by
  simp only [signal, if_true, mul_one]
  decide

theorem signal_offdiagonal (ell a b j : ℕ) (hj : j < ell)
    (hsize : ell < 2^a * 3^b) :
    red2 (signal ell a b j) = 0 ∨ red3 (signal ell a b j) = 0 := by
  rw [signal_red2, signal_red3]
  by_cases h2 : j % 2^a = ell % 2^a
  · right
    have h3 : ¬ j % 3^b = ell % 3^b := by
      intro h3
      have hd2 : 2^a ∣ ell-j := (Nat.modEq_iff_dvd' hj.le).mp h2
      have hd3 : 3^b ∣ ell-j := (Nat.modEq_iff_dvd' hj.le).mp h3
      have hcop : Nat.Coprime (2^a) (3^b) := (by norm_num : Nat.Coprime 2 3).pow a b
      have hd : 2^a * 3^b ∣ ell-j := hcop.mul_dvd_of_dvd_of_dvd hd2 hd3
      have := Nat.le_of_dvd (by omega : 0 < ell-j) hd
      omega
    simp [h3]
  · left
    simp [h2]

end ITPIRPreproc.MatchVec.PolynomialConstruction


set_option backward.isDefEq.respectTransparency false
open Finset Function

namespace ITPIRPreproc.MatchVec.PolynomialConstruction

theorem restriction_eq_iff {ell : ℕ} (sigma tau : Fin ell → Fin ell)
    (I : Finset (Fin ell)) :
    restriction sigma I = restriction tau I ↔ I ⊆ agreement sigma tau := by
  constructor
  · intro h j hj
    simp only [agreement, mem_filter, mem_univ, true_and]
    exact congrFun h ⟨j, hj⟩
  · intro h
    funext j
    exact (mem_filter.mp (h j.property)).2

theorem vector_inner_product {ell k : ℕ} (c : ℕ → ZMod 6)
    (sigma tau : Fin ell → Fin ell) :
    (∑ z : Coordinate ell k, leftVector c sigma z * rightVector tau z) =
      ∑ I ∈ (agreement sigma tau).powerset.filter (fun I => I.card ≤ k), c I.card := by
  classical
  rw [Fintype.sum_sigma]
  simp only [leftVector, rightVector, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp_rw [restriction_eq_iff]
  rw [← Finset.sum_subtype (univ.filter fun I : Finset (Fin ell) => I.card ≤ k)
    (by simp) (fun I : Finset (Fin ell) => if I ⊆ agreement sigma tau then c I.card else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext I
  simp [and_comm]

theorem subset_sum_newton {R : Type*} [CommSemiring R]
    {ell k : ℕ} (S : Finset (Fin ell)) (c : ℕ → R) :
    (∑ I ∈ S.powerset.filter (fun I => I.card ≤ k), c I.card) =
      ∑ t ∈ range (k+1), (S.card.choose t : R) * c t := by
  rw [Finset.sum_filter, Finset.sum_powerset]
  have hs (j : ℕ) := Finset.sum_powersetCard j S (fun t => if t ≤ k then c t else 0)
  simp_rw [hs]
  simp only [nsmul_eq_mul, mul_ite, mul_zero]
  change (∑ t ∈ range (S.card+1), if t ≤ k then (S.card.choose t : R)*c t else 0) = _
  rcases le_total (S.card+1) (k+1) with h | h
  · calc
      _ = ∑ t ∈ range (S.card+1), (S.card.choose t : R)*c t := by
        apply sum_congr rfl
        intro t ht
        have := mem_range.mp ht
        simp [show t ≤ k by omega]
      _ = _ := Finset.sum_subset (Finset.range_mono h) (by
        intro t ht hnot
        have hgt : S.card < t := by simpa using hnot
        simp [Nat.choose_eq_zero_of_lt hgt])
  · symm
    calc
      _ = ∑ t ∈ range (k+1), if t ≤ k then (S.card.choose t : R)*c t else 0 := by
        apply sum_congr rfl
        intro t ht
        simp [show t ≤ k from Nat.le_of_lt_succ (mem_range.mp ht)]
      _ = _ := Finset.sum_subset (Finset.range_mono h) (by
        intro t ht hnot
        have hgt : k < t := by simpa using hnot
        simp [Nat.not_le.mpr hgt])

theorem rightVector_injective_mod2 {ell k : ℕ} (hk : 1 ≤ k) :
    Function.Injective (fun sigma : Fin ell → Fin ell =>
      fun z : Coordinate ell k => red2 (rightVector sigma z)) := by
  classical
  intro sigma tau h
  funext j
  let I : Subsets ell k := ⟨{j}, by simpa using hk⟩
  let z : Coordinate ell k := ⟨I, restriction sigma I.val⟩
  have hz := congrFun h z
  change red2 (rightVector sigma z) = red2 (rightVector tau z) at hz
  have hs : rightVector sigma z = 1 := by simp [rightVector, z]
  rw [hs, map_one] at hz
  have ht : restriction tau I.val = restriction sigma I.val := by
    by_contra hn
    have hv : rightVector tau z = 0 := by simp [rightVector, z, hn]
    rw [hv, map_zero] at hz
    exact one_ne_zero hz
  exact (congrFun ht ⟨j, by simp [I]⟩).symm

theorem agreement_self {ell : ℕ} (sigma : Fin ell → Fin ell) :
    (agreement sigma sigma).card = ell := by simp [agreement]

theorem agreement_lt {ell : ℕ} {sigma tau : Fin ell → Fin ell} (h : sigma ≠ tau) :
    (agreement sigma tau).card < ell := by
  have hsub : agreement sigma tau ⊂ (univ : Finset (Fin ell)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨subset_univ _, ?_⟩
    intro he
    apply h
    funext j
    have hj : j ∈ agreement sigma tau := by rw [he]; exact mem_univ _
    exact (mem_filter.mp hj).2
  simpa using Finset.card_lt_card hsub

theorem coordinate_card (ell k : ℕ) :
    Fintype.card (Coordinate ell k) = ∑ t ∈ range (k+1), ell.choose t * ell^t := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
  rw [← Finset.sum_subtype (univ.filter fun I : Finset (Fin ell) => I.card ≤ k)
    (by simp) (fun I : Finset (Fin ell) => ell^I.card)]
  have hs := subset_sum_newton (k := k) (univ : Finset (Fin ell)) (fun t => ell^t)
  simpa using hs

theorem coordinate_card_bound (ell k : ℕ) (hell : 1 ≤ ell) :
    Fintype.card (Coordinate ell k) ≤ (k+1) * ell^(2*k) := by
  rw [coordinate_card]
  calc
    _ ≤ ∑ t ∈ range (k+1), ell^(2*k) := by
      apply sum_le_sum
      intro t ht
      have ht' : t ≤ k := Nat.le_of_lt_succ (mem_range.mp ht)
      calc
        ell.choose t * ell^t ≤ ell^t * ell^t := Nat.mul_le_mul_right _ (Nat.choose_le_pow ell t)
        _ = ell^(2*t) := by rw [← pow_add]; congr 1; omega
        _ ≤ ell^(2*k) := Nat.pow_le_pow_right hell (by omega)
    _ = _ := by simp

theorem polynomial_matching_family (ell a b m d : ℕ)
    (hk : 1 ≤ degree a b) (hsize : ell < 2^a * 3^b)
    (rows : Fin m ↪ (Fin ell → Fin ell))
    (coords : Fin d ≃ Coordinate ell (degree a b)) :
    IsMVFamily m d
      (fun r j => leftVector (coefficient ell a b) (rows r) (coords j))
      (fun r j => rightVector (rows r) (coords j)) := by
  classical
  have hip (r s : Fin m) :
      (fun j => leftVector (coefficient ell a b) (rows r) (coords j)) ⬝ᵥ
        (fun j => rightVector (rows s) (coords j)) =
      signal ell a b (agreement (rows r) (rows s)).card := by
    change (∑ j, leftVector (coefficient ell a b) (rows r) (coords j) *
      rightVector (rows s) (coords j)) = _
    rw [coords.sum_comp (fun z => leftVector (coefficient ell a b) (rows r) z *
      rightVector (rows s) z)]
    rw [vector_inner_product, subset_sum_newton, ← signal_newton]
  constructor
  · intro r
    rw [hip, agreement_self, signal_diagonal]
  · intro r s hrs
    rw [hip]
    apply signal_offdiagonal ell a b _ _ hsize
    apply agreement_lt
    intro he
    exact hrs (rows.injective he).symm
  · intro r s hrs
    apply rows.injective
    apply rightVector_injective_mod2 hk
    funext z
    obtain ⟨j, rfl⟩ := coords.surjective z
    exact congrFun hrs j

end ITPIRPreproc.MatchVec.PolynomialConstruction
open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction
open Finset
theorem solution (ell a b m d : ℕ)
    (hk : 1 ≤ degree a b) (hsize : ell < 2^a * 3^b)
    (rows : Fin m ↪ (Fin ell → Fin ell))
    (coords : Fin d ≃ Coordinate ell (degree a b)) :
    IsMVFamily m d
      (fun r j => leftVector (coefficient ell a b) (rows r) (coords j))
      (fun r j => rightVector (rows r) (coords j)) ∧
    d = ∑ t ∈ range (degree a b + 1), ell.choose t * ell^t ∧
    (1 ≤ ell → d ≤ (degree a b + 1) * ell^(2 * degree a b)) := by
  refine ⟨polynomial_matching_family ell a b m d hk hsize rows coords, ?_, ?_⟩
  · calc
      d = Fintype.card (Coordinate ell (degree a b)) := by
        simpa using Fintype.card_congr coords
      _ = _ := coordinate_card ell (degree a b)
  · intro hell
    have hd : d = Fintype.card (Coordinate ell (degree a b)) := by
      simpa using Fintype.card_congr coords
    rw [hd]
    exact coordinate_card_bound ell (degree a b) hell
