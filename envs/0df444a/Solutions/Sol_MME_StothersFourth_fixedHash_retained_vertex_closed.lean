-- Prove2me | solution 1 for MME.StothersFourth.fixedHash_retained_vertex_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T21:49:36.133034+00:00
-- url     : https://prove2.me/submissions/4ad13144-14a7-4090-a47e-a4d13c33d422

import Definitions.Def_mme_stothers_fixed_affine_hash
import Theorems.Thm_mme_threeAP_free_half_modulus_no_collision

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000


namespace MME.StothersFourth


/-- The three doubled `d = 8` hashes form an arithmetic progression on every
coordinatewise-supported mixed edge. -/
private theorem fixedHash_doubled_AP_identity
    {R : Type} [CommSemiring R] {m : ℕ}
    (b0 : R) (w : Fin (fixedOuterLength m) → R)
    (x y z : FixedOuterAddress m)
    (hsupp : FixedCoordinatewiseSupported (fixedMixedAddress x y z)) :
    fixedHashDoubledX w (x 0) + fixedHashDoubledY b0 w (y 1) =
      2 * fixedHashDoubledZ b0 w (z 2) := by
  simp only [fixedHashDoubledX, fixedHashDoubledY, fixedHashDoubledZ]
  have hsum :
      (∑ k, (((2 * (x 0 k).val : ℕ) : R) * w k)) +
          (∑ k, (((2 * (y 1 k).val : ℕ) : R) * w k)) =
        2 * ∑ k, (((8 - (z 2 k).val : ℕ) : R) * w k) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    have hk : (x 0 k).val + (y 1 k).val + (z 2 k).val = 8 := by
      simpa [fixedMixedAddress, Fin.sum_univ_succ, add_assoc] using hsupp k
    have hxy :
        (x 0 k).val + (y 1 k).val = 8 - (z 2 k).val := by
      omega
    have hxyR :
        ((x 0 k).val : R) + ((y 1 k).val : R) =
          ((8 - (z 2 k).val : ℕ) : R) := by
      rw [← Nat.cast_add]
      exact congrArg (fun n : ℕ ↦ (n : R)) hxy
    push_cast
    calc
      2 * ((x 0 k).val : R) * w k +
          2 * ((y 1 k).val : R) * w k =
          2 * (((x 0 k).val : R) + ((y 1 k).val : R)) * w k := by
            ring
      _ = 2 * (((8 - (z 2 k).val : ℕ) : R) * w k) := by
            rw [hxyR]
            ring
  calc
    (∑ k, (((2 * (x 0 k).val : ℕ) : R) * w k)) +
          (2 * b0 + ∑ k, (((2 * (y 1 k).val : ℕ) : R) * w k)) =
        2 * b0 +
          ((∑ k, (((2 * (x 0 k).val : ℕ) : R) * w k)) +
            ∑ k, (((2 * (y 1 k).val : ℕ) : R) * w k)) := by
      ac_rfl
    _ = 2 * b0 +
        2 * ∑ k, (((8 - (z 2 k).val : ℕ) : R) * w k) := by
      rw [hsum]
    _ = 2 *
        (b0 + ∑ k, (((8 - (z 2 k).val : ℕ) : R) * w k)) := by
      ring

/-- Odd moduli turn the doubled identity into the ordinary modular
arithmetic-progression identity. -/
private theorem fixedHash_modular_AP_identity
    {M m : ℕ} (hM : Odd M)
    (b0 : ZMod M) (w : Fin (fixedOuterLength m) → ZMod M)
    (x y z : FixedOuterAddress m)
    (hsupp : FixedCoordinatewiseSupported (fixedMixedAddress x y z)) :
    fixedHashXMod w (x 0) + fixedHashYMod b0 w (y 1) =
      2 * fixedHashZMod b0 w (z 2) := by
  have hunit : IsUnit (2 : ZMod M) :=
    (ZMod.isUnit_iff_coprime 2 M).2 hM.coprime_two_left
  have hAP := fixedHash_doubled_AP_identity b0 w x y z hsupp
  simp only [fixedHashXMod, fixedHashYMod, fixedHashZMod]
  calc
    (2 : ZMod M)⁻¹ * fixedHashDoubledX w (x 0) +
          (2 : ZMod M)⁻¹ * fixedHashDoubledY b0 w (y 1) =
        (2 : ZMod M)⁻¹ *
          (fixedHashDoubledX w (x 0) +
            fixedHashDoubledY b0 w (y 1)) := by ring
    _ = (2 : ZMod M)⁻¹ *
        (2 * fixedHashDoubledZ b0 w (z 2)) := by rw [hAP]
    _ = fixedHashDoubledZ b0 w (z 2) := by
      rw [← mul_assoc, ZMod.inv_mul_of_unit (2 : ZMod M) hunit, one_mul]
    _ = 2 * ((2 : ZMod M)⁻¹ *
        fixedHashDoubledZ b0 w (z 2)) := by
      rw [← mul_assoc, ZMod.mul_inv_of_unit (2 : ZMod M) hunit, one_mul]

/-- Linear-affine normal forms for the first two hashes. -/
private theorem fixedHash_XY_normal_forms
    {p N : ℕ} (hpodd : Odd p)
    (b0 : ZMod p) (w : Fin N → ZMod p)
    (x y : Fin N → Fin 9) :
    fixedHashXMod w x = ∑ k, ((x k).val : ZMod p) * w k ∧
      fixedHashYMod b0 w y =
        b0 + ∑ k, ((y k).val : ZMod p) * w k := by
  have hunit : IsUnit (2 : ZMod p) :=
    (ZMod.isUnit_iff_coprime 2 p).2 hpodd.coprime_two_left
  have htwo : (2 : ZMod p)⁻¹ * 2 = 1 :=
    ZMod.inv_mul_of_unit 2 hunit
  constructor
  · simp only [fixedHashXMod, fixedHashDoubledX]
    rw [show (∑ k, ((2 * (x k).val : ℕ) : ZMod p) * w k) =
        2 * ∑ k, ((x k).val : ZMod p) * w k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring]
    rw [← mul_assoc, htwo, one_mul]
  · simp only [fixedHashYMod, fixedHashDoubledY]
    rw [show (∑ k, ((2 * (y k).val : ℕ) : ZMod p) * w k) =
        2 * ∑ k, ((y k).val : ZMod p) * w k by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      push_cast
      ring]
    calc
      (2 : ZMod p)⁻¹ * (2 * b0 + 2 *
          ∑ k, ((y k).val : ZMod p) * w k) =
          ((2 : ZMod p)⁻¹ * 2) *
            (b0 + ∑ k, ((y k).val : ZMod p) * w k) := by ring
      _ = b0 + ∑ k, ((y k).val : ZMod p) * w k := by
        rw [htwo, one_mul]

/-- Two distinct mode words determine an address in the grade-sum-eight
support. -/
private theorem fixedHash_supported_two_modes_determine_address
    {m : ℕ} {a b : FixedOuterAddress m}
    (ha : FixedCoordinatewiseSupported a)
    (hb : FixedCoordinatewiseSupported b)
    {i k : Fin 3} (hik : i ≠ k)
    (hi : a i = b i) (hk : a k = b k) :
    a = b := by
  funext r j
  have hi_j : a i j = b i j := congrFun hi j
  have hk_j : a k j = b k j := congrFun hk j
  by_cases hri : r = i
  · simpa only [hri] using hi_j
  by_cases hrk : r = k
  · simpa only [hrk] using hk_j
  apply Fin.ext
  have hi_val : (a i j).val = (b i j).val := congrArg Fin.val hi_j
  have hk_val : (a k j).val = (b k j).val := congrArg Fin.val hk_j
  have ha_j : (a 0 j).val + (a 1 j).val + (a 2 j).val = 8 := by
    simpa [Fin.sum_univ_succ, add_assoc] using ha j
  have hb_j : (b 0 j).val + (b 1 j).val + (b 2 j).val = 8 := by
    simpa [Fin.sum_univ_succ, add_assoc] using hb j
  fin_cases i <;> fin_cases k <;> fin_cases r <;>
    simp_all <;> omega

/-- Every positive-scale fixed marginal word contains grade one. -/
private theorem fixedHash_marginal_address_has_grade_one
    (m : ℕ) (hm : 0 < m)
    (a : FixedMarginalSupportedAddress m) (i : Fin 3) :
    ∃ k : Fin (fixedOuterLength m), a.1 i k = (1 : Fin 9) := by
  have hcard := a.2.2 i (1 : Fin 9)
  have hpos : 0 < (Finset.univ.filter
      (fun k ↦ a.1 i k = (1 : Fin 9))).card := by
    rw [hcard]
    exact Nat.mul_pos hm (by norm_num [fixedMarginalBaseCount])
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  exact ⟨k, (Finset.mem_filter.mp hk).2⟩

/-- Distinct nine-grade words have a nonzero coordinate difference modulo
every modulus at least nine. -/
private theorem fixedHash_Fin9_word_difference_nonzero
    {p N : ℕ} (hp : 9 ≤ p)
    (x y : Fin (N + 1) → Fin 9) (hxy : x ≠ y) :
    ∃ k : Fin (N + 1),
      ((x k).val : ZMod p) - ((y k).val : ZMod p) ≠ 0 := by
  have hcoord : ∃ k : Fin (N + 1), x k ≠ y k := by
    by_contra h
    push Not at h
    exact hxy (funext h)
  obtain ⟨k, hk⟩ := hcoord
  refine ⟨k, ?_⟩
  intro hzero
  have hcast : ((x k).val : ZMod p) = ((y k).val : ZMod p) :=
    sub_eq_zero.mp hzero
  rw [ZMod.natCast_eq_natCast_iff'] at hcast
  have hxlt : (x k).val < p := lt_of_lt_of_le (x k).isLt hp
  have hylt : (y k).val < p := lt_of_lt_of_le (y k).isLt hp
  rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hcast
  exact hk (Fin.ext hcast)

/- The retained full marginal hypergraph is vertex-closed. -/
end MME.StothersFourth

open MME.StothersFourth

theorem solution
    (m p : ℕ) (S : Finset ℕ) (b0 : ZMod p)
    (w : Fin (fixedOuterLength m) → ZMod p)
    (hpodd : Odd p)
    (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) :
    FixedMarginalVertexClosed (fixedHashRetainedEdges m p S b0 w) := by
  classical
  intro x hx y hy z hz hsupp
  simp only [fixedHashRetainedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and] at hx hy hz
  obtain ⟨sx, hsx, hxx, _, _⟩ := hx
  obtain ⟨sy, hsy, _, hyy, _⟩ := hy
  obtain ⟨sz, hsz, _, _, hzz⟩ := hz
  have hap := fixedHash_modular_AP_identity hpodd b0 w
    x.1 y.1 z.1 hsupp
  rw [hxx, hyy, hzz] at hap
  obtain ⟨hxs, hsy'⟩ :=
    mme_threeAP_free_half_modulus_no_collision p S hSrange hSfree
      sx sz sy hsx hsz hsy hap
  have hregular : FixedMarginallyRegular
      (fixedMixedAddress x.1 y.1 z.1) := by
    intro i r
    fin_cases i
    · exact x.2.2 (0 : Fin 3) r
    · exact y.2.2 (1 : Fin 3) r
    · exact z.2.2 (2 : Fin 3) r
  let e : FixedMarginalSupportedAddress m :=
    ⟨fixedMixedAddress x.1 y.1 z.1, hsupp, hregular⟩
  refine ⟨e, ?_, rfl⟩
  simp only [fixedHashRetainedEdges, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine ⟨sz, hsz, ?_, ?_, ?_⟩
  · calc
      fixedHashXMod w (e.1 0) = fixedHashXMod w (x.1 0) := by rfl
      _ = (sx : ZMod p) := hxx
      _ = (sz : ZMod p) := congrArg (fun n : ℕ ↦ (n : ZMod p)) hxs
  · calc
      fixedHashYMod b0 w (e.1 1) = fixedHashYMod b0 w (y.1 1) := by rfl
      _ = (sy : ZMod p) := hyy
      _ = (sz : ZMod p) :=
        congrArg (fun n : ℕ ↦ (n : ZMod p)) hsy'.symm
  · exact hzz
