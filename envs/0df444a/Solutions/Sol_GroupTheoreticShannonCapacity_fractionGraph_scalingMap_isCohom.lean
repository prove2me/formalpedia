-- Prove2me | solution 1 for GroupTheoreticShannonCapacity.fractionGraph_scalingMap_isCohom
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:37:32.409827+00:00
-- url     : https://prove2.me/submissions/a3c94ea8-68ba-4596-af7d-f036c5719adb

import Definitions.Def_GroupTheoreticShannonCapacity_Basic
import Definitions.Def_GroupTheoreticShannonCapacity_FractionGraphs
section
namespace GroupTheoreticShannonCapacity
open Matrix
private lemma div_sub_le (a c x y : ℕ) (_ha : 0 < a) (hle : y ≤ x) :
    (x - y) * c / a ≤ x * c / a - y * c / a := by
  have hsum : (x - y) * c + y * c = x * c := by rw [← Nat.add_mul, Nat.sub_add_cancel hle]
  have hdiv := Nat.add_div_le_add_div ((x - y) * c) (y * c) a
  rw [hsum] at hdiv
  have hmono : y * c / a ≤ x * c / a := Nat.div_le_div_right (Nat.mul_le_mul_right c hle)
  omega
private lemma sub_mul_div_le (a b c d : ℕ) (ha : 0 < a) (had_le_bc : a * d ≤ b * c) :
    (a - b) * c / a ≤ c - d := by
  have h1 : (a - b) * c ≤ a * c - a * d := by
    rw [Nat.sub_mul]; exact Nat.sub_le_sub_left had_le_bc _
  have h2 : a * c - a * d = a * (c - d) := (Nat.mul_sub a c d).symm
  calc (a - b) * c / a ≤ (a * (c - d)) / a := Nat.div_le_div_right (h1.trans_eq h2)
    _ = c - d := Nat.mul_div_cancel_left (c - d) ha
private lemma div_add_one_le_of_rem_pos (a b c d k : ℕ) (ha : 0 < a) (hc : 0 < c)
    (had_le_bc : a * d ≤ b * c) (hk_le : k ≤ a - b) (hrem_pos : 0 < k * c % a) :
    k * c / a + 1 ≤ c - d := by
  by_cases hk_lt : k < a - b
  · -- k < a - b case
    have h5 : k * c < (a - b) * c := Nat.mul_lt_mul_of_pos_right hk_lt hc
    have h6 : k * c / a ≤ (a - b) * c / a := Nat.div_le_div_right (le_of_lt h5)
    by_cases heq : k * c / a = (a - b) * c / a
    · -- Same quotient: (a-b)*c % a > k*c % a ≥ 1, so (a-b)*c/a < c-d
      have hab_rem_pos : 0 < (a - b) * c % a := by
        have hmod_lt : k * c % a < (a - b) * c % a := by
          have h7 : k * c = a * (k * c / a) + k * c % a := (Nat.div_add_mod _ a).symm
          have h8 : (a - b) * c = a * ((a - b) * c / a) + (a - b) * c % a :=
            (Nat.div_add_mod _ a).symm
          rw [heq.symm] at h8; omega
        omega
      have hab_strict : (a - b) * c / a < c - d := by
        have h12 : (a - b) * c ≤ a * (c - d) := by
          have : (a - b) * c ≤ a * c - a * d := by
            rw [Nat.sub_mul]; exact Nat.sub_le_sub_left had_le_bc _
          calc (a - b) * c ≤ a * c - a * d := this
            _ = a * (c - d) := (Nat.mul_sub a c d).symm
        have h22 : (a - b) * c = a * ((a - b) * c / a) + (a - b) * c % a :=
          (Nat.div_add_mod _ a).symm
        have h23 : a * ((a - b) * c / a) < a * (c - d) := by omega
        exact Nat.lt_of_mul_lt_mul_left h23
      omega
    · -- Different quotient: k*c/a < (a-b)*c/a ≤ c-d
      have h7 : k * c / a < (a - b) * c / a := Nat.lt_of_le_of_ne h6 heq
      have hab_le := sub_mul_div_le a b c d ha had_le_bc
      omega
  · -- k = a - b case
    push_neg at hk_lt
    have hk_eq : k = a - b := Nat.le_antisymm hk_le hk_lt
    rw [hk_eq] at hrem_pos ⊢
    have hab_strict : (a - b) * c / a < c - d := by
      have h19 : (a - b) * c ≤ a * (c - d) := by
        have : (a - b) * c ≤ a * c - a * d := by
          rw [Nat.sub_mul]; exact Nat.sub_le_sub_left had_le_bc _
        calc (a - b) * c ≤ a * c - a * d := this
          _ = a * (c - d) := (Nat.mul_sub a c d).symm
      have h22 : (a - b) * c = a * ((a - b) * c / a) + (a - b) * c % a :=
        (Nat.div_add_mod _ a).symm
      have h23 : a * ((a - b) * c / a) < a * (c - d) := by omega
      exact Nat.lt_of_mul_lt_mul_left h23
    omega
end GroupTheoreticShannonCapacity
end

set_option autoImplicit true
open GroupTheoreticShannonCapacity
open Matrix
namespace GroupTheoreticShannonCapacity
theorem _root_.solution (a b c d : ℕ) [NeZero a] [NeZero c]
    (hb_pos : 0 < b) (hab_le_cd : (a : ℚ) / b ≤ (c : ℚ) / d) :
    ∀ u v, u ≠ v → ¬(fractionGraph a b).Adj u v →
      fractionGraph_scalingMap a c u ≠ fractionGraph_scalingMap a c v ∧
      ¬(fractionGraph c d).Adj (fractionGraph_scalingMap a c u)
        (fractionGraph_scalingMap a c v) := by
  have ha_pos : 0 < a := NeZero.pos a
  have hc_pos : 0 < c := NeZero.pos c
  -- Key inequality from a/b ≤ c/d: a * d ≤ b * c
  have had_le_bc : a * d ≤ b * c := by
    by_cases hd : d = 0
    · simp only [hd, Nat.cast_zero, div_zero] at hab_le_cd
      have hpos : 0 < (a : ℚ) / b := by positivity
      linarith
    · have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
      rw [div_le_div_iff₀ (by positivity : (0:ℚ) < b) (by positivity : (0:ℚ) < d)] at hab_le_cd
      have := (mod_cast hab_le_cd : a * d ≤ c * b); linarith
  -- Key: x.val * c / a < c for any x : ZMod a
  have hf_lt : ∀ x : ZMod a, x.val * c / a < c := fun x =>
    calc x.val * c / a < (a * c) / a :=
        Nat.div_lt_div_of_lt_of_dvd (dvd_mul_right a c)
          (Nat.mul_lt_mul_of_pos_right x.val_lt hc_pos)
      _ = c := Nat.mul_div_cancel_left c ha_pos
  let f := fractionGraph_scalingMap a c
  have hf_val : ∀ x : ZMod a, (f x).val = x.val * c / a := fun x =>
    ZMod.val_cast_of_lt (hf_lt x)
  intro u v huv hnadj
  simp only [fractionGraph, not_and, not_lt] at hnadj
  have hdist_ge_b : distMod a u v ≥ b := hnadj huv
  constructor
  · -- Part 1: f u ≠ f v (injectivity on non-adjacent pairs)
    intro hfeq
    have hval_eq : u.val * c / a = v.val * c / a := by
      rw [← hf_val u, ← hf_val v]; exact congrArg ZMod.val hfeq
    by_cases hd : d = 0
    · simp only [hd, Nat.cast_zero, div_zero] at hab_le_cd
      have hpos : 0 < (a : ℚ) / b := by positivity
      linarith
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    have ha_le_bc : a ≤ b * c := calc a = a * 1 := (Nat.mul_one a).symm
      _ ≤ a * d := Nat.mul_le_mul_left a hd_pos
      _ ≤ b * c := had_le_bc
    -- If f(u) = f(v), they're in same bucket, so |u.val - v.val| * c < a
    -- Since a ≤ bc, |u.val - v.val| < b, contradicting distMod ≥ b
    -- Case split on u.val vs v.val ordering
    rcases le_or_gt u.val v.val with huv_val | huv_val
    · -- Case u.val ≤ v.val
      have hdiff_lt : (v.val - u.val) * c < a := by
        by_contra hge; push_neg at hge
        have hvc : u.val * c + a ≤ v.val * c := by
          have : (v.val - u.val) * c = v.val * c - u.val * c := Nat.sub_mul v.val u.val c; omega
        have hdiv : u.val * c / a < v.val * c / a := by
          have h1 : u.val * c / a + 1 = (u.val * c + a) / a :=
            (Nat.add_div_right (u.val * c) ha_pos).symm
          have h2 : (u.val * c + a) / a ≤ v.val * c / a := Nat.div_le_div_right hvc
          omega
        omega
      have hdiff_lt_b : v.val - u.val < b := by
        by_contra hge; push_neg at hge
        have : b * c ≤ (v.val - u.val) * c := Nat.mul_le_mul_right c hge; omega
      have hdist : distMod a u v ≤ v.val - u.val := by
        simp only [distMod]
        by_cases heq : u.val = v.val
        · exact absurd (ZMod.val_injective a heq) huv
        have hlt : u.val < v.val := lt_of_le_of_ne huv_val heq
        have hsub : (u - v).val = a - (v.val - u.val) := by
          have heq' : u - v = -(v - u) := by ring
          rw [heq', ZMod.neg_val, if_neg (sub_ne_zero.mpr huv.symm)]
          congr 1
          conv_lhs => rw [← ZMod.natCast_zmod_val v, ← ZMod.natCast_zmod_val u]
          rw [ZMod.val_sub (by simp only [ZMod.val_natCast_of_lt u.val_lt,
            ZMod.val_natCast_of_lt v.val_lt]; exact le_of_lt hlt)]
          simp only [ZMod.val_natCast_of_lt v.val_lt, ZMod.val_natCast_of_lt u.val_lt]
        rw [hsub]; apply min_le_of_right_le; omega
      exact absurd hdist_ge_b (not_le.mpr (lt_of_le_of_lt hdist hdiff_lt_b))
    · -- Case v.val < u.val (symmetric)
      have hdiff_lt : (u.val - v.val) * c < a := by
        by_contra hge; push_neg at hge
        have huc : v.val * c + a ≤ u.val * c := by
          have : (u.val - v.val) * c = u.val * c - v.val * c := Nat.sub_mul u.val v.val c; omega
        have hdiv : v.val * c / a < u.val * c / a := by
          have h1 : v.val * c / a + 1 = (v.val * c + a) / a :=
            (Nat.add_div_right (v.val * c) ha_pos).symm
          have h2 : (v.val * c + a) / a ≤ u.val * c / a := Nat.div_le_div_right huc
          omega
        omega
      have hdiff_lt_b : u.val - v.val < b := by
        by_contra hge; push_neg at hge
        have : b * c ≤ (u.val - v.val) * c := Nat.mul_le_mul_right c hge; omega
      have hdist : distMod a u v ≤ u.val - v.val := by
        simp only [distMod]
        have hsub : (u - v).val = u.val - v.val := by
          have hle : v.val ≤ u.val := le_of_lt huv_val
          conv_lhs => rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v]
          rw [ZMod.val_sub (by simp only [ZMod.val_natCast_of_lt v.val_lt,
            ZMod.val_natCast_of_lt u.val_lt]; exact hle)]
          simp only [ZMod.val_natCast_of_lt u.val_lt, ZMod.val_natCast_of_lt v.val_lt]
        rw [hsub]; apply min_le_of_left_le; exact le_refl _
      exact absurd hdist_ge_b (not_le.mpr (lt_of_le_of_lt hdist hdiff_lt_b))
  · -- Part 2: distMod c (f u) (f v) ≥ d (non-adjacency preserved)
    simp only [fractionGraph, not_and, not_lt]
    intro _
    by_cases hd : d = 0
    · simp [hd]
    have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
    -- Use wlog to assume v.val ≤ u.val; the other case follows by symmetry of distMod
    rename_i hfuv_ne
    wlog hvu : v.val ≤ u.val generalizing u v with Hsym
    · have hdist_sym : distMod a v u ≥ b := distMod_comm a u v ▸ hdist_ge_b
      have := Hsym v u huv.symm (fun h => distMod_comm a u v ▸ hnadj h.symm) hdist_sym
        hfuv_ne.symm (le_of_not_ge hvu)
      rwa [distMod_comm c (f v) (f u)] at this
    -- Now we have v.val ≤ u.val, so δ = (u - v).val = u.val - v.val
    have hvu' : (v.val : ZMod a).val ≤ (u.val : ZMod a).val := by
      simp only [ZMod.val_natCast_of_lt v.val_lt, ZMod.val_natCast_of_lt u.val_lt]; exact hvu
    have hδ_eq : (u - v).val = u.val - v.val := by
      conv_lhs => rw [← ZMod.natCast_zmod_val u, ← ZMod.natCast_zmod_val v]
      rw [ZMod.val_sub hvu']
      simp only [ZMod.val_natCast_of_lt u.val_lt, ZMod.val_natCast_of_lt v.val_lt]
    let δ := u.val - v.val
    have hδ_bounds : b ≤ δ ∧ δ ≤ a - b := by
      have hdm := hdist_ge_b; simp only [distMod, hδ_eq] at hdm
      have hmin := le_min_iff.mp hdm
      exact ⟨hmin.1, by omega⟩
    have hδca_ge_d : d ≤ δ * c / a := by
      rw [Nat.le_div_iff_mul_le ha_pos]
      calc d * a = a * d := Nat.mul_comm d a
        _ ≤ b * c := had_le_bc
        _ ≤ δ * c := Nat.mul_le_mul_right c hδ_bounds.1
    have hf_mono : (f u).val ≥ (f v).val := by
      simp only [hf_val]; exact Nat.div_le_div_right (Nat.mul_le_mul_right c hvu)
    have hfuv_val : (f u - f v).val = (f u).val - (f v).val := ZMod.val_sub hf_mono
    simp only [distMod]
    apply le_min
    · -- d ≤ (f u - f v).val
      rw [hfuv_val, hf_val, hf_val]
      calc d ≤ δ * c / a := hδca_ge_d
        _ ≤ u.val * c / a - v.val * c / a := div_sub_le a c u.val v.val ha_pos hvu
    · -- d ≤ c - (f u - f v).val
      rw [hfuv_val, hf_val, hf_val]
      have hf_u_lt : u.val * c / a < c := hf_lt u
      have hf_v_lt : v.val * c / a < c := hf_lt v
      have hb_le_a : b ≤ a := by
        have := hδ_bounds; omega
      have hd_le_c : d ≤ c := by
        have h1 : a * d ≤ a * c := calc a * d ≤ b * c := had_le_bc
          _ ≤ a * c := Nat.mul_le_mul_right c hb_le_a
        exact Nat.le_of_mul_le_mul_left h1 ha_pos
      suffices h : u.val * c / a - v.val * c / a ≤ c - d by omega
      have hdiff_eq : u.val * c = δ * c + v.val * c := by
        simp only [δ]; rw [← Nat.add_mul, Nat.sub_add_cancel hvu]
      have h_split := Nat.add_div (a := δ * c) (b := v.val * c) ha_pos
      rw [hdiff_eq]
      have hv_div_le : v.val * c / a ≤ u.val * c / a :=
        Nat.div_le_div_right (Nat.mul_le_mul_right c hvu)
      by_cases hremainder : a ≤ δ * c % a + v.val * c % a
      · -- The +1 case: need strict bound
        simp only [if_pos hremainder] at h_split
        have hrem_pos : 0 < δ * c % a := by
          by_contra h; push_neg at h
          have hrem_zero : δ * c % a = 0 := Nat.le_zero.mp h
          rw [hrem_zero] at hremainder
          have hv_rem_lt : v.val * c % a < a := Nat.mod_lt _ ha_pos; omega
        have hstrict := div_add_one_le_of_rem_pos a b c d δ ha_pos hc_pos had_le_bc
          hδ_bounds.2 hrem_pos
        -- Derive: u.val * c / a - v.val * c / a = δ * c / a + 1
        have h_eq : u.val * c / a - v.val * c / a = δ * c / a + 1 := by
          have h1 : u.val * c / a = δ * c / a + v.val * c / a + 1 := by
            rw [hdiff_eq]; exact h_split
          omega
        omega
      · -- No +1 case
        simp only [if_neg hremainder] at h_split
        -- Derive: u.val * c / a - v.val * c / a = δ * c / a
        have h_eq : u.val * c / a - v.val * c / a = δ * c / a := by
          have h1 : u.val * c / a = δ * c / a + v.val * c / a := by
            rw [hdiff_eq]; exact h_split
          omega
        have hδca_le : δ * c / a ≤ c - d := calc
          δ * c / a ≤ (a - b) * c / a := Nat.div_le_div_right (Nat.mul_le_mul_right c hδ_bounds.2)
          _ ≤ c - d := sub_mul_div_le a b c d ha_pos had_le_bc
        omega
end GroupTheoreticShannonCapacity
