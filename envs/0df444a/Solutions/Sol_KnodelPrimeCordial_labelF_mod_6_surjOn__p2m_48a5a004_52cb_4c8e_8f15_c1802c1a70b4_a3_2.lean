-- Prove2me | solution 2 for KnodelPrimeCordial.labelF_mod_6_surjOn__p2m_48a5a004_52cb_4c8e_8f15_c1802c1a70b4_a3
-- status  : ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-16T13:00:57.018389+00:00
-- url     : https://prove2.me/submissions/a4db1de0-e377-435f-a5eb-82e776f33670

import Mathlib
import Definitions.Def_KnodelPrimeCordial_labelF

private def inverseLabelResidue (r : ℕ) : ℕ :=
  match r with
  | 0 => 3
  | 1 => 0
  | 2 => 4
  | 3 => 1
  | 4 => 2
  | 5 => 5
  | 6 => 8
  | 7 => 6
  | 8 => 9
  | 9 => 11
  | 10 => 7
  | _ => 10

theorem solution (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) :
    Set.SurjOn KnodelPrimeCordial.labelF (Set.Icc 0 (n - 1)) (Set.Icc 1 n) := by
  intro y hy
  have hy1 : 1 ≤ y := hy.1
  have hyn : y ≤ n := hy.2
  let k : ℕ := n / 12
  let z : ℕ := y - 1
  let q : ℕ := z / 12
  let r : ℕ := z % 12
  have hnrepr : n = 12 * k + 6 := by
    dsimp [k]
    have h := Nat.mod_add_div n 12
    omega
  have hzrepr : z = 12 * q + r := by
    dsimp [q, r]
    have h := Nat.mod_add_div z 12
    omega
  have hrlt : r < 12 := by
    dsimp [r]
    exact Nat.mod_lt _ (by decide)
  have hyle : y = 12 * q + r + 1 := by
    dsimp [z] at hzrepr
    omega
  have hqle : q ≤ k := by omega
  let s := inverseLabelResidue r
  have hslt : s < 12 := by
    dsimp [s]
    interval_cases r <;> norm_num [inverseLabelResidue]
  have hres : (12 * q + s) % 12 = s := by
    rw [Nat.add_mod]
    simp [Nat.mod_eq_of_lt hslt]
  have hlabel : KnodelPrimeCordial.labelF (12 * q + s) = y := by
    rw [KnodelPrimeCordial.labelF, hres]
    dsimp [s]
    interval_cases r <;> norm_num [inverseLabelResidue, hyle] <;> omega
  have hxle : 12 * q + s ≤ n - 1 := by
    rw [hnrepr]
    by_cases hqk : q = k
    · have hr5 : r ≤ 5 := by omega
      have hs5 : s ≤ 5 := by
        dsimp [s]
        interval_cases r <;> norm_num [inverseLabelResidue] at *
      omega
    · have hqlt : q < k := by omega
      omega
  refine ⟨12 * q + s, ⟨Nat.zero_le _, hxle⟩, hlabel⟩
