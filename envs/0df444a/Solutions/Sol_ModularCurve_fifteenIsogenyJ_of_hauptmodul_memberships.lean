-- Prove2me | solution 1 for ModularCurve.fifteenIsogenyJ_of_hauptmodul_memberships
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d2a4e2d5-9f48-5a74-9447-ea19e17713ea

import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Algebra.Rat
import Theorems.Thm_ModularCurve_FifteenA1_coords_of_equation
import Theorems.Thm_ModularCurve_psiFifteen_birational_identity
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_fifteenIsogenyJ_of_hauptmodul_memberships
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularCurve.FifteenA1.deltaPair_zero ModularCurve.FifteenA1.shortW_a₄ ModularCurve.FifteenA1.shortW_a₁ ModularCurve.FifteenA1.shortW_a₂ ModularCurve.FifteenA1.shortW_a₆ ModularCurve.FifteenA1.shortW_a₃ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

namespace M4cP3

def psiFifteen (u v : ℚ) : ℚ :=
  (u + 27) * (u + 3) ^ 3 * v - u * (v ^ 2 + 10 * v + 5) ^ 3

theorem psiFifteen_eq_zero_of_memberships {u v W C : ℚ} (hW : W ≠ 0)
    (h3 : (u + 27) * (u + 3) ^ 3 * W = C * u)
    (h5 : (v ^ 2 + 10 * v + 5) ^ 3 * W = C * v) :
    psiFifteen u v = 0 := by
  have key : psiFifteen u v * W = 0 := by
    unfold psiFifteen
    linear_combination v * h3 - u * h5
  exact (mul_eq_zero.mp key).resolve_right hW

theorem ne_zero_of_hauptmodulFive_membership {D C v : ℚ} (hD : D ≠ 0)
    (h5 : (v ^ 2 + 10 * v + 5) ^ 3 * D = C * v) : v ≠ 0 := by
  intro hv0
  apply hD
  have h0 : ((0 : ℚ) ^ 2 + 10 * 0 + 5) ^ 3 * D = C * 0 := by rw [← hv0]; exact h5
  linear_combination (1 / 125 : ℚ) * h0

def birationalXNum (u v : ℚ) : ℚ :=
  135 - 1701 * v - 972 * v ^ 2 - 108 * v ^ 3 + 250 * u - 146 * u * v - 12 * u * v ^ 2
    - 8 * u * v ^ 3 + 15 * u ^ 2 - 13 * u ^ 2 * v

def birationalXDen (u v : ℚ) : ℚ :=
  1458 * v + 621 * v ^ 2 + 54 * v ^ 3 - 250 * u - 7 * u * v - 24 * u * v ^ 2 - u * v ^ 3
    - 15 * u ^ 2 + 4 * u ^ 2 * v

def birationalYNum (u v : ℚ) : ℚ :=
  64125 - 196047 * v - 86022 * v ^ 2 - 5778 * v ^ 3 + 10125 * u - 79605 * u * v
    - 10035 * u * v ^ 2 + 225 * u * v ^ 3 - 432 * u ^ 2 * v + 63 * u ^ 2 * v ^ 2
    + 27 * u ^ 2 * v ^ 3 + 90 * u ^ 3 * v

def birationalYDen (u v : ℚ) : ℚ :=
  134136 * v + 43011 * v ^ 2 + 2889 * v ^ 3 - 23000 * u + 290 * u * v + 2930 * u * v ^ 2
    + 225 * u * v ^ 3 - 1125 * u ^ 2 - 484 * u ^ 2 * v - 44 * u ^ 2 * v ^ 2
    - u ^ 2 * v ^ 3 + 5 * u ^ 3 * v

theorem birational_weierstrass_identity {u v : ℚ} (hpsi : psiFifteen u v = 0) :
    birationalYNum u v ^ 2 * birationalXDen u v ^ 3
        + birationalXNum u v * birationalYNum u v * birationalXDen u v ^ 2 * birationalYDen u v
        + birationalYNum u v * birationalXDen u v ^ 3 * birationalYDen u v
        - birationalXNum u v ^ 3 * birationalYDen u v ^ 2
        - birationalXNum u v ^ 2 * birationalXDen u v * birationalYDen u v ^ 2
        + 10 * birationalXNum u v * birationalXDen u v ^ 2 * birationalYDen u v ^ 2
        + 10 * birationalXDen u v ^ 3 * birationalYDen u v ^ 2 = 0 :=
  ModularCurve.psiFifteen_birational_identity u v hpsi (birationalXNum u v)
    (birationalXDen u v) (birationalYNum u v) (birationalYDen u v) rfl rfl rfl rfl

theorem birationalMap_equation {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hD : birationalXDen u v ≠ 0) (hD' : birationalYDen u v ≠ 0) :
    (birationalYNum u v / birationalYDen u v) ^ 2
        + (birationalXNum u v / birationalXDen u v) * (birationalYNum u v / birationalYDen u v)
        + (birationalYNum u v / birationalYDen u v)
      = (birationalXNum u v / birationalXDen u v) ^ 3
        + (birationalXNum u v / birationalXDen u v) ^ 2
        - 10 * (birationalXNum u v / birationalXDen u v) - 10 := by
  have key := birational_weierstrass_identity hpsi
  have h2 : (birationalYNum u v / birationalYDen u v) ^ 2
        + (birationalXNum u v / birationalXDen u v) * (birationalYNum u v / birationalYDen u v)
        + (birationalYNum u v / birationalYDen u v)
        - ((birationalXNum u v / birationalXDen u v) ^ 3
          + (birationalXNum u v / birationalXDen u v) ^ 2
          - 10 * (birationalXNum u v / birationalXDen u v) - 10)
      = (birationalYNum u v ^ 2 * birationalXDen u v ^ 3
        + birationalXNum u v * birationalYNum u v * birationalXDen u v ^ 2 * birationalYDen u v
        + birationalYNum u v * birationalXDen u v ^ 3 * birationalYDen u v
        - birationalXNum u v ^ 3 * birationalYDen u v ^ 2
        - birationalXNum u v ^ 2 * birationalXDen u v * birationalYDen u v ^ 2
        + 10 * birationalXNum u v * birationalXDen u v ^ 2 * birationalYDen u v ^ 2
        + 10 * birationalXDen u v ^ 3 * birationalYDen u v ^ 2)
          / (birationalXDen u v ^ 3 * birationalYDen u v ^ 2) := by
    field_simp
    ring
  rw [key, zero_div] at h2
  linear_combination h2

theorem image_mem_fifteenA1_of_psiFifteen_eq_zero {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hD : birationalXDen u v ≠ 0) (hD' : birationalYDen u v ≠ 0) :
    (birationalXNum u v / birationalXDen u v = -2
        ∧ birationalYNum u v / birationalYDen u v = 3) ∨
      (birationalXNum u v / birationalXDen u v = 3
        ∧ birationalYNum u v / birationalYDen u v = -2) ∨
      (birationalXNum u v / birationalXDen u v = -2
        ∧ birationalYNum u v / birationalYDen u v = -2) ∨
      (birationalXNum u v / birationalXDen u v = -1
        ∧ birationalYNum u v / birationalYDen u v = 0) ∨
      (birationalXNum u v / birationalXDen u v = 8
        ∧ birationalYNum u v / birationalYDen u v = 18) ∨
      (birationalXNum u v / birationalXDen u v = -13 / 4
        ∧ birationalYNum u v / birationalYDen u v = 9 / 8) ∨
      (birationalXNum u v / birationalXDen u v = 8
        ∧ birationalYNum u v / birationalYDen u v = -27) :=
  ModularCurve.FifteenA1.coords_of_equation _ _ (birationalMap_equation hpsi hD hD')

theorem not_seven_dvd_num_den (q : ℚ) (ha : ((q.num : ℤ) : ZMod 7) = 0)
    (hb : (((q.den : ℕ) : ℤ) : ZMod 7) = 0) : False := by
  have ha' : (7 : ℤ) ∣ q.num := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp ha
  have hb' : (7 : ℤ) ∣ (q.den : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 7).mp hb
  have ha'' : (7 : ℕ) ∣ q.num.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr ha'
  have hb'' : (7 : ℕ) ∣ q.den := by exact_mod_cast hb'
  have hg : (7 : ℕ) ∣ Nat.gcd q.num.natAbs q.den := Nat.dvd_gcd ha'' hb''
  rw [Nat.Coprime.gcd_eq_one q.reduced] at hg
  exact absurd (Nat.dvd_one.mp hg) (by norm_num)

theorem mul_den_eq_num' (q : ℚ) : q * ((q.den : ℕ) : ℚ) = (q.num : ℚ) :=
  (eq_div_iff (Nat.cast_ne_zero.mpr q.den_nz)).mp (Rat.num_div_den q).symm

theorem sq_ne_five (q : ℚ) : q ^ 2 ≠ 5 := by
  intro h
  have hnum := mul_den_eq_num' q
  have hQ : (q.num : ℚ) ^ 2 - 5 * ((q.den : ℕ) : ℚ) ^ 2 = 0 := by
    rw [← hnum]
    calc (q * ((q.den : ℕ) : ℚ)) ^ 2 - 5 * ((q.den : ℕ) : ℚ) ^ 2
        = ((q.den : ℕ) : ℚ) ^ 2 * (q ^ 2 - 5) := by ring
      _ = 0 := by rw [h, sub_self, mul_zero]
  have key : q.num ^ 2 - 5 * (q.den : ℤ) ^ 2 = 0 := by exact_mod_cast hQ
  have hdec : ∀ a b : ZMod 7, a ^ 2 - 5 * b ^ 2 = 0 → a = 0 ∧ b = 0 := by decide
  have key7 : (q.num : ZMod 7) ^ 2 - 5 * ((q.den : ℤ) : ZMod 7) ^ 2 = 0 := by
    have h0 := congrArg (fun z : ℤ => (z : ZMod 7)) key
    push_cast at h0 ⊢
    linear_combination h0
  obtain ⟨ha, hb⟩ := hdec _ _ key7
  exact not_seven_dvd_num_den q ha hb

theorem fiberQuadA_ne_zero (v : ℚ) : v ^ 2 + 4 * v - 1 ≠ 0 := fun h =>
  sq_ne_five (v + 2) (by linear_combination h)

theorem fiberQuadB_ne_zero (v : ℚ) : v ^ 2 + 10 * v + 5 ≠ 0 := fun h =>
  sq_ne_five ((v + 5) / 2) (by linear_combination h / 4)

theorem fiberCubic_ne_zero (q : ℚ) : 2 * q ^ 3 + 7 * q ^ 2 + 32 * q + 135 ≠ 0 := by
  intro h
  have hnum := mul_den_eq_num' q
  have hQ : 2 * (q.num : ℚ) ^ 3 + 7 * (q.num : ℚ) ^ 2 * ((q.den : ℕ) : ℚ)
      + 32 * (q.num : ℚ) * ((q.den : ℕ) : ℚ) ^ 2 + 135 * ((q.den : ℕ) : ℚ) ^ 3 = 0 := by
    rw [← hnum]
    calc 2 * (q * ((q.den : ℕ) : ℚ)) ^ 3 + 7 * (q * ((q.den : ℕ) : ℚ)) ^ 2 * ((q.den : ℕ) : ℚ)
          + 32 * (q * ((q.den : ℕ) : ℚ)) * ((q.den : ℕ) : ℚ) ^ 2 + 135 * ((q.den : ℕ) : ℚ) ^ 3
        = ((q.den : ℕ) : ℚ) ^ 3 * (2 * q ^ 3 + 7 * q ^ 2 + 32 * q + 135) := by ring
      _ = 0 := by rw [h, mul_zero]
  have key : 2 * q.num ^ 3 + 7 * q.num ^ 2 * (q.den : ℤ) + 32 * q.num * (q.den : ℤ) ^ 2
      + 135 * (q.den : ℤ) ^ 3 = 0 := by exact_mod_cast hQ
  have hdec : ∀ a b : ZMod 7,
      2 * a ^ 3 + 7 * a ^ 2 * b + 32 * a * b ^ 2 + 135 * b ^ 3 = 0 → a = 0 ∧ b = 0 := by
    decide
  have key7 : 2 * (q.num : ZMod 7) ^ 3 + 7 * (q.num : ZMod 7) ^ 2 * ((q.den : ℤ) : ZMod 7)
      + 32 * (q.num : ZMod 7) * ((q.den : ℤ) : ZMod 7) ^ 2
      + 135 * ((q.den : ℤ) : ZMod 7) ^ 3 = 0 := by
    have h0 := congrArg (fun z : ℤ => (z : ZMod 7)) key
    push_cast at h0 ⊢
    linear_combination h0
  obtain ⟨ha, hb⟩ := hdec _ _ key7
  exact not_seven_dvd_num_den q ha hb

theorem fiberSeptic_ne_zero (q : ℚ) :
    107 * q ^ 7 + 3840 * q ^ 6 + 82505 * q ^ 5 + 1249955 * q ^ 4 + 8194730 * q ^ 3
      - 18328530 * q ^ 2 - 319467500 * q - 216421875 ≠ 0 := by
  intro h
  have hnum := mul_den_eq_num' q
  have hQ : 107 * (q.num : ℚ) ^ 7 + 3840 * (q.num : ℚ) ^ 6 * ((q.den : ℕ) : ℚ)
      + 82505 * (q.num : ℚ) ^ 5 * ((q.den : ℕ) : ℚ) ^ 2
      + 1249955 * (q.num : ℚ) ^ 4 * ((q.den : ℕ) : ℚ) ^ 3
      + 8194730 * (q.num : ℚ) ^ 3 * ((q.den : ℕ) : ℚ) ^ 4
      - 18328530 * (q.num : ℚ) ^ 2 * ((q.den : ℕ) : ℚ) ^ 5
      - 319467500 * (q.num : ℚ) * ((q.den : ℕ) : ℚ) ^ 6
      - 216421875 * ((q.den : ℕ) : ℚ) ^ 7 = 0 := by
    rw [← hnum]
    calc 107 * (q * ((q.den : ℕ) : ℚ)) ^ 7 + 3840 * (q * ((q.den : ℕ) : ℚ)) ^ 6 * ((q.den : ℕ) : ℚ)
          + 82505 * (q * ((q.den : ℕ) : ℚ)) ^ 5 * ((q.den : ℕ) : ℚ) ^ 2
          + 1249955 * (q * ((q.den : ℕ) : ℚ)) ^ 4 * ((q.den : ℕ) : ℚ) ^ 3
          + 8194730 * (q * ((q.den : ℕ) : ℚ)) ^ 3 * ((q.den : ℕ) : ℚ) ^ 4
          - 18328530 * (q * ((q.den : ℕ) : ℚ)) ^ 2 * ((q.den : ℕ) : ℚ) ^ 5
          - 319467500 * (q * ((q.den : ℕ) : ℚ)) * ((q.den : ℕ) : ℚ) ^ 6
          - 216421875 * ((q.den : ℕ) : ℚ) ^ 7
        = ((q.den : ℕ) : ℚ) ^ 7 * (107 * q ^ 7 + 3840 * q ^ 6 + 82505 * q ^ 5
            + 1249955 * q ^ 4 + 8194730 * q ^ 3 - 18328530 * q ^ 2 - 319467500 * q
            - 216421875) := by ring
      _ = 0 := by rw [h, mul_zero]
  have key : 107 * q.num ^ 7 + 3840 * q.num ^ 6 * (q.den : ℤ)
      + 82505 * q.num ^ 5 * (q.den : ℤ) ^ 2 + 1249955 * q.num ^ 4 * (q.den : ℤ) ^ 3
      + 8194730 * q.num ^ 3 * (q.den : ℤ) ^ 4 - 18328530 * q.num ^ 2 * (q.den : ℤ) ^ 5
      - 319467500 * q.num * (q.den : ℤ) ^ 6 - 216421875 * (q.den : ℤ) ^ 7 = 0 := by
    exact_mod_cast hQ
  have hdec : ∀ a b : ZMod 7,
      107 * a ^ 7 + 3840 * a ^ 6 * b + 82505 * a ^ 5 * b ^ 2 + 1249955 * a ^ 4 * b ^ 3
        + 8194730 * a ^ 3 * b ^ 4 - 18328530 * a ^ 2 * b ^ 5 - 319467500 * a * b ^ 6
        - 216421875 * b ^ 7 = 0 → a = 0 ∧ b = 0 := by
    decide
  have key7 : 107 * (q.num : ZMod 7) ^ 7 + 3840 * (q.num : ZMod 7) ^ 6 * ((q.den : ℤ) : ZMod 7)
      + 82505 * (q.num : ZMod 7) ^ 5 * ((q.den : ℤ) : ZMod 7) ^ 2
      + 1249955 * (q.num : ZMod 7) ^ 4 * ((q.den : ℤ) : ZMod 7) ^ 3
      + 8194730 * (q.num : ZMod 7) ^ 3 * ((q.den : ℤ) : ZMod 7) ^ 4
      - 18328530 * (q.num : ZMod 7) ^ 2 * ((q.den : ℤ) : ZMod 7) ^ 5
      - 319467500 * (q.num : ZMod 7) * ((q.den : ℤ) : ZMod 7) ^ 6
      - 216421875 * ((q.den : ℤ) : ZMod 7) ^ 7 = 0 := by
    have h0 := congrArg (fun z : ℤ => (z : ZMod 7)) key
    push_cast at h0 ⊢
    linear_combination h0
  obtain ⟨ha, hb⟩ := hdec _ _ key7
  exact not_seven_dvd_num_den q ha hb

theorem fiberQuad87_ne_zero (q : ℚ) : 87 * q ^ 2 - 1267 * q - 6350 ≠ 0 := by
  intro h
  have hnum := mul_den_eq_num' q
  have hQ : 87 * (q.num : ℚ) ^ 2 - 1267 * (q.num : ℚ) * ((q.den : ℕ) : ℚ)
      - 6350 * ((q.den : ℕ) : ℚ) ^ 2 = 0 := by
    rw [← hnum]
    calc 87 * (q * ((q.den : ℕ) : ℚ)) ^ 2 - 1267 * (q * ((q.den : ℕ) : ℚ)) * ((q.den : ℕ) : ℚ)
          - 6350 * ((q.den : ℕ) : ℚ) ^ 2
        = ((q.den : ℕ) : ℚ) ^ 2 * (87 * q ^ 2 - 1267 * q - 6350) := by ring
      _ = 0 := by rw [h, mul_zero]
  have key : 87 * q.num ^ 2 - 1267 * q.num * (q.den : ℤ) - 6350 * (q.den : ℤ) ^ 2 = 0 := by
    exact_mod_cast hQ
  have hdec : ∀ a b : ZMod 7,
      87 * a ^ 2 - 1267 * a * b - 6350 * b ^ 2 = 0 → a = 0 ∧ b = 0 := by
    decide
  have key7 : 87 * (q.num : ZMod 7) ^ 2 - 1267 * (q.num : ZMod 7) * ((q.den : ℤ) : ZMod 7)
      - 6350 * ((q.den : ℤ) : ZMod 7) ^ 2 = 0 := by
    have h0 := congrArg (fun z : ℤ => (z : ZMod 7)) key
    push_cast at h0 ⊢
    linear_combination h0
  obtain ⟨ha, hb⟩ := hdec _ _ key7
  exact not_seven_dvd_num_den q ha hb

def fiberEliminationKernel (v : ℚ) : ℚ :=
  (v ^ 2 + 4 * v - 1) ^ 2
    * ((v ^ 2 + 10 * v + 5) ^ 3 * (2 * v ^ 3 + 7 * v ^ 2 + 32 * v + 135))

theorem fiberEliminationKernel_ne_zero (v : ℚ) : fiberEliminationKernel v ≠ 0 := by
  unfold fiberEliminationKernel
  intro h
  rcases mul_eq_zero.mp h with h | h
  · exact fiberQuadA_ne_zero v ((pow_eq_zero_iff two_ne_zero).mp h)
  · rcases mul_eq_zero.mp h with h | h
    · exact fiberQuadB_ne_zero v ((pow_eq_zero_iff three_ne_zero).mp h)
    · exact fiberCubic_ne_zero v h

set_option maxHeartbeats 6400000 in

theorem birationalXDen_ne_zero {u v : ℚ} (hpsi : psiFifteen u v = 0) (hv : v ≠ 0) :
    birationalXDen u v ≠ 0 := by
  intro hD
  have hR : 27 * v ^ 2 * fiberEliminationKernel v = 0 := by
    unfold fiberEliminationKernel
    unfold psiFifteen at hpsi
    unfold birationalXDen at hD
    linear_combination
      (4 * u * v ^ 7 + (-15) * u * v ^ 6 + 988 * u * v ^ 5 + 16335 * u * v ^ 4 +
        30950 * u * v ^ 3 + (-78875) * u * v ^ 2 + 491250 * u * v + (-6328125) * u +
        (-1) * v ^ 9 + (-24) * v ^ 8 + (-38) * v ^ 7 + (-874) * v ^ 6 + (-45273) * v ^ 5 +
        (-654680) * v ^ 4 + (-4073750) * v ^ 3 + (-16221000) * v ^ 2 + (-59796250) * v +
        (-105468750)) * hpsi +
      ((-1) * u ^ 3 * v ^ 7 + (-247) * u ^ 3 * v ^ 5 + (-5010) * u ^ 3 * v ^ 4 +
        (-26525) * u ^ 3 * v ^ 3 + (-79750) * u ^ 3 * v ^ 2 + (-421875) * u ^ 3 * v +
        (-90) * u ^ 2 * v ^ 7 + (-2781) * u ^ 2 * v ^ 6 + (-45126) * u ^ 2 * v ^ 5 +
        (-355860) * u ^ 2 * v ^ 4 + (-1538100) * u ^ 2 * v ^ 3 + (-5331375) * u ^ 2 * v ^ 2 +
        (-15187500) * u ^ 2 * v + (-864) * u * v ^ 8 + (-27594) * u * v ^ 7 +
        (-358830) * u * v ^ 6 + (-2551392) * u * v ^ 5 + (-11762010) * u * v ^ 4 +
        (-42506100) * u * v ^ 3 + (-110106000) * u * v ^ 2 + (-113906250) * u * v + 1 * v ^ 12 +
        30 * v ^ 11 + 346 * v ^ 10 + 2110 * v ^ 9 + 9020 * v ^ 8 + 31004 * v ^ 7 +
        64034 * v ^ 6 + 45344 * v ^ 5 + 10440 * v ^ 4 + 481500 * v ^ 3 + 2989000 * v ^ 2 +
        7437500 * v + 52734375) * hD
  rcases mul_eq_zero.mp hR with h | h
  · rcases mul_eq_zero.mp h with h | h
    · norm_num at h
    · exact hv ((pow_eq_zero_iff two_ne_zero).mp h)
  · exact fiberEliminationKernel_ne_zero v h

set_option maxHeartbeats 6400000 in

theorem birationalY_not_both_zero {u v : ℚ} (hN : birationalYNum u v = 0)
    (hD : birationalYDen u v = 0) : False := by
  have hR : 3375 * (v ^ 2 + 4 * v - 1) * (v ^ 2 + 10 * v + 5)
      * (87 * v ^ 2 - 1267 * v - 6350)
      * (107 * v ^ 7 + 3840 * v ^ 6 + 82505 * v ^ 5 + 1249955 * v ^ 4 + 8194730 * v ^ 3
          - 18328530 * v ^ 2 - 319467500 * v - 216421875) = 0 := by
    unfold birationalYNum at hN
    unfold birationalYDen at hD
    linear_combination
      ((-140) * u ^ 2 * v ^ 8 + (-4170) * u ^ 2 * v ^ 7 + (-84050) * u ^ 2 * v ^ 6 +
        (-1159865) * u ^ 2 * v ^ 5 + (-4360025) * u ^ 2 * v ^ 4 + 39102675 * u ^ 2 * v ^ 3 +
        195955625 * u ^ 2 * v ^ 2 + 113906250 * u ^ 2 * v + 28 * u * v ^ 10 + 2066 * u * v ^ 9 +
        68663 * u * v ^ 8 + 1453134 * u * v ^ 7 + 21196132 * u * v ^ 6 + 177311547 * u * v ^ 5 +
        377951055 * u * v ^ 4 + (-4723569290) * u * v ^ 3 + (-30121570750) * u * v ^ 2 +
        (-55837546875) * u * v + (-25628906250) * u + (-6621) * v ^ 10 + (-293087) * v ^ 9 +
        (-7049306) * v ^ 8 + (-119215653) * v ^ 7 + (-1137604729) * v ^ 6 +
        (-2924136524) * v ^ 5 + 28425787890 * v ^ 4 + 164825873005 * v ^ 3 +
        107616636500 * v ^ 2 + (-505875828125) * v + (-361652343750)) * hN +
      (2520 * u ^ 2 * v ^ 8 + 75060 * u ^ 2 * v ^ 7 + 1512900 * u ^ 2 * v ^ 6 +
        20877570 * u ^ 2 * v ^ 5 + 78480450 * u ^ 2 * v ^ 4 + (-703848150) * u ^ 2 * v ^ 3 +
        (-3527201250) * u ^ 2 * v ^ 2 + (-2050312500) * u ^ 2 * v + 756 * u * v ^ 10 +
        24282 * u * v ^ 9 + 465426 * u * v ^ 8 + 6127443 * u * v ^ 7 + 12122064 * u * v ^ 6 +
        (-536828706) * u * v ^ 5 + (-3335622390) * u * v ^ 4 + 3394750545 * u * v ^ 3 +
        39841956000 * u * v ^ 2 + 22826812500 * u * v + (-2367) * v ^ 10 + (-363924) * v ^ 9 +
        (-12113712) * v ^ 8 + (-257368356) * v ^ 7 + (-3775669083) * v ^ 6 +
        (-26586951273) * v ^ 5 + 2589596280 * v ^ 4 + 819920989260 * v ^ 3 +
        2561337918000 * v ^ 2 + 1088884265625 * v + (-230660156250)) * hD
  rcases mul_eq_zero.mp hR with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · exact fiberQuadA_ne_zero v h
      · exact fiberQuadB_ne_zero v h
    · exact fiberQuad87_ne_zero v h
  · exact fiberSeptic_ne_zero v h

theorem birationalYDen_ne_zero {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hD4 : birationalXDen u v ≠ 0) : birationalYDen u v ≠ 0 := by
  intro hD5
  have hW := birational_weierstrass_identity hpsi
  rw [hD5] at hW
  have h2 : birationalYNum u v ^ 2 * birationalXDen u v ^ 3 = 0 := by linear_combination hW
  rcases mul_eq_zero.mp h2 with h | h
  · exact birationalY_not_both_zero ((pow_eq_zero_iff two_ne_zero).mp h) hD5
  · exact hD4 ((pow_eq_zero_iff three_ne_zero).mp h)

set_option maxHeartbeats 6400000 in

theorem fiber_x_neg_two {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hg : birationalXNum u v + 2 * birationalXDen u v = 0) :
    u = -729 / 32 ∧ v = -25 / 8 := by
  have hR : 135 * (8 * v + 25) * fiberEliminationKernel v = 0 := by
    unfold fiberEliminationKernel
    unfold psiFifteen at hpsi
    unfold birationalXNum birationalXDen at hg
    linear_combination
      ((-40) * u * v ^ 7 + (-525) * u * v ^ 6 + (-3130) * u * v ^ 5 + (-13095) * u * v ^ 4 +
        (-42740) * u * v ^ 3 + (-92395) * u * v ^ 2 + (-107850) * u * v + (-50625) * u +
        (-80) * v ^ 9 + (-1290) * v ^ 8 + (-9970) * v ^ 7 + (-53720) * v ^ 6 +
        (-223530) * v ^ 5 + (-691720) * v ^ 4 + (-1536310) * v ^ 3 + (-2361840) * v ^ 2 +
        (-2193950) * v + (-843750)) * hpsi +
      ((-8) * u ^ 3 * v ^ 7 + (-81) * u ^ 3 * v ^ 6 + (-383) * u ^ 3 * v ^ 5 +
        (-1470) * u ^ 3 * v ^ 4 + (-4138) * u ^ 3 * v ^ 3 + (-6065) * u ^ 3 * v ^ 2 +
        (-3375) * u ^ 3 * v + (-288) * u ^ 2 * v ^ 7 + (-3132) * u ^ 2 * v ^ 6 +
        (-15624) * u ^ 2 * v ^ 5 + (-57780) * u ^ 2 * v ^ 4 + (-156204) * u ^ 2 * v ^ 3 +
        (-227520) * u ^ 2 * v ^ 2 + (-121500) * u ^ 2 * v + (-2214) * u * v ^ 7 +
        (-31401) * u * v ^ 6 + (-196533) * u * v ^ 5 + (-729270) * u * v ^ 4 +
        (-1693548) * u * v ^ 3 + (-2132865) * u * v ^ 2 + (-941625) * u * v + 8 * v ^ 12 +
        321 * v ^ 11 + 5333 * v ^ 10 + 48983 * v ^ 9 + 290617 * v ^ 8 + 1270414 * v ^ 7 +
        4267378 * v ^ 6 + 9848176 * v ^ 5 + 12603420 * v ^ 4 + 6170841 * v ^ 3 +
        203705 * v ^ 2 + 150625 * v + 421875) * hg
  have hveq : v = -25 / 8 := by
    rcases mul_eq_zero.mp hR with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by norm_num)
      · linarith
    · exact absurd h (fiberEliminationKernel_ne_zero v)
  refine ⟨?_, hveq⟩
  rw [hveq] at hg hpsi
  have hquad : (5 : ℚ) * ((u - 72) * (32 * u + 729)) = 0 := by
    unfold birationalXNum birationalXDen at hg
    linear_combination 256 * hg
  rcases mul_eq_zero.mp hquad with h | h
  · exact absurd h (by norm_num)
  rcases mul_eq_zero.mp h with h | h
  · exfalso
    have hu72 : u = 72 := by linarith
    rw [hu72] at hpsi
    exact absurd hpsi (by unfold psiFifteen; norm_num)
  · linarith

set_option maxHeartbeats 6400000 in

theorem fiber_x_three {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hg : birationalXNum u v - 3 * birationalXDen u v = 0) :
    u = -729 / 2 ∧ v = -40 := by
  have hR : 135 * (v + 40) ^ 2 * fiberEliminationKernel v = 0 := by
    unfold fiberEliminationKernel
    unfold psiFifteen at hpsi
    unfold birationalXNum birationalXDen at hg
    linear_combination
      (25 * u * v ^ 7 + 1965 * u * v ^ 6 + 44515 * u * v ^ 5 + (-110025) * u * v ^ 4 +
        (-271840) * u * v ^ 3 + 1753600 * u * v ^ 2 + (-8160000) * u * v + 12960000 * u +
        5 * v ^ 9 + 345 * v ^ 8 + 3790 * v ^ 7 + (-75415) * v ^ 6 + 467700 * v ^ 5 +
        (-952550) * v ^ 4 + (-12104555) * v ^ 3 + 1030200 * v ^ 2 + 15290000 * v +
        216000000) * hpsi +
      (1 * u ^ 3 * v ^ 7 + 81 * u ^ 3 * v ^ 6 + 1975 * u ^ 3 * v ^ 5 + 339 * u ^ 3 * v ^ 4 +
        (-10060) * u ^ 3 * v ^ 3 + 46000 * u ^ 3 * v ^ 2 + (-216000) * u ^ 3 * v +
        (-18) * u ^ 2 * v ^ 7 + 4077 * u ^ 2 * v ^ 6 + 88785 * u ^ 2 * v ^ 5 +
        60507 * u ^ 2 * v ^ 4 + (-512955) * u ^ 2 * v ^ 3 + 184500 * u ^ 2 * v ^ 2 +
        (-7776000) * u ^ 2 * v + (-1350) * u * v ^ 8 + (-36153) * u * v ^ 7 +
        (-241569) * u * v ^ 6 + 132165 * u * v ^ 5 + 310419 * u * v ^ 4 +
        (-13075560) * u * v ^ 3 + (-37800000) * u * v ^ 2 + (-57834000) * u * v +
        (-1) * v ^ 12 + (-111) * v ^ 11 + (-4450) * v ^ 10 + (-81517) * v ^ 9 +
        (-787349) * v ^ 8 + (-4541165) * v ^ 7 + (-18844478) * v ^ 6 + (-61767020) * v ^ 5 +
        (-123708753) * v ^ 4 + (-89923455) * v ^ 3 + (-1379125) * v ^ 2 + 2350000 * v +
        27000000) * hg
  have hveq : v = -40 := by
    rcases mul_eq_zero.mp hR with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by norm_num)
      · have := (pow_eq_zero_iff two_ne_zero).mp h
        linarith
    · exact absurd h (fiberEliminationKernel_ne_zero v)
  refine ⟨?_, hveq⟩
  rw [hveq] at hg hpsi
  have hquad : (5 : ℚ) * ((2 * u + 729) * (106 * u + 3563)) = 0 := by
    unfold birationalXNum birationalXDen at hg
    linear_combination hg
  rcases mul_eq_zero.mp hquad with h | h
  · exact absurd h (by norm_num)
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exfalso
    have hu2 : u = -3563 / 106 := by linarith
    rw [hu2] at hpsi
    exact absurd hpsi (by unfold psiFifteen; norm_num)

set_option maxHeartbeats 6400000 in

theorem fiber_x_neg_one {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hg : birationalXNum u v + birationalXDen u v = 0) : False := by
  have hR : (27 : ℚ) * fiberEliminationKernel v = 0 := by
    unfold fiberEliminationKernel
    unfold psiFifteen at hpsi
    unfold birationalXNum birationalXDen at hg
    linear_combination
      (9 * u * v ^ 5 + 45 * u * v ^ 4 + 243 * u * v ^ 3 + 855 * u * v ^ 2 + 9 * v ^ 7 +
        81 * v ^ 6 + 522 * v ^ 5 + 2241 * v ^ 4 + 7632 * v ^ 3 + 16290 * v ^ 2 +
        2025 * v) * hpsi +
      (1 * u ^ 3 * v ^ 5 + 5 * u ^ 3 * v ^ 4 + 27 * u ^ 3 * v ^ 3 + 95 * u ^ 3 * v ^ 2 +
        30 * u ^ 2 * v ^ 5 + 141 * u ^ 2 * v ^ 4 + 981 * u ^ 2 * v ^ 3 + 3615 * u ^ 2 * v ^ 2 +
        225 * u ^ 2 * v + (-6) * u * v ^ 6 + (-81) * u * v ^ 5 + (-1365) * u * v ^ 4 +
        2097 * u * v ^ 3 + 26295 * u * v ^ 2 + 5700 * u * v + (-1) * v ^ 10 + (-35) * v ^ 9 +
        (-486) * v ^ 8 + (-3585) * v ^ 7 + (-17225) * v ^ 6 + (-64689) * v ^ 5 +
        (-173674) * v ^ 4 + (-234364) * v ^ 3 + (-75585) * v ^ 2 + 125 * v + 3375) * hg
  rcases mul_eq_zero.mp hR with h | h
  · norm_num at h
  · exact fiberEliminationKernel_ne_zero v h

set_option maxHeartbeats 6400000 in

theorem fiber_x_neg_thirteen_quarters {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hg : 4 * birationalXNum u v + 13 * birationalXDen u v = 0) :
    u = -2 ∧ v = -10 := by
  have hR : 135 * (v + 10) ^ 2 * fiberEliminationKernel v = 0 := by
    unfold fiberEliminationKernel
    unfold psiFifteen at hpsi
    unfold birationalXNum birationalXDen at hg
    linear_combination
      ((-135) * u * v ^ 6 + (-2160) * u * v ^ 5 + (-12825) * u * v ^ 4 + (-45090) * u * v ^ 3 +
        (-165375) * u * v ^ 2 + (-411750) * u * v + (-455625) * u + (-45) * v ^ 9 +
        (-1080) * v ^ 8 + (-10710) * v ^ 7 + (-63090) * v ^ 6 + (-294525) * v ^ 5 +
        (-1167300) * v ^ 4 + (-3336930) * v ^ 3 + (-6961500) * v ^ 2 + (-11094750) * v +
        (-7593750)) * hpsi +
      ((-1) * u ^ 3 * v ^ 7 + (-16) * u ^ 3 * v ^ 6 + (-95) * u ^ 3 * v ^ 5 +
        (-334) * u ^ 3 * v ^ 4 + (-1225) * u ^ 3 * v ^ 3 + (-3050) * u ^ 3 * v ^ 2 +
        (-3375) * u ^ 3 * v + (-42) * u ^ 2 * v ^ 7 + (-717) * u ^ 2 * v ^ 6 +
        (-4530) * u ^ 2 * v ^ 5 + (-15792) * u ^ 2 * v ^ 4 + (-51000) * u ^ 2 * v ^ 3 +
        (-124275) * u ^ 2 * v ^ 2 + (-121500) * u ^ 2 * v + (-522) * u * v ^ 7 +
        (-10566) * u * v ^ 6 + (-79560) * u * v ^ 5 + (-302814) * u * v ^ 4 +
        (-775800) * u * v ^ 3 + (-1419300) * u * v ^ 2 + (-924750) * u * v + 1 * v ^ 12 +
        46 * v ^ 11 + 890 * v ^ 10 + 9542 * v ^ 9 + 64364 * v ^ 8 + 305440 * v ^ 7 +
        1113438 * v ^ 6 + 2960400 * v ^ 5 + 4563768 * v ^ 4 + 2639900 * v ^ 3 +
        107600 * v ^ 2 + 100000 * v + 421875) * hg
  have hveq : v = -10 := by
    rcases mul_eq_zero.mp hR with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by norm_num)
      · have := (pow_eq_zero_iff two_ne_zero).mp h
        linarith
    · exact absurd h (fiberEliminationKernel_ne_zero v)
  refine ⟨?_, hveq⟩
  rw [hveq] at hg hpsi
  have hquad : (-135 : ℚ) * ((u + 2) * (u - 102)) = 0 := by
    unfold birationalXNum birationalXDen at hg
    linear_combination hg
  rcases mul_eq_zero.mp hquad with h | h
  · exact absurd h (by norm_num)
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exfalso
    have hu2 : u = 102 := by linarith
    rw [hu2] at hpsi
    exact absurd hpsi (by unfold psiFifteen; norm_num)

set_option maxHeartbeats 6400000 in

theorem fiber_x_eight {u v : ℚ} (hpsi : psiFifteen u v = 0)
    (hg : birationalXNum u v - 8 * birationalXDen u v = 0) :
    u = -32 ∧ v = -25 / 2 := by
  have hR : 135 * (2 * v + 25) * fiberEliminationKernel v = 0 := by
    unfold fiberEliminationKernel
    unfold psiFifteen at hpsi
    unfold birationalXNum birationalXDen at hg
    linear_combination
      (45 * u * v ^ 6 + 450 * u * v ^ 5 + (-2385) * u * v ^ 4 + (-4500) * u * v ^ 3 +
        17595 * u * v ^ 2 + (-147150) * u * v + 455625 * u + (-180) * v ^ 7 + (-2250) * v ^ 6 +
        (-720) * v ^ 5 + (-22230) * v ^ 4 + (-72180) * v ^ 3 + 478890 * v ^ 2 + 2626200 * v +
        7593750) * hpsi +
      (1 * u ^ 3 * v ^ 6 + 13 * u ^ 3 * v ^ 5 + (-14) * u ^ 3 * v ^ 4 +
        (-142) * u ^ 3 * v ^ 3 + (-35) * u ^ 3 * v ^ 2 + (-3375) * u ^ 3 * v +
        36 * u ^ 2 * v ^ 6 + 420 * u ^ 2 * v ^ 5 + (-1032) * u ^ 2 * v ^ 4 +
        (-8856) * u ^ 2 * v ^ 3 + (-22380) * u ^ 2 * v ^ 2 + (-121500) * u ^ 2 * v +
        (-12) * u * v ^ 8 + (-324) * u * v ^ 7 + (-2739) * u * v ^ 6 + (-9567) * u * v ^ 5 +
        (-49794) * u * v ^ 4 + (-270282) * u * v ^ 3 + (-750735) * u * v ^ 2 +
        (-907875) * u * v + (-1) * v ^ 11 + (-43) * v ^ 10 + (-739) * v ^ 9 + (-6681) * v ^ 8 +
        (-37094) * v ^ 7 + (-151324) * v ^ 6 + (-479200) * v ^ 5 + (-911622) * v ^ 4 +
        (-628901) * v ^ 3 + 3395 * v ^ 2 + 49375 * v + 421875) * hg
  have hveq : v = -25 / 2 := by
    rcases mul_eq_zero.mp hR with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact absurd h (by norm_num)
      · linarith
    · exact absurd h (fiberEliminationKernel_ne_zero v)
  refine ⟨?_, hveq⟩
  rw [hveq] at hg hpsi
  have hquad : (45 : ℚ) * ((u + 32) * (31 * u + 408)) = 0 := by
    unfold birationalXNum birationalXDen at hg
    linear_combination 2 * hg
  rcases mul_eq_zero.mp hquad with h | h
  · exact absurd h (by norm_num)
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · exfalso
    have hu2 : u = -408 / 31 := by linarith
    rw [hu2] at hpsi
    exact absurd hpsi (by unfold psiFifteen; norm_num)

theorem onlyFourPoints {u v : ℚ} (hpsi : psiFifteen u v = 0) (hv : v ≠ 0) :
    (u = -2 ∧ v = -10) ∨ (u = -729 / 2 ∧ v = -40) ∨ (u = -32 ∧ v = -25 / 2) ∨
      (u = -729 / 32 ∧ v = -25 / 8) := by

  have hD4 : birationalXDen u v ≠ 0 := birationalXDen_ne_zero hpsi hv
  have hD5 : birationalYDen u v ≠ 0 := birationalYDen_ne_zero hpsi hD4

  rcases image_mem_fifteenA1_of_psiFifteen_eq_zero hpsi hD4 hD5 with
    ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, hy⟩ | ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, -⟩ | ⟨hx, hy⟩

  · obtain ⟨h1, h2⟩ := fiber_x_neg_two hpsi
      (by linear_combination (div_eq_iff hD4).mp hx)
    exact Or.inr (Or.inr (Or.inr ⟨h1, h2⟩))

  · obtain ⟨h1, h2⟩ := fiber_x_three hpsi
      (by linear_combination (div_eq_iff hD4).mp hx)
    exact Or.inr (Or.inl ⟨h1, h2⟩)

  · exfalso
    obtain ⟨h1, h2⟩ := fiber_x_neg_two hpsi
      (by linear_combination (div_eq_iff hD4).mp hx)
    rw [h1, h2] at hy
    rw [div_eq_iff (by unfold birationalYDen; norm_num)] at hy
    revert hy
    unfold birationalYNum birationalYDen
    norm_num

  · exact absurd (by linear_combination (div_eq_iff hD4).mp hx)
      (fun h => fiber_x_neg_one hpsi h)

  · obtain ⟨h1, h2⟩ := fiber_x_eight hpsi
      (by linear_combination (div_eq_iff hD4).mp hx)
    exact Or.inr (Or.inr (Or.inl ⟨h1, h2⟩))

  · obtain ⟨h1, h2⟩ := fiber_x_neg_thirteen_quarters hpsi
      (by linear_combination 4 * (div_eq_iff hD4).mp hx)
    exact Or.inl ⟨h1, h2⟩

  · exfalso
    obtain ⟨h1, h2⟩ := fiber_x_eight hpsi
      (by linear_combination (div_eq_iff hD4).mp hx)
    rw [h1, h2] at hy
    rw [div_eq_iff (by unfold birationalYDen; norm_num)] at hy
    revert hy
    unfold birationalYNum birationalYDen
    norm_num

end M4cP3

open M4cP3 in

theorem solution {D C u v : ℚ} (hD : D ≠ 0) (h3 : (u + 27) * (u + 3) ^ 3 * D = C * u) (h5 : (v ^ 2 + 10 * v + 5) ^ 3 * D = C * v) : C = -25 / 2 * D ∨ C = -349938025 / 8 * D ∨ C = -121945 / 32 * D ∨ C = 46969655 / 32768 * D := by

  have hv : v ≠ 0 := ne_zero_of_hauptmodulFive_membership hD h5

  have hpsi : psiFifteen u v = 0 := psiFifteen_eq_zero_of_memberships hD h3 h5

  rcases onlyFourPoints hpsi hv with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl (by linear_combination (1 / 2 : ℚ) * h3)
  · exact Or.inr (Or.inl (by linear_combination (2 / 729 : ℚ) * h3))
  · exact Or.inr (Or.inr (Or.inl (by linear_combination (1 / 32 : ℚ) * h3)))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination (32 / 729 : ℚ) * h3)))

end S_ModularCurve_fifteenIsogenyJ_of_hauptmodul_memberships
end P2MW
export P2MW.S_ModularCurve_fifteenIsogenyJ_of_hauptmodul_memberships (solution)
