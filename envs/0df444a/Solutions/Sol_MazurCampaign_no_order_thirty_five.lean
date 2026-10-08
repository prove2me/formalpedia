-- Prove2me | solution 1 for MazurCampaign.no_order_thirty_five
-- status  : ACCEPTED   (prove)
-- author  : @Xiang Huang
-- created : 2026-10-06T21:28:38.102482+00:00
-- url     : https://prove2.me/submissions/2e3cc8bf-0be8-4312-b519-7a858a36075f

/-
No elliptic curve over the rationals has a rational point of order 35
(mission leaf MazurCampaign.no_order_thirty_five).

Author: Xiang Huang
License: Apache-2.0
Source: Xiang Huang's FLT fork, https://github.com/xiangyazi24/FLT,
  commit 51bbb4f191ad0d3753b87123635c100a638ae580
  (Lean v4.31.0-rc2), ported to Lean v4.33.1 / Mathlib 0df444a360ea.
Port repairs inside the source ranges are marked `port v4.33.1` or listed in the
port notes of the staging repository; no statement of a non-private declaration
was changed.

Contents, in order (each source range sits in its own `section`):
  * FLT/Assumptions/MazurProof/TorsionDefs.lean (HasRationalPointOfOrder)
  * FLT/Assumptions/MazurProof/CyclicOrderReduction.lean (exists_point_of_prime_order_of_dvd)
  * FLT/Assumptions/MazurProof/CyclicExclusion35.lean (order35_gives_order5, order35_gives_order7, order35_gives_orders5_and_7)
  * the leaf, assembled from three published theorems; it follows no_simultaneous_orders_five_seven and
    no_rational_point_of_order_35 of FLT/Assumptions/MazurProof/CyclicExclusion35.lean and src/Bridge/NoOrderThirtyFive.lean
-/
import Mathlib
import Definitions.Def_MazurCampaign_group_constraints
import Theorems.Thm_MazurHuang_exists_X0_five_seven_fiber_point_of_addOrderOf_eq_five_of_eq_seven
import Theorems.Thm_MazurHuang_exists_X0_thirtyFive_point_of_X0_five_seven_fiber
import Theorems.Thm_MazurHuang_eq_zero_of_X0_thirtyFive_equation

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/TorsionDefs.lean (whole module, imports dropped). -/
section

/-!
# Torsion definitions for the Mazur bound proof

Extracted from Axioms.lean to break import cycles.
Both Axioms.lean and RealTorsionBound.lean import this file.
-/

open scoped WeierstrassCurve.Affine

namespace MazurProof

abbrev torsionSet (E : WeierstrassCurve ℚ) : Set (E⁄ℚ).Point :=
  AddCommGroup.torsion (E⁄ℚ).Point

def HasFullRationalTorsion (E : WeierstrassCurve ℚ) [E.IsElliptic] (m : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod m →+ (E⁄ℚ).Point, Function.Injective f

def HasRationalPointOfOrder (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  ∃ P : (E⁄ℚ).Point, addOrderOf P = n

def HasTorsionStructure (E : WeierstrassCurve ℚ) [E.IsElliptic] (m n : ℕ) : Prop :=
  ∃ f : ZMod m × ZMod n →+ (E⁄ℚ).Point, Function.Injective f

abbrev ContainsZ2xZn (E : WeierstrassCurve ℚ) [E.IsElliptic] (n : ℕ) : Prop :=
  HasTorsionStructure E 2 n

structure TorsionStructureData (E : WeierstrassCurve ℚ) [E.IsElliptic] where
  m : ℕ
  n : ℕ
  m_pos : 0 < m
  n_pos : 0 < n
  dvd_mn : m ∣ n
  has_structure : HasTorsionStructure E m n
  has_point_order_n : HasRationalPointOfOrder E n
  card_eq : (torsionSet E).ncard = m * n

end MazurProof

end

/- Source: flt@51bbb4f191ad FLT/Assumptions/MazurProof/CyclicOrderReduction.lean and FLT/Assumptions/MazurProof/CyclicExclusion35.lean. -/
section

open scoped WeierstrassCurve.Affine

namespace MazurProof

-- FLT/Assumptions/MazurProof/CyclicOrderReduction.lean, lines 30-45
/--
If `P` has finite additive order `n` and `p ∣ n`, then `(n / p) • P` has
additive order `p`.
-/
theorem exists_point_of_prime_order_of_dvd
    (E : WeierstrassCurve ℚ) [E.IsElliptic] {n p : ℕ}
    (hn : n ≠ 0) (hp : Nat.Prime p) (hpn : p ∣ n)
    (hord : HasRationalPointOfOrder E n) :
    HasRationalPointOfOrder E p := by
  rcases hord with ⟨P, hP⟩
  refine ⟨(n / p) • P, ?_⟩
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hp_le_n : p ≤ n := Nat.le_of_dvd hnpos hpn
  have hdiv_ne : n / p ≠ 0 := (Nat.div_pos hp_le_n hp.pos).ne'
  rw [addOrderOf_nsmul' P hdiv_ne, hP]
  rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd hpn), Nat.div_div_self hpn hn]

-- FLT/Assumptions/MazurProof/CyclicExclusion35.lean, lines 33-59
/-- From a rational point of exact order `35`, the point `7 • P` has order `5`. -/
theorem order35_gives_order5
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 35) :
    HasRationalPointOfOrder E 5 :=
  exists_point_of_prime_order_of_dvd E
    (show (35 : ℕ) ≠ 0 by norm_num)
    (show Nat.Prime 5 by norm_num)
    (show (5 : ℕ) ∣ 35 by norm_num) h

/-- From a rational point of exact order `35`, the point `5 • P` has order `7`. -/
theorem order35_gives_order7
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 35) :
    HasRationalPointOfOrder E 7 :=
  exists_point_of_prime_order_of_dvd E
    (show (35 : ℕ) ≠ 0 by norm_num)
    (show Nat.Prime 7 by norm_num)
    (show (7 : ℕ) ∣ 35 by norm_num) h

/-- A rational point of exact order `35` yields simultaneous rational points of
order `5` and order `7`. -/
theorem order35_gives_orders5_and_7
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (h : HasRationalPointOfOrder E 35) :
    HasRationalPointOfOrder E 5 ∧ HasRationalPointOfOrder E 7 :=
  ⟨order35_gives_order5 E h, order35_gives_order7 E h⟩


end MazurProof

end

open scoped WeierstrassCurve.Affine

theorem solution
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ 35 := by
  intro x hx
  obtain ⟨⟨P, hP⟩, ⟨Q, hQ⟩⟩ := MazurProof.order35_gives_orders5_and_7 E
    ⟨(x : (E⁄ℚ).Point), by rw [AddSubgroup.addOrderOf_coe]; exact hx⟩
  obtain ⟨a, b, _ha, hb, hab⟩ :=
    MazurHuang.exists_X0_five_seven_fiber_point_of_addOrderOf_eq_five_of_eq_seven E P Q hP hQ
  obtain ⟨u, v, hu, huv⟩ :=
    MazurHuang.exists_X0_thirtyFive_point_of_X0_five_seven_fiber hb hab
  exact hu (MazurHuang.eq_zero_of_X0_thirtyFive_equation huv)
