-- Prove2me | solution 1 for OAI.ComplexCancellation.Rigidity.orbit_constant
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:33:03.205608+00:00
-- url     : https://prove2.me/submissions/72c2ada8-cb0f-4aa0-bea6-7596e6831b53

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Rigidity.lean:L73-L121
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.Rigidity.orbit_constant. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Theorems.Thm_OAI_ComplexCancellation_Rigidity_orbit_coprime
import Theorems.Thm_OAI_ComplexCancellation_Rigidity_radical_orbit_bound

-- ---- from OAI.Algebra.AffineCancellation.Rigidity ----
namespace OAI

noncomputable section

/-! Polynomial orbit rigidity from the Mason–Stothers theorem. -/
namespace ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain

variable {k : Type*} [Field k]

/-- A nonsquare obstruction over the coefficient field forces constant polynomial orbits. -/
theorem orbit_constant [CharZero k] {a d u n : k[X]}
    (ha : a ≠ 0) (hd : d ≠ 0) (hu : u ≠ 0) (hn : n ≠ 0)
    (hdeg : n.natDegree ≤ 1) (heq : d ^ 2 + a ^ 2 * u ^ 3 = n)
    (hns : ∀ z : k, z ^ 2 ≠ -(u.coeff 0) ^ 3) :
    a = C (a.coeff 0) ∧ d = C (d.coeff 0) ∧ u = C (u.coeff 0) := by
  classical
  have hdn : d ^ 2 ≠ 0 := pow_ne_zero _ hd
  have haun : a ^ 2 * u ^ 3 ≠ 0 := mul_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hu)
  have hp := Polynomial.abc hdn haun (neg_ne_zero.mpr hn)
    (orbit_coprime hn hdeg heq) (by rw [heq]; ring)
  have hda : d.natDegree = a.natDegree ∧ u.natDegree = 0 := by
    rcases hp with hp | hp
    · have hb := radical_orbit_bound a d u n
      have h1 := hp.1.trans hb
      have h2 := hp.2.1.trans hb
      rw [natDegree_pow] at h1
      rw [natDegree_mul (pow_ne_zero _ ha) (pow_ne_zero _ hu),
        natDegree_pow, natDegree_pow] at h2
      omega
    · have h1 := derivative_eq_zero.mp hp.1
      have h2 := derivative_eq_zero.mp hp.2.1
      rw [natDegree_pow] at h1
      rw [natDegree_mul (pow_ne_zero _ ha) (pow_ne_zero _ hu),
        natDegree_pow, natDegree_pow] at h2
      omega
  have hd0 : d.natDegree = 0 := by
    by_contra hdpos
    have hlt : n.natDegree < 2 * d.natDegree := by omega
    have hc := congrArg (fun p : k[X] => p.coeff (2 * d.natDegree)) heq
    rw [coeff_add, coeff_eq_zero_of_natDegree_lt hlt] at hc
    have hcd : (d ^ 2).coeff (2 * d.natDegree) = d.leadingCoeff ^ 2 := by
      rw [← natDegree_pow d 2, coeff_natDegree, leadingCoeff_pow]
    have hcau : (a ^ 2 * u ^ 3).coeff (2 * d.natDegree) =
        a.leadingCoeff ^ 2 * (u.coeff 0) ^ 3 := by
      have hdegau : (a ^ 2 * u ^ 3).natDegree = 2 * d.natDegree := by
        rw [natDegree_mul (pow_ne_zero _ ha) (pow_ne_zero _ hu),
          natDegree_pow, natDegree_pow, hda.2, ← hda.1]
        omega
      rw [← hdegau, coeff_natDegree, leadingCoeff_mul, leadingCoeff_pow,
        leadingCoeff_pow]
      congr 2
      exact congrArg (fun m : ℕ => u.coeff m) hda.2
    rw [hcd, hcau] at hc
    apply hns (d.leadingCoeff / a.leadingCoeff)
    rw [div_pow, div_eq_iff (pow_ne_zero 2 (leadingCoeff_ne_zero.mpr ha))]
    linear_combination hc
  exact ⟨eq_C_of_natDegree_eq_zero (hda.1.symm.trans hd0),
    eq_C_of_natDegree_eq_zero hd0, eq_C_of_natDegree_eq_zero hda.2⟩

end ComplexCancellation.Rigidity

namespace ComplexCancellation.Rigidity

end ComplexCancellation.Rigidity

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Rigidity
open Polynomial UniqueFactorizationMonoid UniqueFactorizationDomain


theorem solution : type_of% @_root_.OAI.ComplexCancellation.Rigidity.orbit_constant := @_root_.OAI.ComplexCancellation.Rigidity.orbit_constant
