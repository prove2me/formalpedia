-- Prove2me | solution 1 for OAI.ComplexCancellation.LND.cancel_factor_locallyNilpotent
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:37:08.178419+00:00
-- url     : https://prove2.me/submissions/e71a53e6-ce3e-4096-bfb6-ac943978733f

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Order.lean:L45-L62
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.LND.cancel_factor_locallyNilpotent. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order

-- ---- from OAI.Algebra.AffineCancellation.Orbit ----
namespace OAI

noncomputable section

/-! Orbit polynomials and exponentiation of locally nilpotent derivations. -/
namespace ComplexCancellation.LND
open Polynomial

variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

lemma orbit_constant_iff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    orbit D hD r = C r ↔ D r = 0 := by
  constructor
  · intro h
    simpa using congrArg (fun p : R[X] => p.coeff 1) h
  · intro h
    ext n
    cases n with
    | zero => simp
    | succ n => simp [Function.iterate_succ_apply, h]

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Kernel ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

lemma inv_factorial_succ (n : ℕ) :
    ((n + 1 : ℕ) : k) * ((n + 1).factorial : k)⁻¹ = (n.factorial : k)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have hn : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

lemma derivative_orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).derivative = orbit D hD (D r) := by
  ext n
  rw [Polynomial.coeff_derivative, orbit_coeff, orbit_coeff,
    ← Function.iterate_succ_apply]
  rw [mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_factorial_succ]

end ComplexCancellation.LND
namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R] [IsDomain R]

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

end ComplexCancellation.LND

end

end OAI

-- ---- from OAI.Algebra.AffineCancellation.Order ----
namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R] [Algebra k R]

omit [CharZero k] [IsDomain R] in
lemma orbit_ne_zero (D : Derivation k R R) (hD : LocallyNilpotent D) {r : R} (hr : r ≠ 0) :
    orbit D hD r ≠ 0 := by
  intro h
  apply hr
  simpa using congrArg (fun f : R[X] => f.coeff 0) h

lemma order_mul (D : Derivation k R R) (hD : LocallyNilpotent D) {r s : R}
    (hr : r ≠ 0) (hs : s ≠ 0) : order D hD (r*s) = order D hD r + order D hD s := by
  exact (congrArg natDegree (orbit_mul D hD r s)).trans
    (natDegree_mul (orbit_ne_zero D hD hr) (orbit_ne_zero D hD hs))

omit [CharZero k] [IsDomain R] in
lemma order_zero_iff (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    order D hD r = 0 ↔ D r = 0 := by
  rw [← orbit_constant_iff D hD r]
  constructor
  · intro hr
    simpa using eq_C_of_natDegree_eq_zero hr
  · intro h
    simp only [order, h, natDegree_C]

lemma order_derivative (D : Derivation k R R) (hD : LocallyNilpotent D) {r : R}
    (hr : D r ≠ 0) : order D hD (D r) + 1 = order D hD r := by
  let : CharZero R := Algebra.charZero_of_charZero k R
  have hpos : 0 < order D hD r := Nat.pos_of_ne_zero (mt (order_zero_iff D hD r).mp hr)
  change (orbit D hD (D r)).natDegree+1 = _
  rw [← derivative_orbit, natDegree_derivative]
  change order D hD r - 1 + 1 = order D hD r
  omega

/-- Dividing a locally nilpotent derivation by a nonzero common factor still
produces a locally nilpotent derivation, even if the factor is not invariant. -/
lemma cancel_factor_locallyNilpotent {S : Type*} [CommRing S] [Algebra k S]
    (f : S →ₐ[k] R) (hf : Function.Injective f)
    (D : Derivation k R R) (hD : LocallyNilpotent D)
    (E : Derivation k S S) {c : R} (hc : c ≠ 0)
    (h : ∀ r : S, D (f r) = c * f (E r)) : LocallyNilpotent E := by
  intro r
  induction hn : order D hD (f r) using Nat.strong_induction_on generalizing r with
  | h n ih =>
    by_cases her : E r = 0
    · exact ⟨1, her⟩
    · have hfer : f (E r) ≠ 0 := by simpa only [map_zero] using hf.ne her
      have hdr : D (f r) ≠ 0 := by rw [h]; exact mul_ne_zero hc hfer
      have ho := order_derivative D hD hdr
      rw [h, order_mul D hD hc hfer, hn] at ho
      obtain ⟨m, hm⟩ := ih (order D hD (f (E r))) (by omega) (E r) rfl
      exact ⟨m+1, by simpa only [Function.iterate_succ_apply] using hm⟩

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R S : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [CommRing S] [Algebra k S] [Algebra k R]
end ComplexCancellation.LND

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.LND
open Polynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.LND.cancel_factor_locallyNilpotent := @_root_.OAI.ComplexCancellation.LND.cancel_factor_locallyNilpotent
