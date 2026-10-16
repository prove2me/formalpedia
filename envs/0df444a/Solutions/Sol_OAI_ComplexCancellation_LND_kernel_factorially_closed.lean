-- Prove2me | solution 1 for OAI.ComplexCancellation.LND.kernel_factorially_closed
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:35:51.167336+00:00
-- url     : https://prove2.me/submissions/9ff59a48-bdad-4850-84f2-17e9ce587362

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/Kernel.lean:L25-L48
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.LND.kernel_factorially_closed. The node keeps its source
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

lemma kernel_factorially_closed [IsDomain R] (D : Derivation k R R)
    (hD : LocallyNilpotent D) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : D (r * s) = 0) : D r = 0 ∧ D s = 0 := by
  have hor : orbit D hD r ≠ 0 := by
    intro h
    have := congrArg (fun p : R[X] => p.coeff 0) h
    simp at this
    exact hr this
  have hos : orbit D hD s ≠ 0 := by
    intro h
    have := congrArg (fun p : R[X] => p.coeff 0) h
    simp at this
    exact hs this
  have hp := (orbit_constant_iff D hD (r*s)).mpr hrs
  rw [orbit_mul] at hp
  have hn := congrArg Polynomial.natDegree hp
  rw [natDegree_mul hor hos, natDegree_C] at hn
  have hnr : (orbit D hD r).natDegree = 0 := by omega
  have hns : (orbit D hD s).natDegree = 0 := by omega
  constructor
  · apply (orbit_constant_iff D hD r).mp
    simpa using eq_C_of_natDegree_eq_zero hnr
  · apply (orbit_constant_iff D hD s).mp
    simpa using eq_C_of_natDegree_eq_zero hns

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

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.LND
open Polynomial


theorem solution : type_of% @_root_.OAI.ComplexCancellation.LND.kernel_factorially_closed := @_root_.OAI.ComplexCancellation.LND.kernel_factorially_closed
