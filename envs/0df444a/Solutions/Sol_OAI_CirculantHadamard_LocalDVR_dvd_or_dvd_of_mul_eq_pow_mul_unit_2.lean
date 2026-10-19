-- Prove2me | solution 2 for OAI.CirculantHadamard.LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:24:30.55207+00:00
-- url     : https://prove2.me/submissions/603c5f5f-bbcc-4d23-9410-635289aa1ec9

-- Generated from openai/math@1581d4c lean/OAI/LinearAlgebra/CirculantHadamard/LocalDVR.lean:L82-L104
-- (upload_full_project.md Phase 4): solution for node OAI.CirculantHadamard.LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR

-- ---- from OAI.LinearAlgebra.CirculantHadamard.LocalDVR ----
namespace OAI

universe uR

/-!
# Principal maximal ideals and local factor divisibility

A nonzero principal maximal ideal in a Noetherian local domain gives a DVR
and uniformizer factorizations. Its canonical additive valuation, valued in
`ℕ∞`, splits a product of a prime power and a unit.
-/

noncomputable section

namespace CirculantHadamard.LocalDVR

open IsLocalRing IsDiscreteValuationRing

section PrincipalMaximalIdeal

variable {R : Type uR} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]

end PrincipalMaximalIdeal

section Valuation

variable {R : Type uR} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

private theorem finite_add_eq {a b : ℕ∞} {N : ℕ} (h : a + b = (N : ℕ∞)) :
    ∃ m n : ℕ, a = (m : ℕ∞) ∧ b = (n : ℕ∞) ∧ m + n = N := by
  have ha : a ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_right zero_le
  have hb : b ≤ (N : ℕ∞) := by
    rw [← h]
    exact le_add_of_nonneg_left zero_le
  obtain ⟨m, hm, _⟩ := ENat.le_natCast_iff.mp ha
  obtain ⟨n, hn, _⟩ := ENat.le_natCast_iff.mp hb
  refine ⟨m, n, hm, hn, ?_⟩
  rw [hm, hn, ← Nat.cast_add] at h
  exact_mod_cast h

/-- If the valuation of a product is at least twice that of `p`, one factor
is divisible by `p`. The value of `p` is allowed to be ramified. -/
theorem dvd_or_dvd_of_mul_eq_pow_mul_unit {p x y b : R} {D e : ℕ}
    (_hp : p ≠ 0) (_hD : 0 < D) (hpval : addVal R p = (D : ℕ∞))
    (he : 2 ≤ e) (hb : IsUnit b) (hxy : x * y = p ^ e * b) :
    p ∣ x ∨ p ∣ y := by
  have hv := congrArg (addVal R) hxy
  rw [addVal_mul, addVal_mul, addVal_pow, hpval,
    addVal_eq_zero_iff.mpr hb, add_zero] at hv
  have hv' : addVal R x + addVal R y = ((e * D : ℕ) : ℕ∞) := by
    simpa only [nsmul_eq_mul, Nat.cast_mul] using hv
  obtain ⟨m, n, hm, hn, hmn⟩ := finite_add_eq hv'
  have heD : 2 * D ≤ e * D := Nat.mul_le_mul_right D he
  have hsplit : D ≤ m ∨ D ≤ n := by omega
  rcases hsplit with hx | hy
  · left
    apply addVal_le_iff_dvd.mp
    rw [hpval, hm]
    exact_mod_cast hx
  · right
    apply addVal_le_iff_dvd.mp
    rw [hpval, hn]
    exact_mod_cast hy

end Valuation

end CirculantHadamard.LocalDVR

end

end OAI

-- ---- platform node ----
open OAI OAI.CirculantHadamard OAI.CirculantHadamard.LocalDVR
open IsLocalRing IsDiscreteValuationRing


theorem solution.{uR} : type_of% @_root_.OAI.CirculantHadamard.LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit.{uR} := @_root_.OAI.CirculantHadamard.LocalDVR.dvd_or_dvd_of_mul_eq_pow_mul_unit.{uR}
