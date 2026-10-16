-- Prove2me | solution 1 for OAI.ComplexCancellation.RationalSlice.constant_fraction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T21:05:44.802985+00:00
-- url     : https://prove2.me/submissions/4c8c2035-a621-4e75-89b6-acd0c8b87c51

-- Generated from openai/math@1581d4c lean/OAI/Algebra/AffineCancellation/RationalSlice.lean:L62-L77
-- (upload_full_project.md Phase 4): solution for node OAI.ComplexCancellation.RationalSlice.constant_fraction. The node keeps its source
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
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice

-- ---- from OAI.Algebra.AffineCancellation.RationalSlice ----
namespace OAI

noncomputable section

namespace ComplexCancellation.RationalSlice
open DifferentialSlice FractionDerivation
variable {k R K : Type*} [Field k] [CharZero k] [CommRing R] [IsDomain R]
  [Algebra k R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K]

omit [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  [Algebra k K] [IsScalarTower k R K] [CharZero k] in
lemma last_nonzero (D : Derivation k R R) {r : R} (hr : r ≠ 0)
    (h : ∃ m : ℕ, (D : R → R)^[m] r = 0) :
    ∃ n : ℕ, (D : R → R)^[n] r ≠ 0 ∧ D ((D : R → R)^[n] r) = 0 := by
  obtain ⟨m, hm⟩ := h
  induction m generalizing r with
  | zero => exact (hr hm).elim
  | succ m ih =>
    by_cases hdr : D r = 0
    · exact ⟨0, hr, hdr⟩
    · rw [Function.iterate_succ_apply] at hm
      obtain ⟨n, hn, hdn⟩ := ih hdr hm
      exact ⟨n+1, by simpa only [Function.iterate_succ_apply] using hn,
        by simpa only [Function.iterate_succ_apply] using hdn⟩

omit [CharZero k] [CharZero K] in
lemma iterate_constant_mul (D : Derivation k K K) {c : K} (hc : D c = 0) (r : K) (n : ℕ) :
    (D : K → K)^[n] (c * r) = c * (D : K → K)^[n] r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Derivation.leibniz, hc,
      smul_zero, add_zero, smul_eq_mul, Function.iterate_succ_apply']

omit [CharZero k] [CharZero K] in
lemma constant_fraction (D : Derivation k R R) (hD : LND.LocallyNilpotent D)
    {c : K} (hc : extend D c = 0) :
    ∃ a b : R, D a = 0 ∧ D b = 0 ∧ b ≠ 0 ∧ algebraMap R K a / algebraMap R K b = c := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective R c
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨n, hn, hdn⟩ := last_nonzero D hb0 (hD b)
  have hbK : algebraMap R K b ≠ 0 := by simpa using (IsFractionRing.injective R K).ne hb0
  have hz : c * algebraMap R K b = algebraMap R K a := by rw [← hab]; exact div_mul_cancel₀ _ hbK
  have he := congrArg (fun z : K => (extend D : K → K)^[n] z) hz
  rw [iterate_constant_mul _ hc, iterate_algebraMap, iterate_algebraMap] at he
  refine ⟨(D : R → R)^[n] a, (D : R → R)^[n] b, ?_, hdn, hn, ?_⟩
  · apply IsFractionRing.injective R K
    rw [map_zero, ← extend_algebraMap, ← he, Derivation.leibniz, hc,
      extend_algebraMap, hdn, map_zero, smul_zero, smul_zero, add_zero]
  · rw [← he, mul_div_cancel_right₀ _ (by simpa using (IsFractionRing.injective R K).ne hn)]

end ComplexCancellation.RationalSlice

end

end OAI

-- ---- platform node ----
open OAI OAI.ComplexCancellation OAI.ComplexCancellation.RationalSlice
open DifferentialSlice FractionDerivation


theorem solution : type_of% @_root_.OAI.ComplexCancellation.RationalSlice.constant_fraction := @_root_.OAI.ComplexCancellation.RationalSlice.constant_fraction
