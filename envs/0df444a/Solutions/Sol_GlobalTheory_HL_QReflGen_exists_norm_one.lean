-- Prove2me | solution 1 for GlobalTheory.HL.QReflGen.exists_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:02:07.786478+00:00
-- url     : https://prove2.me/submissions/12a44fee-0ae1-4443-b5d7-fd603a62a2ce

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsometriesFixingSubspaceLeQuasiReflectionClosure
import Theorems.Thm_GlobalTheory_HL_QReflGen_nontriv
import Theorems.Thm_GlobalTheory_HL_QReflGen_exists_skew
import Theorems.Thm_GlobalTheory_HL_QReflGen_quad_finite
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.MainNotions.S.Loc.Pt.cast_blocks



set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.QReflGen
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
namespace GlobalTheory.HL.QReflGen
theorem _root_.solution [CharZero F] (L : LocE F E) (t s : E) (ht : IsUnit t) (htc : L.cj t = t) :
    ∃ u : E, u * L.cj u = 1 ∧ IsUnit (t - L.cj u * s) ∧
      IsUnit ((t - L.cj u * s) + L.cj (t - L.cj u * s)) := by
  haveI := nontriv L
  obtain ⟨δ, D, hD, hδ, hδ2⟩ := exists_skew L
  obtain ⟨τ, rfl⟩ := (L.cj_fix t).1 htc
  have hτ : τ ≠ 0 := by rintro rfl; simp at ht
  obtain ⟨A, hA⟩ := (L.cj_fix (s + L.cj s)).1 (by simp [L.cj_cj, add_comm])
  obtain ⟨B, hB⟩ := (L.cj_fix (δ * (s - L.cj s))).1 (by simp [L.cj_cj, hδ]; ring)
  obtain ⟨N, hN⟩ := (L.cj_fix (s * L.cj s)).1 (by simp [L.cj_cj, mul_comm])
  have inj : Function.Injective (algebraMap F E) := (algebraMap F E).injective
  have hrel : D * A ^ 2 - B ^ 2 = 4 * D * N := by
    apply inj
    simp only [map_sub, map_mul, map_pow, map_ofNat, hA, hB, hN, ← hδ2]
    ring
  have f1 := quad_finite (1 : F) 0 (-D) (by simp)
  have f2 := quad_finite (A - 2 * τ) (-2 * B) (D * (A + 2 * τ)) (by
    rintro ⟨h1, -, h3⟩
    have h4 := (mul_eq_zero.1 h3).resolve_left hD
    apply hτ
    linear_combination (1 / 4 : F) * (h4 - h1))
  have f3 := quad_finite (τ * A - (τ ^ 2 + N)) (-2 * τ * B) (D * (τ * A + (τ ^ 2 + N))) (by
    rintro ⟨h1, h2, h3⟩
    have h4 := (mul_eq_zero.1 h3).resolve_left hD
    have hA0 : A = 0 := by
      have : τ * A = 0 := by linear_combination (1 / 2 : F) * (h4 + h1)
      exact (mul_eq_zero.1 this).resolve_left hτ
    have hB0 : B = 0 := by
      have : τ * B = 0 := by linear_combination (-1 / 2 : F) * h2
      exact (mul_eq_zero.1 this).resolve_left hτ
    have hN0 : N = 0 := by
      have : D * N = 0 := by rw [hA0, hB0] at hrel; linear_combination (-1 / 4 : F) * hrel
      exact (mul_eq_zero.1 this).resolve_left hD
    apply hτ
    have : τ ^ 2 = 0 := by rw [hA0, hN0] at h1; linear_combination -h1
    exact pow_eq_zero_iff (two_ne_zero) |>.1 this)
  obtain ⟨r, hr⟩ := ((f1.union f2).union f3).exists_notMem
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hr
  obtain ⟨⟨r1, r2⟩, r3⟩ := hr
  have r1' : r ^ 2 - D ≠ 0 := fun h => r1 (by linear_combination h)
  set e : F := (r ^ 2 - D)⁻¹ with he
  have he1 : e * (r ^ 2 - D) = 1 := inv_mul_cancel₀ r1'
  have he2 : algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) = 1 := by
    rw [hδ2, ← map_pow, ← map_sub, ← map_mul, he1, map_one]
  set u : E := algebraMap F E e * (algebraMap F E r + δ) ^ 2 with hu
  have hcu : L.cj u = algebraMap F E e * (algebraMap F E r - δ) ^ 2 := by
    simp [hu, hδ, sub_eq_add_neg]
  have huu : u * L.cj u = 1 := by
    rw [hcu, hu]
    linear_combination (algebraMap F E e * (algebraMap F E r ^ 2 - δ * δ) + 1) * he2
  have hT : L.cj u * s + u * L.cj s = algebraMap F E (e * ((r ^ 2 + D) * A - 2 * r * B)) := by
    rw [hcu, hu]
    simp only [map_sub, map_add, map_mul, map_pow, map_ofNat, hA, hB, ← hδ2]
    ring
  have hcb : L.cj (algebraMap F E τ - L.cj u * s) = algebraMap F E τ - u * L.cj s := by
    simp [L.cj_cj]
  clear_value u
  refine ⟨u, huu, ?_, ?_⟩
  · have : (algebraMap F E τ - L.cj u * s) * (algebraMap F E τ - u * L.cj s) =
        algebraMap F E (τ ^ 2 + N - τ * (e * ((r ^ 2 + D) * A - 2 * r * B))) := by
      rw [map_sub, map_add, map_mul (algebraMap F E), ← hT, hN, map_pow]
      linear_combination s * L.cj s * huu
    refine isUnit_of_mul_isUnit_left (y := algebraMap F E τ - u * L.cj s) ?_
    rw [this]
    refine (IsUnit.mk0 _ fun h => r3 ?_).map _
    linear_combination (-(r ^ 2 - D)) * h - τ * ((r ^ 2 + D) * A - 2 * r * B) * he1
  · have : (algebraMap F E τ - L.cj u * s) + (algebraMap F E τ - u * L.cj s) =
        algebraMap F E (2 * τ - (e * ((r ^ 2 + D) * A - 2 * r * B))) := by
      rw [map_sub, map_mul (algebraMap F E), ← hT, map_ofNat]
      ring
    rw [hcb, this]
    refine (IsUnit.mk0 _ fun h => r2 ?_).map _
    linear_combination (-(r ^ 2 - D)) * h - ((r ^ 2 + D) * A - 2 * r * B) * he1
end GlobalTheory.HL.QReflGen
