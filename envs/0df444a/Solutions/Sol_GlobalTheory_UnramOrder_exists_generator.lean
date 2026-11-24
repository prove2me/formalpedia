-- Prove2me | solution 1 for GlobalTheory.UnramOrder.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:19:11.657328+00:00
-- url     : https://prove2.me/submissions/fd918b8f-985f-4efa-abc3-baa2c2fc18e7

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
import Theorems.Thm_GlobalTheory_UnramOrder_cj_mem
import Theorems.Thm_GlobalTheory_UnramOrder_exists_int_of_fixed
import Theorems.Thm_GlobalTheory_UnramOrder_exists_eq_mul_of_anti
import Theorems.Thm_GlobalTheory_UnramOrder_exists_mem_sub_cj_ne_zero
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
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.UnramOrder
open IsLocalRing Polynomial
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable [IsNonarchimedeanLocalField F]
namespace GlobalTheory.UnramOrder
theorem _root_.solution [CharZero F] (L : LocE F E) : ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 ∧
    ∀ x ∈ L.O, ∃ b : 𝒪[F], x - L.cj x = algebraMap F E b * (ω - L.cj ω) := by
  have := L.reduced
  have hdisc : ∀ x ∈ L.O, ∃ d : 𝒪[F], (x - L.cj x) ^ 2 = algebraMap F E d := fun x hx =>
    exists_int_of_fixed L (L.O.pow_mem (L.O.sub_mem hx (cj_mem L hx)) 2) (by
      rw [map_pow, map_sub, L.cj_cj]; ring)
  let S : Set 𝒪[F] := {d | ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 ∧ (ω - L.cj ω) ^ 2 = algebraMap F E d}
  have hS : S.Nonempty := by
    obtain ⟨ω, h1, h2⟩ := exists_mem_sub_cj_ne_zero L
    obtain ⟨d, hd⟩ := hdisc ω h1
    exact ⟨d, ω, h1, h2, hd⟩
  obtain ⟨d, ⟨ω, hω, hω0, hd⟩, hmin⟩ := (wellFounded_dvdNotUnit (α := 𝒪[F])).has_min S hS
  refine ⟨ω, hω, hω0, fun x hx => ?_⟩
  obtain ⟨c, hc⟩ := exists_eq_mul_of_anti L (y := x - L.cj x) (z := ω - L.cj ω)
    (by simp [L.cj_cj]) (by simp [L.cj_cj]) hω0
  by_cases hci : c ∈ 𝒪[F]
  · exact ⟨⟨c, hci⟩, hc⟩
  exfalso
  have hc0 : c ≠ 0 := by rintro rfl; exact hci (zero_mem _)
  rcases ValuationRing.isInteger_or_isInteger 𝒪[F] c with ⟨c', rfl⟩ | ⟨c', hc'⟩
  · exact hci c'.2
  have hc'' : (c' : F) = c⁻¹ := hc'
  have h1 : algebraMap F E c * algebraMap F E c⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
  have hx0 : x - L.cj x ≠ 0 := fun h => hω0 (by
    rw [hc] at h
    linear_combination algebraMap F E c⁻¹ * h - (ω - L.cj ω) * h1)
  obtain ⟨e, he⟩ := hdisc x hx
  refine hmin e ⟨x, hx, hx0, he⟩ ⟨?_, c' ^ 2, ?_, ?_⟩
  · rintro rfl
    exact hx0 (IsReduced.eq_zero _ ⟨2, by rw [he]; simp⟩)
  · intro hu
    obtain ⟨v, hv⟩ := ((isUnit_pow_iff two_ne_zero).1 hu).exists_right_inv
    have hv' : (c' : F) * v = 1 := congrArg Subtype.val hv
    rw [hc''] at hv'
    have : c = v := by field_simp at hv'; exact hv'.symm
    exact hci (this ▸ v.2)
  · apply Subtype.ext
    apply algebraMap_inj L
    rw [Subring.coe_mul, Subring.coe_pow, map_mul, map_pow, ← hd, ← he, hc, hc'']
    linear_combination (-(ω - L.cj ω) ^ 2 * (algebraMap F E c * algebraMap F E c⁻¹ + 1)) * h1
end GlobalTheory.UnramOrder
