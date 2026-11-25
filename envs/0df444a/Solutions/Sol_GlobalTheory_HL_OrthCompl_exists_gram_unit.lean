-- Prove2me | solution 1 for GlobalTheory.HL.OrthCompl.exists_gram_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:47:33.396557+00:00
-- url     : https://prove2.me/submissions/11cf797c-0c8a-4178-bc1e-0c253e89df29

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_OrthonormalBasisAndOneOrbit
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsNormOneOrthTriple
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.OrthCompl
variable {o E : Type*} [CommRing o] [IsLocalRing o] [CommRing E]
namespace GlobalTheory.HL.OrthCompl
theorem _root_.solution (S : Subring E) (σ : E →+* E) (φ : o →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hσS : ∀ x ∈ S, σ x ∈ S) (hN : ∀ x ∈ S, ∃ c, x * σ x = φ c)
    (hτ : ∃ τ ∈ S, τ + σ τ = 1) {y0 y1 y2 c0 c1 c2 : E} (hy0 : y0 ∈ S) (hy1 : y1 ∈ S)
    (hy2 : y2 ∈ S) (hc0 : c0 ∈ S) (hc1 : c1 ∈ S) (hc2 : c2 ∈ S)
    (h : y0 * σ c0 + y1 * σ c1 + y2 * σ c2 = 1) :
    ∃ d0 ∈ S, ∃ d1 ∈ S, ∃ d2 ∈ S, ∃ w : o, IsUnit w ∧
      (y0 * σ y0 + y1 * σ y1 + y2 * σ y2) * (d0 * σ d0 + d1 * σ d1 + d2 * σ d2)
        - (y0 * σ d0 + y1 * σ d1 + y2 * σ d2) * (d0 * σ y0 + d1 * σ y1 + d2 * σ y2) = φ w := by
  obtain ⟨n0, hn0⟩ := hN y0 hy0
  obtain ⟨n1, hn1⟩ := hN y1 hy1
  obtain ⟨n2, hn2⟩ := hN y2 hy2
  have hu : ∀ a b : o, ¬ IsUnit a → IsUnit b → IsUnit (a - b) := fun a b ha hb => by
    by_contra hab
    have h1 : a ∈ IsLocalRing.maximalIdeal o := ha
    have h2 : a - b ∈ IsLocalRing.maximalIdeal o := hab
    have h3 := Ideal.sub_mem _ h1 h2
    rw [sub_sub_cancel] at h3
    exact h3 hb
  by_cases ha : IsUnit (n0 + n1 + n2)
  · by_cases h0 : IsUnit (n1 + n2)
    · refine ⟨1, S.one_mem, 0, S.zero_mem, 0, S.zero_mem, n1 + n2, h0, ?_⟩
      simp only [map_one, map_zero, map_add, ← hn1, ← hn2]
      ring
    by_cases h1 : IsUnit (n0 + n2)
    · refine ⟨0, S.zero_mem, 1, S.one_mem, 0, S.zero_mem, n0 + n2, h1, ?_⟩
      simp only [map_one, map_zero, map_add, ← hn0, ← hn2]
      ring
    have u0 : IsUnit n0 := by
      have := (hu _ _ h0 ha).neg
      rwa [show -(n1 + n2 - (n0 + n1 + n2)) = n0 by ring] at this
    have u1 : IsUnit n1 := by
      have := (hu _ _ h1 ha).neg
      rwa [show -(n0 + n2 - (n0 + n1 + n2)) = n1 by ring] at this
    obtain ⟨τ, hτS, hτ⟩ := hτ
    obtain ⟨t, ht⟩ := hN τ hτS
    refine ⟨1, S.one_mem, τ * σ y0 * y1, S.mul_mem (S.mul_mem hτS (hσS _ hy0)) hy1, 0, S.zero_mem,
      ((n1 + n2) + (n0 + n2) * (t * n0 * n1)) - n0 * n1, hu _ _ ?_ (u0.mul u1), ?_⟩
    · have g0 : n1 + n2 ∈ IsLocalRing.maximalIdeal o := h0
      have g1 : n0 + n2 ∈ IsLocalRing.maximalIdeal o := h1
      exact Ideal.add_mem _ g0 (Ideal.mul_mem_right _ _ g1)
    · simp only [map_one, map_zero, map_add, map_sub, map_mul, hσ, ← hn0, ← hn1, ← hn2, ← ht]
      linear_combination (-(y0 * σ y0 * (y1 * σ y1))) * hτ
  · obtain ⟨m0, hm0⟩ := hN c0 hc0
    obtain ⟨m1, hm1⟩ := hN c1 hc1
    obtain ⟨m2, hm2⟩ := hN c2 hc2
    have h' := congrArg σ h
    simp only [map_add, map_mul, hσ, map_one] at h'
    refine ⟨c0, hc0, c1, hc1, c2, hc2, (n0 + n1 + n2) * (m0 + m1 + m2) - 1,
      hu _ _ (fun hh => ha (isUnit_of_mul_isUnit_left hh)) isUnit_one, ?_⟩
    simp only [map_one, map_add, map_sub, map_mul, ← hn0, ← hn1, ← hn2, ← hm0, ← hm1, ← hm2]
    rw [h]
    linear_combination -h'
end GlobalTheory.HL.OrthCompl
