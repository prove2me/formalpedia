-- Prove2me | solution 1 for GlobalTheory.UnramOrder.exists_mem_sub_cj_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:08:24.196879+00:00
-- url     : https://prove2.me/submissions/f1377492-7c0d-415a-be53-ff73e8d64ab4

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_inj
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
namespace GlobalTheory.UnramOrder
theorem _root_.solution [CharZero F] (L : LocE F E) :
    ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, L.cj x ≠ x := by
    by_contra h
    push Not at h
    have hb : Function.Bijective (Algebra.linearMap F E) :=
      ⟨algebraMap_inj L, fun x => (L.cj_fix x).1 (h x)⟩
    have := (LinearEquiv.ofBijective _ hb).finrank_eq
    rw [L.rank, Module.finrank_self] at this
    omega
  have key : ∀ (z : E) (d : 𝒪[F]), z ≠ 0 → L.cj z = -z → z ^ 2 = algebraMap F E d →
      ∃ ω ∈ L.O, ω - L.cj ω ≠ 0 := by
    intro z d hz0 hz hd
    refine ⟨z, (L.O_def z).2 (IsIntegral.of_pow two_pos ?_), fun h => hz0 ?_⟩
    · rw [hd]; exact isIntegral_algebraMap (R := 𝒪[F]) (A := E) (x := d)
    · have h2 : algebraMap F E 2⁻¹ * 2 = 1 := by
        rw [← map_ofNat (algebraMap F E) 2, ← map_mul, inv_mul_cancel₀ two_ne_zero, map_one]
      rw [hz] at h
      linear_combination algebraMap F E 2⁻¹ * h - z * h2
  have hz0 : x - L.cj x ≠ 0 := fun h => hx (sub_eq_zero.1 h).symm
  have hz : L.cj (x - L.cj x) = -(x - L.cj x) := by simp [L.cj_cj]
  set z := x - L.cj x
  obtain ⟨d, hd⟩ := (L.cj_fix (z ^ 2)).1 (by simp [hz])
  by_cases hd0 : d = 0
  · exact key z 0 hz0 hz (by rw [← hd, hd0]; rfl)
  rcases ValuationRing.isInteger_or_isInteger 𝒪[F] d with ⟨d', rfl⟩ | ⟨d', hd'⟩
  · exact key z d' hz0 hz hd.symm
  · have h1 : algebraMap F E d * algebraMap F E d⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hd0, map_one]
    refine key (algebraMap F E d⁻¹ * z) d' (fun h => hz0 ?_) (by
      rw [map_mul, AlgEquiv.commutes, hz, mul_neg]) ?_
    · linear_combination algebraMap F E d * h - z * h1
    · have : (d' : F) = d⁻¹ := hd'
      rw [this, mul_pow, ← hd]
      linear_combination algebraMap F E d⁻¹ * h1
end GlobalTheory.UnramOrder
