-- Prove2me | solution 1 for GlobalTheory.HL.StdLat.exists_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:12:49.075152+00:00
-- url     : https://prove2.me/submissions/798987cc-c50f-49c9-ab3b-ee08bba2a053

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemPerpSpan
import Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
import Theorems.Thm_GlobalTheory_UnramOrder_algebraMap_mem_iff
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
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.StdLat
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
namespace GlobalTheory.HL.StdLat
theorem _root_.solution (s : Finset E) :
    ∃ c : F, c ≠ 0 ∧ c ∈ 𝒪[F] ∧ ∀ x ∈ s, algebraMap F E c * x ∈ L.O := by
  have := L.free
  have : Module.Finite F E := Module.finite_of_finrank_pos (by rw [L.rank]; omega)
  have h1 : ∀ x : E, ∃ c : F, c ≠ 0 ∧ c ∈ 𝒪[F] ∧ algebraMap F E c * x ∈ L.O := by
    intro x
    have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization
      (R := 𝒪[F]) (nonZeroDivisors 𝒪[F]) x hx
    refine ⟨((m : 𝒪[F]) : F), ?_, (m : 𝒪[F]).2, ?_⟩
    · have := nonZeroDivisors.ne_zero m.2
      exact fun h => this (Subtype.ext h)
    · rw [L.O_def]
      convert hm using 1
      rw [Submonoid.smul_def, Algebra.smul_def]
      rfl
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, Subring.one_mem _, by simp⟩
  | insert a s _ ih =>
    obtain ⟨c, hc, hc', h⟩ := ih
    obtain ⟨d, hd, hd', h'⟩ := h1 a
    refine ⟨c * d, mul_ne_zero hc hd, Subring.mul_mem _ hc' hd', fun x hx => ?_⟩
    rcases Finset.mem_insert.1 hx with rfl | hx
    · rw [map_mul, mul_assoc]
      exact L.O.mul_mem ((UnramOrder.algebraMap_mem_iff L c).2 hc') h'
    · rw [map_mul, mul_comm (algebraMap F E c), mul_assoc]
      exact L.O.mul_mem ((UnramOrder.algebraMap_mem_iff L d).2 hd') (h x hx)
end GlobalTheory.HL.StdLat
