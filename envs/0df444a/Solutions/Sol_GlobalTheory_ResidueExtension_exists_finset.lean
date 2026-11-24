-- Prove2me | solution 1 for GlobalTheory.ResidueExtension.exists_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:48:15.600329+00:00
-- url     : https://prove2.me/submissions/a658603b-9fc9-4ae0-96c9-d26b9bb019df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
import Theorems.Thm_GlobalTheory_ResidueExtension_exists_step

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
open GlobalTheory.ResidueExtension
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Ω : Type} [Field Ω]
namespace GlobalTheory.ResidueExtension
theorem _root_.solution (r : O →+* Ω) (hr : RingHom.ker r = maximalIdeal O) (S : Finset Ω) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsDiscreteValuationRing B)
      (j : O →+* B) (r' : B →+* Ω), Function.Injective j ∧ r'.comp j = r ∧
      RingHom.ker r' = maximalIdeal B ∧ ∀ a ∈ S, a ∈ Set.range r' := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨O, _, ‹_›, ‹_›, RingHom.id O, r, Function.injective_id, rfl, hr, by simp⟩
  | insert a S _ ih =>
    obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := ih
    obtain ⟨B', _, _, _, j', r'', h1', h2', h3', h4'⟩ := exists_step r' h3 a
    refine ⟨B', _, ‹_›, ‹_›, j'.comp j, r'', h1'.comp h1,
      by rw [← RingHom.comp_assoc, h2', h2], h3', fun b hb => ?_⟩
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact h4'
    · obtain ⟨y, rfl⟩ := h4 b hb
      exact ⟨j' y, RingHom.congr_fun h2' y⟩
end GlobalTheory.ResidueExtension
