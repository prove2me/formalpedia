-- Prove2me | solution 1 for GlobalTheory.SW.Model.admissible_indicator_functions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:15:33.52363+00:00
-- url     : https://prove2.me/submissions/930121f3-d8c1-4ad9-9e15-673d81efebbb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Theorems.Thm_GlobalTheory_SW_Model_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_Model_mem_of_coprime
import Theorems.Thm_GlobalTheory_SW_Base_mem_of_coprime
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField
open scoped ComplexConjugate ComplexOrder
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Model
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution {n N M R : ℕ} (hM : 0 < M) (hR : 0 < R) : admitted M R (indFam E n N) := by
  refine ⟨⟨hM, hR⟩, ?_, ?_, ?_, ?_⟩
  · intro h _ Λ _ Λ' _ hm x
    have : ColsIn Λ' (h * x) ↔ ColsIn Λ x := by
      refine forall_congr' fun a => ?_
      rw [hm]
      rfl
    classical exact if_congr this rfl rfl
  · intro Λ _ x hx a
    have : ColsIn Λ x := by
      by_contra h; exact hx (if_neg h)
    exact nat_smul_mem Λ R (this a)
  · intro Λ _ x y hy
    have : ColsIn Λ (x + (R : E) • y) ↔ ColsIn Λ x := by
      refine forall_congr' fun a => ?_
      exact Λ.add_mem_iff_left (nat_smul_mem Λ R (hy a))
    classical exact if_congr this rfl rfl
  · rintro Λ _ Λ' _ ⟨s, _, hs, h1, h2⟩ x hx hx'
    have hsR : s.Coprime R := Nat.Coprime.coprime_mul_right_right hs
    have : ColsIn Λ x ↔ ColsIn Λ' x :=
      forall_congr' fun a => ⟨fun h => mem_of_coprime Λ' hsR (h1 _ h) (hx' a),
        fun h => mem_of_coprime Λ hsR (h2 _ h) (hx a)⟩
    classical exact if_congr this rfl rfl
end GlobalTheory.SW.Model
