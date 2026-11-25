-- Prove2me | solution 1 for GlobalTheory.SW.Model.admissible_scaled_lattice_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:13:44.356785+00:00
-- url     : https://prove2.me/submissions/0c3bd62c-f8c1-45e3-abb1-6e9da887686f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily
import Theorems.Thm_GlobalTheory_SW_Model_nat_smul_mem
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
theorem _root_.solution {n N M R : ℕ} (hM : 0 < M) (hR : 0 < R) : admitted M R (divFam E n N R) := by
  classical
  refine ⟨⟨hM, hR⟩, ?_, ?_, ?_, ?_⟩
  · intro h _ Λ _ Λ' _ hm x
    have : ColsIn Λ' ((R : E) • (h * x)) ↔ ColsIn Λ ((R : E) • x) := by
      refine forall_congr' fun a => ?_
      rw [hm, ← Matrix.mul_smul]
      rfl
    exact if_congr this rfl rfl
  · intro Λ _ x hx
    by_contra h; exact hx (if_neg h)
  · intro Λ _ x y hy
    have : ColsIn Λ ((R : E) • (x + (R : E) • y)) ↔ ColsIn Λ ((R : E) • x) := by
      rw [smul_add]
      refine forall_congr' fun a => ?_
      exact Λ.add_mem_iff_left (nat_smul_mem Λ R (nat_smul_mem Λ R (hy a)))
    exact if_congr this rfl rfl
  · intro Λ _ Λ' _ _ x hx hx'
    exact (if_pos hx).trans (if_pos hx').symm
end GlobalTheory.SW.Model
