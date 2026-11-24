-- Prove2me | solution 1 for GlobalTheory.SW.Base.weil_deg_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:24:35.877158+00:00
-- url     : https://prove2.me/submissions/de97b2e3-9b98-4e8f-a8ad-8d75053aa026

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_InhabSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Theorems.Thm_GlobalTheory_SW_Base_I_mem_Hn
import Theorems.Thm_GlobalTheory_SW_Base_thH_deg_zero

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
open GlobalTheory GlobalTheory.SW
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable (Ψ : Finset (E →+* ℂ)) {n N : ℕ}
open GlobalTheory.SW.Base
omit [IsCMField E]
namespace GlobalTheory.SW.Base
theorem _root_.solution (γ : M2 E 0) (φ : Matrix (Fin n) (Fin 0) E → ℂ) : weil Ψ γ φ 0 = φ 0 := by
  have f : ∀ Z z z', hFac Ψ γ Z (n := n) z z' = 1 := fun Z z z' => by simp [hFac, dotProduct]
  have h : ∃ ψ, IsSB ψ ∧ TransH Ψ γ φ ψ :=
    ⟨φ, ⟨1, one_pos, fun _ _ _ i => i.elim0, fun _ _ _ => congrArg φ (Subsingleton.elim _ _)⟩,
      fun Z _ z z' => by rw [f, thH_deg_zero, thH_deg_zero, one_mul]⟩
  have := h.choose_spec.2 _ (I_mem_Hn Ψ) 0 0
  rw [f, thH_deg_zero, thH_deg_zero, one_mul] at this
  rw [weil, dif_pos h, this]
end GlobalTheory.SW.Base
