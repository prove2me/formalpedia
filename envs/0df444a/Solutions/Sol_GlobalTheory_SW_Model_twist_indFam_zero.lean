-- Prove2me | solution 1 for GlobalTheory.SW.Model.twist_indFam_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:10:34.980345+00:00
-- url     : https://prove2.me/submissions/573b875e-22ec-4a45-b735-9fe21f8fc7d7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_FirstCoordinateAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_NotAdmissibleHalfLatticeFamily

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
omit [IsCMField E]
namespace GlobalTheory.SW.Model
theorem _root_.solution {n N R : ℕ} (Λ : Lt E n) :
    twist R (stdL E N) (indFam E n N) Λ 0 = 1 := by
  have h : (∀ ξ ∈ stdL E N, (R : E) • ((0 : Matrix (Fin n) (Fin N) E) *ᵥ ξ) ∈ Λ) ∧
      ∃ s : ℕ, s ≡ 1 [MOD R ^ 2] ∧ ∀ v ∈ stdL E N, (s : E) • v ∈ stdL E N :=
    ⟨fun _ _ => by simp, 1, Nat.ModEq.refl 1, by simp⟩
  unfold twist
  rw [dif_pos h, smul_zero]
  exact if_pos fun _ => Λ.zero_mem
end GlobalTheory.SW.Model
