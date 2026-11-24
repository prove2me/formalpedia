-- Prove2me | solution 1 for GlobalTheory.HomothetyLatSum.term_out_mulQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:37:21.948587+00:00
-- url     : https://prove2.me/submissions/117bc33d-d4ad-4428-957a-647ea62fb4c1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DTermOrigin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdNormSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomothetyLatSum
import Theorems.Thm_GlobalTheory_CMVal_TermUnit_term_unit_and_norm
import Theorems.Thm_GlobalTheory_CMVal_term_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.DeformedSum
open GlobalTheory GlobalTheory.HomothetyLatSum
variable {E : Type} [Field E] [NumberField E]
variable {I : Type} [Fintype I]
namespace GlobalTheory.HomothetyLatSum
theorem _root_.solution [IsCMField E] {φ : I → E →+* ℂ} (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (σ : ℂ) (α : E)
    (q : Quotient (unitRel (E := E))) :
    term φ (2 * s) κ σ (mulQ α q).out = term φ (2 * s) κ σ α * term φ (2 * s) κ σ q.out := by
  have h1 : mulQ α q = Quotient.mk _ (α * q.out) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  obtain ⟨u, hu⟩ := Quotient.exact ((Quotient.out_eq _).trans h1)
  rw [← term_mul, hu, (TermUnit.term_unit_and_norm E I φ hφ s κ σ _).1 u]
end GlobalTheory.HomothetyLatSum
