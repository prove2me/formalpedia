-- Prove2me | solution 1 for GlobalTheory.JHMult.occurs_of_finset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:21.812536+00:00
-- url     : https://prove2.me/submissions/1a51d94c-9c5d-4858-a6a9-4d461a9d396f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_JhMultSubAddQuot
import Theorems.Thm_GlobalTheory_JHMult_step_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL ValuativeRel MeasureTheory
open GlobalTheory GlobalTheory.JHMult
variable {F G V W V₁ V₂ : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W] [AddCommGroup V₁] [Module F V₁] [AddCommGroup V₂] [Module F V₂]
namespace GlobalTheory.JHMult
theorem _root_.solution {σ : Representation F G W} {ρ : Representation F G V} {r : ℕ}
    (A : Finset (Fin r)) (S T : Fin r → Subrepresentation ρ) (h1 : ∀ i, T i ≤ S i)
    (h2 : ∀ i j, i < j → S i ≤ T j) (h3 : ∀ i ∈ A, Step σ (S i) (T i)) :
    OccursTimes σ ρ A.card :=
  ⟨fun i => S (A.orderEmbOfFin rfl i), fun i => T (A.orderEmbOfFin rfl i), fun _ => h1 _,
    fun _ _ h => h2 _ _ ((A.orderEmbOfFin rfl).strictMono h),
    fun _ => step_iff.2 (h3 _ (A.orderEmbOfFin_mem rfl _))⟩
end GlobalTheory.JHMult
