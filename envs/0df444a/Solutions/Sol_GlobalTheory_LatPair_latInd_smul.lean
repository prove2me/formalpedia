-- Prove2me | solution 1 for GlobalTheory.LatPair.latInd_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:50.714782+00:00
-- url     : https://prove2.me/submissions/7a2043ea-1594-4b03-a27d-b02c64d34a40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsGlOfEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
variable [Fintype n']
variable {P : Pair k n'} {Q : Pair k n} {x : Matrix n n' k}
variable [DecidableEq n'] [Fintype n] [DecidableEq n]
namespace GlobalTheory.LatPair
theorem _root_.solution (g : GL n' k) (h : GL n k) (S : Submodule 𝒪[k] (n' → k)) (L : Submodule 𝒪[k] (n → k)) :
    latInd (g • S) (h • L) x = latInd S L ((h⁻¹ : GL n k).val * x * g.val) := by
  have : (∀ y ∈ g • S, x *ᵥ y ∈ h • L) ↔ ∀ y ∈ S, ((h⁻¹ : GL n k).val * x * g.val) *ᵥ y ∈ L := by
    simp only [mem_smul_iff, ← mulVec_mulVec]
    refine ⟨fun H y hy => H (g • y) (by simpa using hy), fun H y hy => ?_⟩
    have := H _ hy
    rwa [show g.val *ᵥ (g⁻¹ • y) = y from smul_inv_smul g y] at this
  classical
  exact if_congr this rfl rfl
end GlobalTheory.LatPair
