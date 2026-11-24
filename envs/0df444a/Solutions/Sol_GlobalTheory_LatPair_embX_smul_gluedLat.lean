-- Prove2me | solution 1 for GlobalTheory.LatPair.embX_smul_gluedLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:48.259898+00:00
-- url     : https://prove2.me/submissions/1b5fd72c-b580-457c-9b4a-05d43627540f

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
variable {c : ℕ}
variable [Fintype n] [DecidableEq n]
namespace GlobalTheory.LatPair
theorem _root_.solution (g : GL n k) (q : Unif k) (c p : ℕ) (L : Submodule 𝒪[k] (n → k)) (f : n → k) :
    RootEx.embX c g • gluedLat q c p L f = gluedLat q c p (g • L) (g • f) := by
  ext y
  have h : (RootEx.embX c g)⁻¹ • y = Sum.elim (g⁻¹ • (y ∘ Sum.inl)) (y ∘ Sum.inr) := by
    rw [← map_inv]
    change fromBlocks (g⁻¹ : GL n k).val 0 0 1 *ᵥ y = _
    rw [fromBlocks_mulVec]
    simp only [zero_mulVec, one_mulVec, add_zero, zero_add]
    rfl
  simp only [mem_smul_iff, h, mem_gluedLat, Sum.elim_comp_inl, Sum.elim_inr, Function.comp_apply, smul_sub,
    smul_comm g⁻¹, inv_smul_smul]
end GlobalTheory.LatPair
