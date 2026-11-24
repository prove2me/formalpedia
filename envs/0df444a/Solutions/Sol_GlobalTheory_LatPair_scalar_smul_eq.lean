-- Prove2me | solution 1 for GlobalTheory.LatPair.scalar_smul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:38:27.533932+00:00
-- url     : https://prove2.me/submissions/f125f538-e87d-4063-9e41-674d3801f5a3

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
namespace GlobalTheory.LatPair
theorem _root_.solution [Fintype n] [DecidableEq n] (g : GL n k) (s : 𝒪[k]ˣ) (hg : ∀ x : n → k, g • x = (s : 𝒪[k]) • x)
    (P : Pair k n) : g • P = (Units.map (residue 𝒪[k]).toMonoidHom s)⁻¹ • P := by
  refine Pair.ext fun x a => ?_
  obtain ⟨y, rfl⟩ : ∃ y, x = g • y := ⟨g⁻¹ • x, (smul_inv_smul g x).symm⟩
  rw [Pair.smul_hasVal, inv_smul_smul, Pair.dia_hasVal, inv_inv, hg]
  refine ⟨fun h => h.smul _, fun h => ?_⟩
  have := h.smul (s⁻¹ : 𝒪[k]ˣ)
  rw [smul_smul, Units.inv_mul, one_smul] at this
  convert this using 1
  change a = _ * (residue 𝒪[k] s * a)
  rw [← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
end GlobalTheory.LatPair
