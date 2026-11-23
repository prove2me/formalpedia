-- Prove2me | solution 1 for GlobalTheory.SW.Nbr.fg_of_agree
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:01:08.04279+00:00
-- url     : https://prove2.me/submissions/3ad9a2c1-82de-4f66-a8e7-9f56b6cdd1fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CycOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Nbr
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]
namespace GlobalTheory.SW.Nbr
theorem _root_.solution {m : ℕ} {Λ Λ' : Lt E n} (h : Λ.FG) (ha : Agree m Λ Λ') : Λ'.FG := by
  obtain ⟨s, hs, -, -, h2⟩ := ha
  have hs' : (s : E) ≠ 0 := Nat.cast_ne_zero.2 hs.ne'
  let f : (Fin n → E) →ₗ[𝓞 E] (Fin n → E) :=
    (LinearMap.lsmul E (Fin n → E) (s : E)⁻¹).restrictScalars (𝓞 E)
  refine Submodule.FG.of_le (h.map f) fun v hv => ⟨_, h2 v hv, ?_⟩
  simp [f, smul_smul, hs']
end GlobalTheory.SW.Nbr
