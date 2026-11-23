-- Prove2me | solution 1 for GlobalTheory.LocalLattice.mem_one_ringOfIntegers_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:40:28.75477+00:00
-- url     : https://prove2.me/submissions/41273bb7-16b1-41dd-a037-149ae1516062

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped nonZeroDivisors
noncomputable section
open GlobalTheory GlobalTheory.LocalLattice
set_option linter.unusedSectionVars false
open NumberField
namespace GlobalTheory.LocalLattice
theorem _root_.solution {K : Type*} [Field K] [NumberField K] (x : K) :
    x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x :=
  Submodule.mem_one.trans
    ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩
end GlobalTheory.LocalLattice
