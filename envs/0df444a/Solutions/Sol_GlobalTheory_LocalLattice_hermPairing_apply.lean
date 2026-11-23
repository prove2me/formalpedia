-- Prove2me | solution 1 for GlobalTheory.LocalLattice.hermPairing_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:12.328686+00:00
-- url     : https://prove2.me/submissions/7403c72c-ad57-474d-9412-050280e26ac8

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
open ReciprocityTheory.ChartRestriction.G.FD
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.LocalLattice
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermPairing G x y = herm G x y := rfl
end GlobalTheory.LocalLattice
