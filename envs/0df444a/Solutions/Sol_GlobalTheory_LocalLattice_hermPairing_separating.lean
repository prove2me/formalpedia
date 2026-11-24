-- Prove2me | solution 1 for GlobalTheory.LocalLattice.hermPairing_separating
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:49:04.786865+00:00
-- url     : https://prove2.me/submissions/d251a9ee-392c-439a-8a06-ca528359d8a6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorsionNonvanishStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_MemIffForallMemLocalizeRingOfIntegers
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply

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
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0) (x : Fin r → E)
    (hx : ∀ y, hermPairing G x y = 0) : x = 0 := by
  refine Matrix.eq_zero_of_vecMul_eq_zero hG (funext fun b => ?_)
  have := hx (Pi.single b 1)
  simpa [herm, cc, Pi.single_apply, apply_ite, Matrix.vecMul, dotProduct] using this
end GlobalTheory.LocalLattice
