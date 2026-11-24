-- Prove2me | solution 1 for GlobalTheory.of_symm_mem_phDom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:30.327069+00:00
-- url     : https://prove2.me/submissions/58c12f64-2c80-4609-bb4b-e4b2afed9e22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Theorems.Thm_GlobalTheory_phSym_eq_self_of_isSymm
import Theorems.Thm_GlobalTheory_isSiegel_iff_mem_siegelH


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix
open GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
variable {g : ℕ}
open Complex Matrix
variable {g : ℕ}
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ}
    (hτ : τ ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) :
    (Matrix.of.symm τ : Fin g → Fin g → ℂ) ∈ _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  show _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of (Matrix.of.symm τ)) ∈ _root_.ReciprocityTheory.PTheta.SiegelH (Fin g)
  rw [Equiv.apply_symm_apply,
    _root_.GlobalTheory.phSym_eq_self_of_isSymm (_root_.GlobalTheory.isSiegel_iff_mem_siegelH.2 hτ).isSymm]
  exact hτ
end _root_.GlobalTheory
end GlobalTheory
