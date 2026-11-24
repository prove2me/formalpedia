-- Prove2me | solution 1 for GlobalTheory.convex_phDom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:47.792546+00:00
-- url     : https://prove2.me/submissions/6bf3eea8-99ba-4b10-bd84-8f69dc7ad3b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_IsPluriharmonicSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_SndFDerivAddSndFDerivIEqZeroOfHarmonicAtLine
import Theorems.Thm_GlobalTheory_IsSiegel_smul
import Theorems.Thm_GlobalTheory_isSiegel_iff_mem_siegelH

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open Complex Matrix
namespace GlobalTheory
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key
section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
end General
variable {g : ℕ}
open Complex Matrix in
variable {g : ℕ} in
private theorem convex_siegelH (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.PTheta.SiegelH (Fin g)) := by
  intro A hA B hB a b ha hb hab
  rw [← _root_.GlobalTheory.isSiegel_iff_mem_siegelH] at *
  refine ⟨?_, ?_⟩
  · exact (hA.isSymm.smul a).add (hB.isSymm.smul b)
  · have hm : ((a • A + b • B).map Complex.im) = a • A.map Complex.im + b • B.map Complex.im := by
      ext i j; simp
    rw [hm]
    rcases ha.eq_or_lt with rfl | ha'
    · simp at hab; subst hab; simpa using hB.posDef
    · exact (hA.posDef.smul ha').add_posSemidef (hB.posDef.posSemidef.smul hb)
end GlobalTheory
end
end

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
theorem _root_.solution (g : ℕ) : Convex ℝ (_root_.ReciprocityTheory.ChartRestriction.G.Key.phDom g) := by
  have hl : IsLinearMap ℝ (fun x : Fin g → Fin g → ℂ => _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym (Matrix.of x)) := by
    constructor
    · intro x y; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp; ring
    · intro c x; unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phSym; ext i j; simp; ring
  have := (convex_siegelH g).is_linear_preimage hl
  unfold _root_.ReciprocityTheory.ChartRestriction.G.Key.phDom
  exact this
end _root_.GlobalTheory
end GlobalTheory
