-- Prove2me | solution 1 for GlobalTheory.T.heckeIdealEuclideanLattice_isZLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:12:03.265946+00:00
-- url     : https://prove2.me/submissions/584fb49f-752d-49d8-a6e8-a2b7967885fc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLatticeStatement
import Theorems.Thm_GlobalTheory_HeckePoisson_lat_isZLattice


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ → ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  first | exact @GlobalTheory.HeckePoisson.lat_isZLattice | exact GlobalTheory.HeckePoisson.lat_isZLattice | (intros; apply GlobalTheory.HeckePoisson.lat_isZLattice <;> assumption)
end _root_.GlobalTheory.T
