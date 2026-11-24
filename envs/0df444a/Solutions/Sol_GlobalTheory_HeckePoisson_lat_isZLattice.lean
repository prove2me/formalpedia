-- Prove2me | solution 1 for GlobalTheory.HeckePoisson.lat_isZLattice
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:49:37.702801+00:00
-- url     : https://prove2.me/submissions/2ddba359-29fa-4ef7-a874-974253ef59e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EmbAApply
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeIdealEuclideanLatticeIsZLattice
import Theorems.Thm_GlobalTheory_HeckePoisson_lat_eq_comap

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
noncomputable section
open GlobalTheory GlobalTheory.HeckePoisson
open GlobalTheory.CMVal InfinitePlace ComplexConjugate
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]
namespace GlobalTheory.HeckePoisson
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I]
    (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ M : Ideal (𝓞 K), M ≠ ⊥ →
      ∃ _ : DiscreteTopology (GlobalTheory.HeckePoisson.lat φ M), IsZLattice ℝ (GlobalTheory.HeckePoisson.lat φ M) := by
  intro K _ _ _ I _ φ h M hM
  classical
  rw [lat_eq_comap h M hM]
  exact ⟨inferInstance, inferInstance⟩
end GlobalTheory.HeckePoisson
