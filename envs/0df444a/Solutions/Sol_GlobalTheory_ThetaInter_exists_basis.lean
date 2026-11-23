-- Prove2me | solution 1 for GlobalTheory.ThetaInter.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:24:33.857174+00:00
-- url     : https://prove2.me/submissions/e32ec3f4-a718-4898-9199-aa395f10b4f2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
variable {α : V → ℂ}
open MeasureTheory
variable {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
  [FiniteDimensional ℝ W] {H : Sesq W} {α : W → ℂ}
namespace GlobalTheory.ThetaInter
theorem _root_.solution {A : AddSubgroup W} (hA : DiscreteTopology A) (hsp : Submodule.span ℝ (A : Set W) = ⊤) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℝ W), (Submodule.span ℤ (Set.range b)).toAddSubgroup = A := by
  have : DiscreteTopology (AddSubgroup.toIntSubmodule A) := hA
  have : IsZLattice ℝ (AddSubgroup.toIntSubmodule A) := ⟨hsp⟩
  have := ZLattice.module_finite ℝ (AddSubgroup.toIntSubmodule A)
  have := ZLattice.module_free ℝ (AddSubgroup.toIntSubmodule A)
  refine ⟨_, (Module.finBasis ℤ (AddSubgroup.toIntSubmodule A)).ofZLatticeBasis ℝ _, ?_⟩
  rw [Module.Basis.ofZLatticeBasis_span]
  rfl
end GlobalTheory.ThetaInter
