-- Prove2me | solution 1 for GlobalTheory.free_finite_finrank_of_lattice_embedding
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:59:07.808001+00:00
-- url     : https://prove2.me/submissions/2cb20761-8d96-490c-9929-8c5e6ef26bc1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsEqCexpQuadraticOfEquivalentFactors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology Complex
open GlobalTheory
variable {L L' : Type*} [AddCommGroup L] [AddCommGroup L']
namespace GlobalTheory
theorem _root_.solution {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] (P : L →+ V) (hP : Function.Injective P)
    (hd : DiscreteTopology (range P)) (hs : Submodule.span ℝ (range P) = ⊤) :
    Module.Free ℤ L ∧ Module.Finite ℤ L ∧ Module.finrank ℤ L = Module.finrank ℝ V := by
  let Λ : Submodule ℤ V := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology Λ := hd
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  let e : L ≃ₗ[ℤ] Λ := LinearEquiv.ofInjective P.toIntLinearMap hP
  exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm,
    e.finrank_eq.trans (ZLattice.rank ℝ Λ)⟩
end GlobalTheory
