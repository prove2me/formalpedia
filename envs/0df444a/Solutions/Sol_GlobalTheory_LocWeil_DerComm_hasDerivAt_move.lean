-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.hasDerivAt_move
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:48:53.693032+00:00
-- url     : https://prove2.me/submissions/08c3a8e2-2cd0-4861-8a01-49fdeaab628a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DifferentiableAtOneParameter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.LocWeil GlobalTheory.LocWeil.DerComm
variable {S U : Type} [AddCommGroup S] [Module ℂ S]
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
namespace GlobalTheory.LocWeil.DerComm
theorem _root_.solution (ℓ : S →ₗ[ℂ] ℂ) (d : U →ₗ[ℝ] Module.End ℂ S) (P : ℝ → Module.End ℂ S) (hP : P 0 = 1)
    (A : Module.End ℂ S) (Φ : S) (hA : ∀ u, HasDerivAt (fun t => ℓ (P t (d u Φ))) (ℓ (A (d u Φ))) 0)
    {c : ℝ → U} {c' : U} (hc : HasDerivAt c c' 0) :
    HasDerivAt (fun t => ℓ (P t (d (c t) Φ))) (ℓ (d c' Φ + A (d (c 0) Φ))) 0 := by
  let b := Module.finBasis ℝ U
  have e : ∀ (Q : Module.End ℂ S) (u : U), ℓ (Q (d u Φ)) = ∑ i, b.coord i u • ℓ (Q (d (b i) Φ)) := fun Q u => by
    conv_lhs => rw [← b.sum_repr u]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smul_of_tower,
      Module.Basis.coord_apply]
  have e1 := e 1 c'
  rw [Module.End.one_apply] at e1
  rw [map_add, e1, e A, add_comm, ← Finset.sum_add_distrib]
  simp only [e (P _) (c _)]
  refine HasDerivAt.fun_sum fun i _ => ?_
  have := ((LinearMap.toContinuousLinearMap (b.coord i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hc).smul (hA (b i))
  rw [hP] at this
  exact this
end GlobalTheory.LocWeil.DerComm
