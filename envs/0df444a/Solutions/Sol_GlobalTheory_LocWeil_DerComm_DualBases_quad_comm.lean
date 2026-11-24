-- Prove2me | solution 1 for GlobalTheory.LocWeil.DerComm.DualBases.quad_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:49:09.07507+00:00
-- url     : https://prove2.me/submissions/99d23906-8871-4c8a-b818-fda1534af079

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
variable (β : U →ₗ[ℝ] U →ₗ[ℝ] ℝ) {ι : Type} [Fintype ι] (b b' : ι → U)
variable {β b b'}
variable {d : U →ₗ[ℝ] Module.End ℂ S} {κ : ℂ} {Y : U →ₗ[ℝ] U}
namespace GlobalTheory.LocWeil.DerComm
namespace DualBases
theorem _root_.solution (h : DualBases β b b') (hs : ∀ x y, β y x = -β x y)
    (hd : ∀ u v, d u * d v - d v * d u = (κ * (β u v : ℝ)) • (1 : Module.End ℂ S))
    (hY : ∀ x y, β (Y x) y = -β x (Y y)) (u : U) : quad d b b' Y * d u - d u * quad d b b' Y = (2 * κ) • d (Y u) := by
  have e : ∀ i, d (Y (b i)) * d (b' i) * d u - d u * (d (Y (b i)) * d (b' i)) =
      κ • d (Y (β (b' i) u • b i)) + κ • d (β (Y u) (b i) • b' i) := fun i => by
    have : d (Y (b i)) * d (b' i) * d u - d u * (d (Y (b i)) * d (b' i)) =
        d (Y (b i)) * (d (b' i) * d u - d u * d (b' i)) + (d (Y (b i)) * d u - d u * d (Y (b i))) * d (b' i) := by
      noncomm_ring
    rw [this, hd, hd, hY (b i), ← hs, mul_smul_comm, smul_mul_assoc, mul_one, one_mul, map_smul, map_smul, map_smul,
      mul_smul, mul_smul, Complex.coe_smul, Complex.coe_smul]
  rw [quad, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, ← map_sum, ← map_sum, ← map_sum, h.1, h.2, two_mul,
    add_smul]
end DualBases
end GlobalTheory.LocWeil.DerComm
