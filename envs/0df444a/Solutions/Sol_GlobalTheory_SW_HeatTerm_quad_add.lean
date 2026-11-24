-- Prove2me | solution 1 for GlobalTheory.SW.HeatTerm.quad_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:26:12.544184+00:00
-- url     : https://prove2.me/submissions/6a54359e-5393-4f9f-b072-1a9e43368be3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DerivDerivConstMulCexpBilinearAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeatTerm
noncomputable section
namespace GlobalTheory.SW.HeatTerm
theorem _root_.solution {n N : ℕ} (S : Matrix (Fin N) (Fin N) ℂ) (z z' : Matrix (Fin n) (Fin N) ℂ)
    (k : Fin n) (a b : Fin N) (s t : ℂ) :
    ∑ j, (z' + Matrix.single k b t) j ⬝ᵥ S *ᵥ (z + Matrix.single k a s) j =
      ∑ j, z' j ⬝ᵥ S *ᵥ z j + s * (z' k ᵥ* S) a + t * ((S *ᵥ z k) b + s * S b a) := by
  have h : ∀ (j : Fin n) (a : Fin N) (s : ℂ) (w : Matrix (Fin n) (Fin N) ℂ),
      (w + Matrix.single k a s) j = w j + if j = k then Pi.single a s else 0 := by
    intro j a s w
    ext i
    by_cases hj : j = k
    · subst hj; simp [Matrix.single_apply, Pi.single_apply, eq_comm]
    · simp [Matrix.single_apply, hj, Ne.symm hj]
  have h2 : ∀ j, (z' + Matrix.single k b t) j ⬝ᵥ S *ᵥ (z + Matrix.single k a s) j =
      z' j ⬝ᵥ S *ᵥ z j +
        if j = k then s * (z' k ᵥ* S) a + t * ((S *ᵥ z k) b + s * S b a) else 0 := by
    intro j
    rw [h, h]
    by_cases hj : j = k
    · subst hj
      simp only [if_true, Matrix.mulVec_add, add_dotProduct, dotProduct_add, single_dotProduct]
      rw [Matrix.dotProduct_mulVec _ _ (Pi.single a s), dotProduct_single]
      simp [Matrix.mulVec_single]
      ring
    · simp [hj]
  simp only [h2, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring
end GlobalTheory.SW.HeatTerm
