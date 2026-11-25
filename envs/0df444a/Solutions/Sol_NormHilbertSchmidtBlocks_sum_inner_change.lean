-- Prove2me | solution 1 for NormHilbertSchmidtBlocks.sum_inner_change
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:30:54.802776+00:00
-- url     : https://prove2.me/submissions/30e97c92-f14c-4f78-8d86-edd30d263ea2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_ClosedLocalOrbits_GaugeLatticeShifts_NormCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HilbertSchmidtBlocks_Change

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Classical ComplexConjugate
open NormHilbertSchmidtBlocks
namespace NormHilbertSchmidtBlocks
theorem _root_.solution {E F ι κ : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (e : κ → E)
    (he : ∀ x y : E, ∑ k, inner ℂ x (e k) * inner ℂ (e k) y = inner ℂ x y)
    (A B : E →ₗ[ℂ] F) :
    ∑ k, inner ℂ (A (e k)) (B (e k)) = ∑ i, inner ℂ (A (b i)) (B (b i)) := by
  have hexp : ∀ x : E, ∑ i, inner ℂ (b i) x • b i = x := fun x => b.sum_repr' x
  have key : ∀ k, inner ℂ (A (e k)) (B (e k)) =
      ∑ i, ∑ i', (inner ℂ (b i) (e k) * inner ℂ (e k) (b i')) * inner ℂ (A (b i')) (B (b i)) := by
    intro k
    conv_lhs => rw [← hexp (e k)]
    simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      inner_conj_symm, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, he, orthonormal_iff_ite.mp b.orthonormal, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
end NormHilbertSchmidtBlocks
