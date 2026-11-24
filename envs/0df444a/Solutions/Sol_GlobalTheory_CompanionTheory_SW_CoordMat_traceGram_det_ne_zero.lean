-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.CoordMat.traceGram_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:12:22.381662+00:00
-- url     : https://prove2.me/submissions/06d15dc7-e0e6-494a-b5bd-9c1a37601c40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TraceGramDetNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.CoordMat
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace GlobalTheory.CompanionTheory.SW.CoordMat
theorem _root_.solution [FiniteDimensional F E] [Algebra.IsSeparable F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (hJ : J.det ≠ 0)
    (b : Module.Basis (Fin d) F E) : (traceGram σ J b).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  apply hv
  let y : Fin M → E := fun j => ∑ l, v (j, l) • b l
  have h1 : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, traceGram, Pi.zero_apply] at h
    rw [← h]
    simp only [Matrix.mulVec, dotProduct, y, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have h2 : ∀ i z, Algebra.trace F E (z * (J *ᵥ y) i) = 0 := by
    intro i z
    have hz : z = ∑ k, b.repr (σ z) k • σ (b k) := by
      have h := congrArg σ (b.sum_repr (σ z))
      rw [hσ, map_sum] at h
      exact h.symm.trans (Finset.sum_congr rfl fun k _ => map_smul σ _ _)
    rw [hz, Finset.sum_mul, map_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [smul_mul_assoc, map_smul, h1, smul_zero]
  have h3 : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun z => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact h2 i z
  have h4 := Matrix.eq_zero_of_mulVec_eq_zero hJ h3
  funext p
  exact Fintype.linearIndependent_iff.mp b.linearIndependent (fun l => v (p.1, l)) (congrFun h4 p.1) p.2
end GlobalTheory.CompanionTheory.SW.CoordMat
