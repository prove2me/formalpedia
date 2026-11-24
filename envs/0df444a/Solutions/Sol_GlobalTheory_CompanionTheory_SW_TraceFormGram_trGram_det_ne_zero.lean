-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.TraceFormGram.trGram_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T13:37:44.301355+00:00
-- url     : https://prove2.me/submissions/2b8352f0-47cf-4cde-9b55-e3c51c7d2623

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_EtaleAwayQuotientEqLocalization
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_TraceFormGram_sig_sig

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TraceFormGram
open HeckeCharacterZeroLocus.SiegelWeilU
open scoped TensorProduct Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [NumberField F] [NumberField E]
namespace GlobalTheory.CompanionTheory.SW.TraceFormGram
theorem _root_.solution {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {M d : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (b : Module.Basis (Fin d) F E) :
    (trGram σ J b).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hBv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  set y : Fin M → E := fun j => ∑ l, v (j, l) • b l with hy
  have key : ∀ i k, Algebra.trace F E (σ (b k) * (J *ᵥ y) i) = 0 := by
    intro i k
    have h0 := congrFun hBv (i, k)
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, trGram, Pi.zero_apply] at h0
    rw [← h0]
    simp only [Matrix.mulVec, dotProduct, hy, Finset.mul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, mul_smul_comm, map_smul, smul_eq_mul, mul_comm, mul_assoc]
  have key2 : ∀ i (e : E), Algebra.trace F E (e * (J *ᵥ y) i) = 0 := by
    intro i e
    have he : e = ∑ k, (b.repr (σ e) k) • σ (b k) := by
      have h3 := congrArg σ (b.sum_repr (σ e))
      rw [sig_sig h, map_sum] at h3
      exact h3.symm.trans (Finset.sum_congr rfl fun k _ => σ.toLinearMap.map_smul _ _)
    rw [he]
    simp only [Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, key, smul_zero,
      Finset.sum_const_zero]
  have hw : J *ᵥ y = 0 := by
    funext i
    refine (traceForm_nondegenerate F E).1 _ fun e => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact key2 i e
  have hy0 : y = 0 := Matrix.eq_zero_of_mulVec_eq_zero hJ.2 hw
  apply hv
  funext ⟨j, l⟩
  have := congrFun hy0 j
  have h2 := Fintype.linearIndependent_iff.1 b.linearIndependent (fun l => v (j, l)) this l
  simpa using h2
end GlobalTheory.CompanionTheory.SW.TraceFormGram
