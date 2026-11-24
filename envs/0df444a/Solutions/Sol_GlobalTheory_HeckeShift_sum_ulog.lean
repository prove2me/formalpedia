-- Prove2me | solution 1 for GlobalTheory.HeckeShift.sum_ulog
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:15:46.106806+00:00
-- url     : https://prove2.me/submissions/5a40e930-9e46-417a-88c9-449f3e27b891

import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegrandUnitMul
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeShift
namespace GlobalTheory.HeckeShift
theorem _root_.solution {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {I : Type} [Fintype I]
    (φ : I → K →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ) (u : (𝓞 K)ˣ) : ∑ i, GlobalTheory.HeckeTheta.ulog φ u i = 0 := by
  have hbij : Function.Bijective (fun i => InfinitePlace.mk (φ i)) := by
    constructor
    · intro i j hij
      obtain ⟨k, _, hk⟩ := hφ (φ i)
      have hi := hk i (Or.inl rfl)
      rcases InfinitePlace.mk_eq_iff.1 hij with h | h
      · rw [hi, hk j (Or.inl h)]
      · rw [hi, hk j (Or.inr (by rw [← h]; ext x; simp [ComplexEmbedding.conjugate_coe_eq]))]
    · intro w
      obtain ⟨k, hk, _⟩ := hφ w.embedding
      refine ⟨k, ?_⟩
      rcases hk with h | h
      · simp only; rw [← h, InfinitePlace.mk_embedding]
      · simp only; rw [← InfinitePlace.mk_conjugate_eq (φ k), ← h, InfinitePlace.mk_embedding]
  have h0 := NumberField.Units.sum_mult_mul_log u
  rw [← (Equiv.ofBijective _ hbij).sum_comp] at h0
  rw [← h0]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hm : (InfinitePlace.mk (φ i)).mult = 2 :=
    InfinitePlace.mult_isComplex ⟨_, IsTotallyComplex.isComplex _⟩
  simp only [Equiv.ofBijective_apply, InfinitePlace.apply, hm, GlobalTheory.HeckeTheta.ulog, Real.log_pow]
end GlobalTheory.HeckeShift
