-- Prove2me | solution 1 for GlobalTheory.LipschitzTR.exists_remb_eq_of_mem_dual
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:34:49.964161+00:00
-- url     : https://prove2.me/submissions/e11ad0a7-26b9-4d55-a48c-bef899542ddc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DualLatticeImageEqLatticeImageTraceDual
import Theorems.Thm_GlobalTheory_LipschitzTR_inner_remb_eq_trace
import Theorems.Thm_GlobalTheory_LipschitzTR_mem_latOf
import Theorems.Thm_GlobalTheory_LipschitzTR_remb_apply
import Theorems.Thm_GlobalTheory_card_realEmbeddings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LipschitzTR.remb_apply



set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
noncomputable section
open GlobalTheory GlobalTheory.LipschitzTR
variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory.LipschitzTR
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℚ F)
    (N : FractionalIdeal (𝓞 F)⁰ F) (hbN : ∀ i, b i ∈ N) (μ : RSp F)
    (hμ : μ ∈ Formalism.H.dual (latOf N)) : ∃ ν : F, remb F ν = μ := by
  set B := Algebra.traceForm ℚ F
  have hB : B.Nondegenerate := traceForm_nondegenerate ℚ F
  set b' := B.dualBasis hB b
  have hdel : ∀ i j, Algebra.trace ℚ F (b' j * b i) = if i = j then 1 else 0 := fun i j => by
    have := LinearMap.BilinForm.apply_dualBasis_left hB b j i
    rwa [Algebra.traceForm_apply] at this
  have hc : ∀ i, ∃ z : ℤ, ⟪μ, remb F (b i)⟫ = z := fun i => by
    have := (LinearMap.BilinForm.mem_dualSubmodule _).mp hμ (remb F (b i))
      ((mem_latOf N _).mpr ⟨b i, hbN i, rfl⟩)
    obtain ⟨z, hz⟩ := Submodule.mem_one.mp this
    exact ⟨z, by simpa using hz.symm⟩
  choose c hc using hc
  set ν : F := ∑ j, (c j : ℚ) • b' j
  have hνb : ∀ i, ⟪remb F ν, remb F (b i)⟫ = c i := fun i => by
    rw [inner_remb_eq_trace]
    have : Algebra.trace ℚ F (ν * b i) = c i := by
      simp only [ν, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, hdel, smul_eq_mul,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [this]; simp
  have hind : LinearIndependent ℝ (fun i => remb F (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have := congrArg (fun w => ⟪w, remb F (b' j)⟫) hg
    simp only [sum_inner, real_inner_smul_left, inner_remb_eq_trace, inner_zero_left] at this
    simp only [mul_comm (b _) (b' j), hdel] at this
    rw [Finset.sum_eq_single j (fun i _ hi => by rw [if_neg hi]; simp) (by simp)] at this
    simpa using this
  have hcard : Fintype.card ι = Module.finrank ℝ (RSp F) := by
    rw [finrank_euclideanSpace, GlobalTheory.card_realEmbeddings, Module.finrank_eq_card_basis b]
  haveI : Nonempty ι := b.index_nonempty
  let E := basisOfLinearIndependentOfCardEqFinrank hind hcard
  have hz : innerₛₗ ℝ (μ - remb F ν) = 0 := E.ext fun i => by
    simp [E, inner_sub_left, hνb, hc]
  have h0 := LinearMap.congr_fun hz (μ - remb F ν)
  have h1 : ⟪μ - remb F ν, μ - remb F ν⟫ = 0 := by
    rw [LinearMap.zero_apply] at h0; exact h0
  rw [inner_self_eq_zero, sub_eq_zero] at h1
  exact ⟨ν, h1.symm⟩
end GlobalTheory.LipschitzTR
