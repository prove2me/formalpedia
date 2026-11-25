-- Prove2me | solution 1 for GlobalTheory.DualCokernel.extZero_self
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:08:01.368213+00:00
-- url     : https://prove2.me/submissions/7f8d6dbd-9bd9-4c33-845c-a536dce51b36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_AcyclicityLemmaDepthDifferentialCokernelsFiniteL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndKerBaseChangeOfForallResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsSMulRegularCokerDualMapOfExactFibres

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian IsLocalRing TensorProduct Function
open GlobalTheory
open GlobalTheory.DualCokernel
variable {R : Type} [CommRing R]
variable [IsLocalRing R]
variable [IsNoetherianRing R]
namespace GlobalTheory.DualCokernel
theorem _root_.solution (ϖ : R) (g : ℕ) (hϖ : ϖ ∈ nonZeroDivisors R) (hm : ϖ ∈ maximalIdeal R)
    [IsRegularLocalRing (R ⧸ Ideal.span {ϖ})] (hg : ringKrullDim (R ⧸ Ideal.span {ϖ}) = g)
    (j : ℕ) (hj : j < g + 1) : ExtZero (R := R) R j := by
  obtain ⟨xs, h, hd⟩ := exists_ofList_eq_maximalIdeal_length_eq (R ⧸ Ideal.span {ϖ})
  have hreg := isRegular_of_ofList_eq_maximalIdeal h hd.le
  have hlen : xs.length = g := by
    rw [hg] at hd
    exact_mod_cast hd
  let σ := Function.surjInv (Ideal.Quotient.mk_surjective (I := Ideal.span {ϖ}))
  have hσ : ∀ a, Ideal.Quotient.mk _ (σ a) = a := Function.surjInv_eq _
  have hmap : (xs.map σ).map (algebraMap R (R ⧸ Ideal.span {ϖ})) = xs := by
    rw [List.map_map]
    exact List.map_id'' hσ xs
  have h1 : RingTheory.Sequence.IsRegular (R ⧸ Ideal.span {ϖ}) (xs.map σ) := by
    rw [← hmap] at hreg
    exact ((AddEquiv.refl _).isRegular_congr <| List.forall₂_map_left_iff.mpr <|
      List.forall₂_same.mpr fun r _ => algebraMap_smul _ r).1 hreg
  have e : QuotSMulTop ϖ R ≃ₗ[R] R ⧸ Ideal.span {ϖ} :=
    Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top])
  have h2 : RingTheory.Sequence.IsRegular R (ϖ :: xs.map σ) := by
    rw [RingTheory.Sequence.isRegular_cons_iff, e.isRegular_congr]
    exact ⟨(isRegular_iff_mem_nonZeroDivisors.mpr hϖ).left.isSMulRegular, h1⟩
  refine ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) _ ?_ _ ?_ _ ?_ h2 j
    (by simpa [hlen] using hj)
  · rw [Module.support_eq_zeroLocus, Ideal.annihilator_quotient]
  · rw [smul_eq_mul, Ideal.mul_top]
    exact (maximalIdeal.isMaximal R).ne_top.lt_top
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hm
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
      have hx' : x ∈ maximalIdeal _ := h ▸ Ideal.subset_span hx
      rw [mem_maximalIdeal, mem_nonunits_iff] at hx' ⊢
      exact fun hu => hx' (hσ x ▸ hu.map (Ideal.Quotient.mk _))
end GlobalTheory.DualCokernel
