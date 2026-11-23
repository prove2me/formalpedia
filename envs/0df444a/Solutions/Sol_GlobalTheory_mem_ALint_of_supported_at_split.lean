-- Prove2me | solution 1 for GlobalTheory.mem_ALint_of_supported_at_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:03.471871+00:00
-- url     : https://prove2.me/submissions/33b6d5e4-e50d-4ea1-9284-e4c56349136d

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GaloisLevelStructure_DefsAut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CmFieldAdeleSplitPlaceSupportIntegral
import Theorems.Thm_GlobalTheory_tensor_exists_decomp
import Theorems.Thm_GlobalTheory_tensor_decomp_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (e : 𝓞 L), Valued.v (s.i (e : L)) = 1 → Valued.v (s.i (IsCMField.complexConj L (e : L))) < 1 → ∀ z : ReciprocityTheory.Aut.AL L, (∀ w, w ≠ s.v → ReciprocityTheory.Aut.compAt L w z = 0) → Valued.v (s.proj z) ≤ 1 → Valued.v (s.proj (ReciprocityTheory.Aut.conjAL L z)) ≤ 1 → z ∈ ReciprocityTheory.Aut.ALint L := by
  intro L _ _ _ s e he hc z hz hp hq
  have hne : (e : L) ≠ IsCMField.complexConj L (e : L) := by
    intro h
    rw [← h, he] at hc
    exact lt_irrefl _ hc
  have hli : LinearIndependent (maximalRealSubfield L) ![(1 : L), (e : L)] := by
    rw [LinearIndependent.pair_iff]
    intro a t h
    have h' := congrArg (IsCMField.complexConj L) h
    simp only [Algebra.smul_def, map_add, map_mul, AlgEquiv.commutes, map_one, map_zero] at h h'
    have hd : algebraMap (maximalRealSubfield L) L t * ((e : L) - IsCMField.complexConj L (e : L)) = 0 := by
      linear_combination h - h'
    have ht : t = 0 := by
      rcases mul_eq_zero.1 hd with h0 | h0
      · simpa using h0
      · exact absurd (sub_eq_zero.1 h0) hne
    subst ht
    simpa using h
  have hcard : Fintype.card (Fin 2) = Module.finrank (maximalRealSubfield L) L := by
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield L) L]; simp
  let b := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hb0 : b 0 = 1 := by simp [b]
  have hb1 : b 1 = (e : L) := by simp [b]
  obtain ⟨A, B, hAB⟩ := tensor_exists_decomp b z
  rw [hb0, hb1] at hAB
  have hoff : ∀ w, w ≠ s.v → A w = 0 ∧ B w = 0 := by
    intro w hw
    have h := hz w hw
    rw [hAB] at h
    apply tensor_decomp_eq_zero b
    rw [hb0, hb1]
    simp [ReciprocityTheory.Aut.compAt, Algebra.TensorProduct.map_tmul] at h
    exact h
  have h1 : s.proj z = A s.v + s.i (e : L) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, Algebra.TensorProduct.lift_tmul]
    rfl
  have h2 : s.proj (ReciprocityTheory.Aut.conjAL L z) =
      A s.v + s.i (IsCMField.complexConj L (e : L)) * B s.v := by
    rw [hAB]
    simp [ReciprocityTheory.Aut.SplitPlace.proj, ReciprocityTheory.Aut.conjAL, Algebra.TensorProduct.lift_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl
  have hu : Valued.v (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) = 1 := by
    rw [Valuation.map_sub_eq_of_lt_left _ (by rw [he]; exact hc), he]
  have hBv : Valued.v (B s.v) ≤ 1 := by
    have hm : (s.i (e : L) - s.i (IsCMField.complexConj L (e : L))) * B s.v =
        s.proj z - s.proj (ReciprocityTheory.Aut.conjAL L z) := by
      rw [h1, h2]; ring
    have hv := congrArg Valued.v hm
    rw [map_mul, hu, one_mul] at hv
    rw [hv]
    exact Valuation.map_sub_le _ hp hq
  have hAv : Valued.v (A s.v) ≤ 1 := by
    have hm : A s.v = s.proj z - s.i (e : L) * B s.v := by rw [h1]; ring
    rw [hm]
    refine Valuation.map_sub_le _ hp ?_
    rw [map_mul, he, one_mul]
    exact hBv
  have hAi : ∀ w, A w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hAv
    · rw [(hoff w hw).1]; exact zero_mem _
  have hBi : ∀ w, B w ∈ w.adicCompletionIntegers (maximalRealSubfield L) := by
    intro w
    rcases eq_or_ne w s.v with rfl | hw
    · exact hBv
    · rw [(hoff w hw).2]; exact zero_mem _
  have hsplit : ((e : L) ⊗ₜ[maximalRealSubfield L] B : ReciprocityTheory.Aut.AL L) =
      ((e : L) ⊗ₜ[maximalRealSubfield L] (1 : ReciprocityTheory.Aut.AFplus L)) *
        ((1 : L) ⊗ₜ[maximalRealSubfield L] B) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [hAB, hsplit]
  refine Subring.add_mem _ (Subring.subset_closure (Or.inr ⟨A, hAi, rfl⟩))
    (Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨e, rfl⟩))
      (Subring.subset_closure (Or.inr ⟨B, hBi, rfl⟩)))
end GlobalTheory
