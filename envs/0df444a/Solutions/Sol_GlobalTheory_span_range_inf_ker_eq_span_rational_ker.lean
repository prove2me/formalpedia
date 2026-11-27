-- Prove2me | solution 1 for GlobalTheory.span_range_inf_ker_eq_span_rational_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:36:08.423803+00:00
-- url     : https://prove2.me/submissions/b84b0caa-d07f-4b3b-9123-32d43ddfee66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpanRangeInfKerEqSpanRationalKer
import Theorems.Thm_GlobalTheory_semilinear_pi_eq_sum_single

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {K : Type} [Field K] (σ : K →+* ℂ) {W E : Type}
    [AddCommGroup W] [Module ℂ W] [AddCommGroup E] [Module ℂ E] {n d : ℕ}
    (j : (Fin n → K) →ₛₗ[σ] W) (j' : (Fin d → K) →ₛₗ[σ] E) (f : W →ₗ[ℂ] E)
    (M : Matrix (Fin d) (Fin n) K)
    (hli : LinearIndependent ℂ (fun l => j' (Pi.single l 1)))
    (hf : ∀ x, f (j x) = j' (M.mulVec x)) :
    Submodule.span ℂ (Set.range j) ⊓ LinearMap.ker f
      = Submodule.span ℂ (j '' {x | M.mulVec x = 0}) := by
  classical
  apply le_antisymm
  · rintro w ⟨hw, hw0⟩
    have hle : Submodule.span ℂ (Set.range j)
        ≤ Submodule.span ℂ (Set.range fun k => j (Pi.single k 1)) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      rw [semilinear_pi_eq_sum_single σ j x]
      exact Submodule.sum_mem _ fun k _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hle hw)
    have h0 : f (∑ k, c k • j (Pi.single k 1)) = 0 := hw0
    have h1 : ∑ l, (∑ k, σ (M l k) * c k) • j' (Pi.single l 1) = 0 := by
      rw [← h0, map_sum]
      simp only [map_smul, hf, Finset.sum_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [semilinear_pi_eq_sum_single σ j' (M.mulVec _), Finset.smul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [smul_smul, mul_comm]
      simp
    have h2 : ∀ l, ∑ k, σ (M l k) * c k = 0 := Fintype.linearIndependent_iff.1 hli _ h1
    letI : Algebra K ℂ := σ.toAlgebra
    let b := Basis.ofVectorSpace K ℂ
    let s := Finset.univ.biUnion fun k => (b.repr (c k)).support
    have hc : ∀ k, c k = ∑ i ∈ s, σ (b.repr (c k) i) * b i := by
      intro k
      have h3 := b.linearCombination_repr (c k)
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (s := s)
          (Finset.subset_biUnion_of_mem (fun k => (b.repr (c k)).support) (Finset.mem_univ k))
          _ (by simp)] at h3
      exact h3.symm
    have hw' : ∑ k, c k • j (Pi.single k 1) = ∑ i ∈ s, b i • j (fun k => b.repr (c k) i) := by
      have h5 : ∀ i, b i • j (fun k => b.repr (c k) i)
          = ∑ k, b i • σ (b.repr (c k) i) • j (Pi.single k 1) := fun i => by
        rw [semilinear_pi_eq_sum_single σ j (fun k => b.repr (c k) i), Finset.smul_sum]
      rw [Finset.sum_congr rfl fun i _ => h5 i, Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      conv_lhs => rw [hc k, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, mul_comm]
    rw [hw']
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, ?_, rfl⟩)
    ext l
    have h4 : b.repr (∑ k, M l k • c k) i = 0 := by
      have : ∑ k, M l k • c k = 0 := h2 l
      rw [this]; simp
    rw [map_sum, Finsupp.finset_sum_apply] at h4
    simp only [map_smul, Finsupp.smul_apply, smul_eq_mul] at h4
    exact h4
  · rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Submodule.subset_span ⟨x, rfl⟩, ?_⟩
    have hx' : M.mulVec x = 0 := hx
    change f (j x) = 0
    rw [hf, hx', map_zero]
end GlobalTheory
