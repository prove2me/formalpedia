-- Prove2me | solution 1 for GlobalTheory.relation_descends_along_functional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:31:24.693108+00:00
-- url     : https://prove2.me/submissions/89c1a9d7-0c07-4d74-9543-ba2ca3b19c11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRationalMultiplierOfComplexMultiplier

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
namespace GlobalTheory
theorem _root_.solution (K A B : Type) [Field K] [CommRing A] [Algebra K A]
    [CommRing B] [Algebra ℂ B] (σ : K →+* ℂ) (rd : A →+* B)
    (hrd : ∀ (a : K) (f : A), rd (a • f) = σ a • rd f) (W : Submodule K A) [FiniteDimensional K W]
    (hW : ∀ (n : ℕ) (b : Fin n → A), (∀ i, b i ∈ W) → LinearIndependent K b →
      LinearIndependent ℂ (fun i => rd (b i)))
    (φ : ℂ →+ K) (hφ : ∀ (a : K) (c : ℂ), φ (σ a * c) = a * φ c)
    {ι : Type} [Fintype ι] (x : ι → A) (hx : ∀ s, x s ∈ W) (c : ι → ℂ)
    (h : ∑ s, c s • rd (x s) = 0) : ∑ s, φ (c s) • x s = 0 := by
  classical
  obtain ⟨n, ⟨bW⟩⟩ : ∃ n, Nonempty (Basis (Fin n) K W) := ⟨_, ⟨Module.finBasis K W⟩⟩
  have hli : LinearIndependent K (fun j => (bW j : A)) :=
    bW.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hli' := hW n (fun j => (bW j : A)) (fun j => (bW j).2) hli
  have hcoord : ∃ α : ι → Fin n → K, ∀ s, x s = ∑ j, α s j • (bW j : A) := by
    refine ⟨fun s j => bW.repr ⟨x s, hx s⟩ j, fun s => ?_⟩
    have h1 := congrArg (fun v : W => (v : A)) (bW.sum_repr ⟨x s, hx s⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h1
    exact h1.symm
  obtain ⟨α, hα⟩ := hcoord
  have hrdx : ∀ s, rd (x s) = ∑ j, σ (α s j) • rd (bW j : A) := by
    intro s
    rw [hα s, map_sum]
    simp only [hrd]
  have hcoef : ∀ j, ∑ s, c s * σ (α s j) = 0 := by
    have h' : ∑ j, (∑ s, c s * σ (α s j)) • rd (bW j : A) = 0 := by
      rw [← h]
      simp only [hrdx, Finset.smul_sum, smul_smul, Finset.sum_smul]
      exact Finset.sum_comm
    exact fun j => Fintype.linearIndependent_iff.mp hli' _ h' j
  have hgoal : ∑ s, φ (c s) • x s = ∑ j, (∑ s, φ (c s) * α s j) • (bW j : A) := by
    simp only [hα, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hgoal]
  refine Finset.sum_eq_zero fun j _ => ?_
  have h5 : ∑ s, φ (c s) * α s j = φ (∑ s, c s * σ (α s j)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm (c s), hφ]
    exact mul_comm _ _
  rw [h5, hcoef j, map_zero, zero_smul]
end GlobalTheory
