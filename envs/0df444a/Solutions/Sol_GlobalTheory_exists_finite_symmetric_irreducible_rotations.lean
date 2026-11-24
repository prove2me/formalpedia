-- Prove2me | solution 1 for GlobalTheory.exists_finite_symmetric_irreducible_rotations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:55:06.471844+00:00
-- url     : https://prove2.me/submissions/8d6a4d08-cc75-4ebe-b565-3aac5c8bbf33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsFiniteSymmetricIrreducibleRotations
import Theorems.Thm_GlobalTheory_HypRot_rot_sq_sub
import Theorems.Thm_GlobalTheory_HypRot_rot_inv
import Theorems.Thm_GlobalTheory_HypRot_rot_det
import Theorems.Thm_GlobalTheory_HypRot_rot_herm
import Theorems.Thm_GlobalTheory_HypRot_diag_rot
import Theorems.Thm_GlobalTheory_HypRot_rot_unitary

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open HypRot
namespace GlobalTheory
theorem _root_.solution :
    (∀ (r p : ℕ), 0 < p → p < r → ∀ W : Submodule ℂ (Fin r → ℂ), (∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → ∀ v ∈ W, (Matrix.single j k (1 : ℂ)).mulVec v ∈ W ∧ (Matrix.single k j (1 : ℂ)).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ (r p : ℕ), 0 < p → p < r → ∃ S : Finset (Matrix (Fin r) (Fin r) ℂ), S.Nonempty ∧ (∀ a ∈ S, a.IsHermitian ∧ a.det ≠ 0 ∧ a⁻¹ ∈ S) ∧ (∀ W : Submodule ℂ (Fin r → ℂ), (∀ a ∈ S, ∀ v ∈ W, (a * a).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤) ∧ ∀ a ∈ S, (a)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (a).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ ∃ s : Matrix (Fin r) (Fin r) ℂ, (s)ᵀ * (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) * (s).map (starRingEnd ℂ) = (Matrix.diagonal fun k : Fin r => if (k : ℕ) < p then (1 : ℂ) else -1) ∧ s * a = a⁻¹ * s) := by
  intro H r p hp hpr
  classical
  have hne : ∀ j k : Fin r, (j : ℕ) < p → p ≤ (k : ℕ) → j ≠ k := by
    intro j k hj hk e
    have := congrArg Fin.val e
    omega
  have hUs : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ),
      u * star u = 1 ∧ -u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by
    intro u hu
    simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl | rfl <;>
      simp [Complex.ext_iff]
  refine ⟨((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
      ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2),
      ?_, ?_, ?_, ?_⟩
  · refine ⟨rot ⟨0, by omega⟩ ⟨p, hpr⟩ 1, Finset.mem_image.mpr ⟨((⟨0, by omega⟩, ⟨p, hpr⟩), 1), ?_, rfl⟩⟩
    simp [hp]
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    refine ⟨rot_herm j k u, rot_det (hne j k hj hk) (hUs u hu).1, ?_⟩
    rw [rot_inv (hne j k hj hk) (hUs u hu).1]
    exact Finset.mem_image.mpr ⟨((j, k), -u), by simp [hj, hk, (hUs u hu).2], rfl⟩
  · intro W hW
    apply H r p hp hpr W
    intro j k hj hk v hv
    have hjk := hne j k hj hk
    have hmem : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), rot j k u ∈
        ((Finset.univ.filter fun jk : Fin r × Fin r => (jk.1 : ℕ) < p ∧ p ≤ (jk.2 : ℕ)) ×ˢ
        ({1, -1, Complex.I, -Complex.I} : Finset ℂ)).image (fun x => rot x.1.1 x.1.2 x.2) := by
      intro u hu
      exact Finset.mem_image.mpr ⟨((j, k), u), by simp [hj, hk, hu], rfl⟩
    have hN : ∀ u ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ), (offN j k u).mulVec v ∈ W := by
      intro u hu
      rw [rot_sq_sub hjk (hUs u hu).1, Matrix.smul_mulVec, Matrix.sub_mulVec]
      exact W.smul_mem _ (W.sub_mem (hW _ (hmem u hu) v hv) (hW _ (hmem _ (hUs u hu).2) v hv))
    have h1 : (1 : ℂ) ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hI : Complex.I ∈ ({1, -1, Complex.I, -Complex.I} : Finset ℂ) := by simp
    have hII : Complex.I * star Complex.I = 1 := by
      rw [Complex.star_def, Complex.conj_I, mul_neg, Complex.I_mul_I, neg_neg]
    have hsI : Complex.I • offN j k Complex.I = -Matrix.single j k (1 : ℂ) + Matrix.single k j 1 := by
      rw [offN, smul_add, Matrix.smul_single, Matrix.smul_single, smul_eq_mul, smul_eq_mul,
        Complex.I_mul_I, hII, Matrix.single_neg]
    have h1' : offN j k (1 : ℂ) = Matrix.single j k 1 + Matrix.single k j 1 := by
      rw [offN, star_one]
    have e1 : Matrix.single j k (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 - Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    have e2 : Matrix.single k j (1 : ℂ) = (1 / 2 : ℂ) • (offN j k 1 + Complex.I • offN j k Complex.I) := by
      rw [hsI, h1']
      module
    constructor
    · rw [e1, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.sub_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
    · rw [e2, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec]
      exact W.smul_mem _ (W.add_mem (hN 1 h1) (W.smul_mem _ (hN _ hI)))
  · intro a ha
    obtain ⟨⟨⟨j, k⟩, u⟩, hx, rfl⟩ := Finset.mem_image.mp ha
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨⟨hj, hk⟩, hu⟩ := hx
    have hjk := hne j k hj hk
    have hd : (fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) j =
        -(fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1) k := by
      simp [hj, not_lt.mpr hk]
    refine ⟨rot_unitary hjk (hUs u hu).1 _ hd, Matrix.diagonal fun i : Fin r => if (i : ℕ) < p then (1 : ℂ) else -1, ?_, ?_⟩
    · rw [Matrix.diagonal_transpose, Matrix.diagonal_map (map_zero _), Matrix.diagonal_mul_diagonal,
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      split_ifs <;> simp
    · rw [rot_inv hjk (hUs u hu).1]
      exact diag_rot _ hd u
end GlobalTheory
