-- Prove2me | solution 1 for GlobalTheory.coords_in_rational_symplectic_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:52.829419+00:00
-- url     : https://prove2.me/submissions/c7300081-ad73-4345-9cdd-6e913eaa3105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_CoordsEqPairingsRationalSymplecticBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε φ : Fin g → Fin r → ℚ), r = 2 * g → Mqᵀ = -Mq →
      Mq.det ≠ 0 → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) →
      (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) →
      ∀ x : Fin r → ℚ, x = ∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j := by
  intro g r Mq ε φ hr hskew hdet hεε hφφ hφε x
  rcases Nat.eq_zero_or_pos g with hg | hg
  · funext i
    exact absurd i.2 (by omega)
  have hsk : ∀ u v : Fin r → ℚ, u ⬝ᵥ Mq *ᵥ v = -(v ⬝ᵥ Mq *ᵥ u) := by
    intro u v
    rw [dotProduct_mulVec, ← mulVec_transpose, hskew, dotProduct_comm, neg_mulVec, dotProduct_neg]
  have hεφ : ∀ i k, ε i ⬝ᵥ Mq *ᵥ φ k = -(if i = k then 1 else 0) := by
    intro i k
    rw [hsk, hφε]

  have pε : ∀ (a b : Fin g → ℚ) k,
      (∑ i, a i • ε i + ∑ j, b j • φ j) ⬝ᵥ Mq *ᵥ ε k = b k := by
    intro a b k
    simp [add_dotProduct, sum_dotProduct, smul_dotProduct, hεε, hφε]
  have pφ : ∀ (a b : Fin g → ℚ) k,
      (∑ i, a i • ε i + ∑ j, b j • φ j) ⬝ᵥ Mq *ᵥ φ k = -a k := by
    intro a b k
    simp [add_dotProduct, sum_dotProduct, smul_dotProduct, hφφ, hεφ]

  set v : Fin g ⊕ Fin g → Fin r → ℚ := Sum.elim ε φ with hv
  have hli : LinearIndependent ℚ v := by
    rw [Fintype.linearIndependent_iff]
    intro c hc s
    rw [Fintype.sum_sum_type] at hc
    simp only [hv, Sum.elim_inl, Sum.elim_inr] at hc
    rcases s with k | k
    · have := pφ (fun i => c (Sum.inl i)) (fun j => c (Sum.inr j)) k
      rw [hc, zero_dotProduct] at this
      linarith
    · have := pε (fun i => c (Sum.inl i)) (fun j => c (Sum.inr j)) k
      rw [hc, zero_dotProduct] at this
      linarith
  haveI : Nonempty (Fin g ⊕ Fin g) := ⟨Sum.inl ⟨0, hg⟩⟩
  have hspan : Submodule.span ℚ (Set.range v) = ⊤ := by
    apply hli.span_eq_top_of_card_eq_finrank
    simp [Module.finrank_fin_fun]
    omega

  set z := x - (∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j) with hz
  let f : (Fin r → ℚ) →ₗ[ℚ] ℚ :=
    { toFun := fun y => z ⬝ᵥ Mq *ᵥ y
      map_add' := by intro a b; simp [mulVec_add, dotProduct_add]
      map_smul' := by intro c a; simp [mulVec_smul, dotProduct_smul] }
  have hf : f = 0 := by
    apply LinearMap.ext_on_range hspan
    intro s
    rcases s with k | k
    · show z ⬝ᵥ Mq *ᵥ ε k = 0
      rw [hz, sub_dotProduct, pε]
      ring
    · show z ⬝ᵥ Mq *ᵥ φ k = 0
      rw [hz, sub_dotProduct, pφ]
      ring
  have hzM : z ᵥ* Mq = 0 := by
    funext j
    have h1 : f (Pi.single j 1) = 0 := by rw [hf]; rfl
    have h2 : f (Pi.single j 1) = (z ᵥ* Mq) j := by
      show z ⬝ᵥ Mq *ᵥ Pi.single j 1 = _
      rw [dotProduct_mulVec, dotProduct_single, mul_one]
    rw [← h2, h1]
    rfl
  have hz0 : z = 0 := eq_zero_of_vecMul_eq_zero hdet hzM
  exact sub_eq_zero.mp hz0
end GlobalTheory
