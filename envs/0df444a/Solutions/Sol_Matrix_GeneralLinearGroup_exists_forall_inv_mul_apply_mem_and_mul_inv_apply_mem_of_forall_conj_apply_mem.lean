-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/efc32f35-df13-5ab4-8384-966fc8630b35

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem

set_option autoImplicit false

theorem solution
    {K : Type*} [Field K] (𝒪 : ValuationSubring K) {n : Type*} [Fintype n] [DecidableEq n]
    (g : GL n K)
    (hg : ∀ M : Matrix n n K, (∀ i j, M i j ∈ 𝒪) →
      ∀ i j, ((g : Matrix n n K) * M * ((g⁻¹ : GL n K) : Matrix n n K)) i j ∈ 𝒪) :
    ∃ c : Kˣ, (∀ i j, ((c⁻¹ : Kˣ) : K) * (g : Matrix n n K) i j ∈ 𝒪) ∧
      (∀ i j, (c : K) * ((g⁻¹ : GL n K) : Matrix n n K) i j ∈ 𝒪) := by
  classical

  have hprod : ∀ i j k l, (g : Matrix n n K) i j * ((g⁻¹ : GL n K) : Matrix n n K) k l ∈ 𝒪 := by
    intro i j k l
    have hint : ∀ a b, Matrix.single j k (1 : K) a b ∈ 𝒪 := by
      intro a b
      by_cases hab : a = j ∧ b = k
      · obtain ⟨rfl, rfl⟩ := hab
        rw [Matrix.single_apply_same]; exact one_mem _
      · rw [Matrix.single_apply_of_ne]
        · exact zero_mem _
        · rintro ⟨h1, h2⟩; exact hab ⟨h1.symm, h2.symm⟩
    have h := hg (Matrix.single j k (1 : K)) hint i l
    have e : ((g : Matrix n n K) * Matrix.single j k (1 : K) * ((g⁻¹ : GL n K) : Matrix n n K)) i l =
        (g : Matrix n n K) i j * ((g⁻¹ : GL n K) : Matrix n n K) k l := by
      rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single j]
      · rw [Matrix.single_mul_apply_same, one_mul]
      · intro b _ hb
        rw [Matrix.single_mul_apply_of_ne (h := hb), mul_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [e] at h
    exact h

  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, fun i => isEmptyElim i, fun i => isEmptyElim i⟩

  obtain ⟨⟨i₀, j₀⟩, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (n × n))
    (fun p => 𝒪.valuation ((g : Matrix n n K) p.1 p.2)) Finset.univ_nonempty
  have hm0 : (g : Matrix n n K) i₀ j₀ ≠ 0 := by
    intro h0
    have hall : ∀ i j, (g : Matrix n n K) i j = 0 := by
      intro i j
      have hle := hmax ⟨i, j⟩ (Finset.mem_univ _)
      simp only [h0, map_zero, le_zero_iff, map_eq_zero] at hle
      exact hle
    have hz : (g : Matrix n n K) = 0 := by ext i j; exact hall i j
    apply Matrix.GeneralLinearGroup.det_ne_zero g
    show (g : Matrix n n K).det = 0
    rw [hz, Matrix.det_zero]
  refine ⟨Units.mk0 _ hm0, ?_, ?_⟩
  · intro i j
    show ((g : Matrix n n K) i₀ j₀)⁻¹ * (g : Matrix n n K) i j ∈ 𝒪
    have hle := hmax ⟨i, j⟩ (Finset.mem_univ _)
    rw [← 𝒪.valuation_le_one_iff, map_mul, map_inv₀]
    have hv0 : 𝒪.valuation ((g : Matrix n n K) i₀ j₀) ≠ 0 := by rwa [ne_eq, map_eq_zero]
    calc (𝒪.valuation ((g : Matrix n n K) i₀ j₀))⁻¹ * 𝒪.valuation ((g : Matrix n n K) i j)
        ≤ (𝒪.valuation ((g : Matrix n n K) i₀ j₀))⁻¹ * 𝒪.valuation ((g : Matrix n n K) i₀ j₀) :=
          mul_le_mul_right hle _
      _ = 1 := inv_mul_cancel₀ hv0
  · intro k l
    exact hprod i₀ j₀ k l

end S_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem
end P2MW
export P2MW.S_Matrix_GeneralLinearGroup_exists_forall_inv_mul_apply_mem_and_mul_inv_apply_mem_of_forall_conj_apply_mem (solution)
