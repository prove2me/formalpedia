-- Prove2me | solution 1 for Matrix.mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/fe342f50-dc4c-5f39-b1d1-f295716b6a0a

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span

set_option autoImplicit false

namespace Matrix
p2m_export "Matrix" "sub_mulVec ext row mulVec_mulVec smul_apply comp_apply of map mulVec_smul mulVec"
p2m_open "Matrix"

theorem exists_smul_vecCons_eq_of_mul_add_mul_eq_zero {K : Type*} [Field K] (a b : K)
    (x : Fin 2 → K) (hab : a ≠ 0 ∨ b ≠ 0) (h : a * x 0 + b * x 1 = 0) :
    ∃ c : K, c • ![b, -a] = x := by
  by_cases ha : a = 0
  · have hb : b ≠ 0 := hab.resolve_left (not_not.mpr ha)
    have hx1 : x 1 = 0 := by
      rw [ha, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_left hb
    refine ⟨x 0 / b, ?_⟩
    funext k
    fin_cases k
    · simp [div_mul_cancel₀ _ hb]
    · simp [ha, hx1]
  · refine ⟨-(x 1) / a, ?_⟩
    funext k
    fin_cases k
    · have hx0 : x 0 = -(b * x 1) / a := by
        field_simp
        linear_combination h
      simp [hx0]
      ring
    · simp [ha]

theorem mem_span_singleton_of_comp_eq_smul_comp {F F' : Type*} [Field F] [Field F']
    (e : F →+* F') {n : Type*} (v w : n → F) (d : F') (h : e ∘ w = d • (e ∘ v))
    (hv : v ≠ 0) : w ∈ F ∙ v := by
  obtain ⟨t, ht⟩ : ∃ t, v t ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv (funext h')
  have het : e (v t) ≠ 0 := (map_ne_zero e).mpr ht
  have hd : d = e (w t / v t) := by
    have h1 := congr_fun h t
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [map_div₀, h1, mul_div_cancel_right₀ _ het]
  refine Submodule.mem_span_singleton.mpr ⟨w t / v t, ?_⟩
  funext s
  apply e.injective
  have h2 := congr_fun h s
  simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at h2
  rw [Pi.smul_apply, smul_eq_mul, map_mul, ← hd, h2]

theorem mul_comm_of_stableLine_impl
    {F F' : Type*} [Field F] [Field F'] (e : F →+* F') {ι : Type*}
    (M : ι → Matrix (Fin 2) (Fin 2) F)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ i, (M i).mulVec v ∉ F ∙ v)
    (u : Fin 2 → F') (hu : u ≠ 0) (hstab : ∀ i, ((M i).map e).mulVec u ∈ F' ∙ u) :
    ∀ i j, M i * M j = M j * M i := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨i, j, hij⟩ := hne
  set N : Matrix (Fin 2) (Fin 2) F := M i * M j - M j * M i with hN
  have hN0 : N ≠ 0 := sub_ne_zero.mpr hij
  obtain ⟨ci, hci⟩ := Submodule.mem_span_singleton.mp (hstab i)
  obtain ⟨cj, hcj⟩ := Submodule.mem_span_singleton.mp (hstab j)

  have hNu : (N.map e).mulVec u = 0 := by
    have hmap : N.map e = (M i).map e * (M j).map e - (M j).map e * (M i).map e := by
      change e.mapMatrix N = e.mapMatrix (M i) * e.mapMatrix (M j) - e.mapMatrix (M j) * e.mapMatrix (M i)
      rw [hN, map_sub, map_mul, map_mul]
    rw [hmap, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hcj, ← hci,
      Matrix.mulVec_smul, Matrix.mulVec_smul, ← hci, ← hcj, smul_smul, smul_smul, mul_comm, sub_self]

  obtain ⟨r, hr⟩ : ∃ r : Fin 2, N r 0 ≠ 0 ∨ N r 1 ≠ 0 := by
    by_contra h'
    push Not at h'
    apply hN0
    ext r c
    fin_cases c
    · exact (h' r).1
    · exact (h' r).2
  have hrow : e (N r 0) * u 0 + e (N r 1) * u 1 = 0 := by
    have h1 := congr_fun hNu r
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h1
  have hab : e (N r 0) ≠ 0 ∨ e (N r 1) ≠ 0 := by
    rcases hr with h0 | h1
    · exact Or.inl ((map_ne_zero e).mpr h0)
    · exact Or.inr ((map_ne_zero e).mpr h1)
  obtain ⟨c, hc⟩ := exists_smul_vecCons_eq_of_mul_add_mul_eq_zero (e (N r 0)) (e (N r 1)) u hab hrow

  set v : Fin 2 → F := ![N r 1, -N r 0] with hv
  have hev : (e ∘ v) = ![e (N r 1), -e (N r 0)] := by
    funext k
    fin_cases k <;> simp [hv]
  have hcu : c • (e ∘ v) = u := by rw [hev]; exact hc
  have hv0 : v ≠ 0 := by
    intro h0
    rcases hr with h0' | h1'
    · exact h0' (by simpa [hv] using congr_fun h0 1)
    · exact h1' (by simpa [hv] using congr_fun h0 0)
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hcu
    exact hu hcu.symm

  obtain ⟨k, hk⟩ := hirr v hv0
  apply hk
  obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp (hstab k)
  have hmv : ((M k).map e).mulVec (e ∘ v) = e ∘ ((M k).mulVec v) := by
    funext t
    exact (RingHom.map_mulVec e (M k) v t).symm
  rw [← hcu, Matrix.mulVec_smul, hmv, smul_comm] at hd
  have hd' : e ∘ ((M k).mulVec v) = d • (e ∘ v) := (smul_right_injective _ hc0 hd).symm
  exact mem_span_singleton_of_comp_eq_smul_comp e v _ d hd' hv0

end Matrix

theorem solution
    {F F' : Type*} [Field F] [Field F'] (e : F →+* F') {ι : Type*}
    (M : ι → Matrix (Fin 2) (Fin 2) F)
    (hirr : ∀ v : Fin 2 → F, v ≠ 0 → ∃ i, (M i).mulVec v ∉ F ∙ v)
    (u : Fin 2 → F') (hu : u ≠ 0) (hstab : ∀ i, ((M i).map e).mulVec u ∈ F' ∙ u) :
    ∀ i j, M i * M j = M j * M i :=
  Matrix.mul_comm_of_stableLine_impl e M hirr u hu hstab

end S_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span
end P2MW
export P2MW.S_Matrix_mul_comm_of_forall_map_mulVec_mem_span_of_forall_exists_mulVec_not_mem_span (solution)
