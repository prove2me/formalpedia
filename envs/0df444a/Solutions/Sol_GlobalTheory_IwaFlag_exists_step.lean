-- Prove2me | solution 1 for GlobalTheory.IwaFlag.exists_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:57:31.320944+00:00
-- url     : https://prove2.me/submissions/fbe8b8b8-5e2a-41ce-9d8b-a53d6652861c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsFlagDualMatrix
import Theorems.Thm_GlobalTheory_IwaFlag_smul_mem_of_sd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IwaFlag
variable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {ρ : ℕ} {c : R →+* R} {ε : R} {O : AddSubgroup R}
  {h : V →ₗ[R] V →ₛₗ[c] R} {M : AddSubgroup V}
namespace GlobalTheory.IwaFlag
theorem _root_.solution (hcc : ∀ a, c (c a) = a) (hεε : ε * ε = ε) (hεc : c ε = ε) (hεO : ε ∈ O) (hOε : ∀ a ∈ O, ε * a = a)
    (hmul : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O) (hcO : ∀ a ∈ O, c a ∈ O) (hP : Princ ε O)
    (hM₁ : ∀ y ∈ M, ε • y = y) (hM₂ : ∀ y, ε • y = y → (y ∈ M ↔ ∀ x ∈ M, h y x ∈ O))
    (X : (Fin ρ → R) →ₗ[R] V) (f : Fin ρ → V) (hXf : ∀ t k, h (X t) (f k) = t k) (N : ℕ) (hN : 0 < N)
    (he : ∀ k, X (Pi.single k ((N : R) * ε)) ∈ M) (hf : ∀ k, ((N : R) * ε) • f k ∈ M)
    (b : Fin ρ → Fin ρ → R) (hb₁ : ∀ i l, i < l → b i l = 0) (hb₂ : ∀ i, X (b i) ∈ M) (j : Fin ρ) (α' : R)
    (hα : b j j * α' = ε) (hJ : ∀ t : Fin ρ → R, (∀ l, j < l → t l = 0) → X t ∈ M → α' * t j ∈ O)
    (ih : ∀ z : Fin ρ → R, (∀ i, z i ∈ O) → ∃ y ∈ M, ∀ i, i < j → h (X (b i)) y = z i) :
    ∃ w ∈ M, (∀ i, i < j → h (X (b i)) w = 0) ∧ h (X (b j)) w = ε := by
  classical
  have hint : ∀ i, ∀ y ∈ M, h (X (b i)) y ∈ O := fun i => (hM₂ _ (hM₁ _ (hb₂ i))).1 (hb₂ i)
  have hsm : ∀ {o : R}, o ∈ O → ∀ {y : V}, y ∈ M → o • y ∈ M := fun ho _ hy => smul_mem_of_sd hmul hM₁ hM₂ ho hy
  let K : AddSubgroup R :=
    { carrier := {a | ∃ y ∈ M, (∀ i, i < j → h (X (b i)) y = 0) ∧ h (X (b j)) y = a}
      zero_mem' := ⟨0, M.zero_mem, fun _ _ => map_zero _, map_zero _⟩
      add_mem' := by
        rintro _ _ ⟨t, h1, h2, rfl⟩ ⟨s, g1, g2, rfl⟩
        exact ⟨t + s, M.add_mem h1 g1, fun l hl => by rw [map_add, h2 l hl, g2 l hl, add_zero], map_add _ _ _⟩
      neg_mem' := by
        rintro _ ⟨t, h1, h2, rfl⟩
        exact ⟨-t, M.neg_mem h1, fun l hl => by rw [map_neg, h2 l hl, neg_zero], map_neg _ _⟩ }
  have hKO : ∀ o ∈ O, ∀ a ∈ K, o * a ∈ K := by
    rintro o ho _ ⟨t, h1, h2, rfl⟩
    exact ⟨c o • t, hsm (hcO o ho) h1, fun l hl => by rw [map_smulₛₗ, h2 l hl, smul_zero],
      by rw [map_smulₛₗ, hcc, smul_eq_mul]⟩
  have hαN : α' * ((N : R) * ε) ∈ O := by
    have := hJ (Pi.single j ((N : R) * ε)) (fun l hl => Pi.single_eq_of_ne hl.ne' _) (he j)
    rwa [Pi.single_eq_same] at this
  have hNK : (N : R) * ε * b j j ∈ K :=
    ⟨_, hf j, fun i hi => by rw [map_smulₛₗ, hXf, hb₁ i j hi, smul_zero],
      by rw [map_smulₛₗ, hXf, map_mul, map_natCast, hεc, smul_eq_mul]⟩
  obtain ⟨β, hβ, β', h1, h2, h3⟩ := hP K
    (by rintro _ ⟨t, h1, -, rfl⟩; exact hOε _ (hint j t h1)) hKO
    ⟨N * N, Nat.mul_pos hN hN, by
      have e : ((N * N : ℕ) : R) * ε = α' * ((N : R) * ε) * ((N : R) * ε * b j j) := by
        push_cast
        linear_combination (-(N : R) * N * ε * ε) * hα - ((N : R) * N * (ε + 1)) * hεε
      rw [e]; exact hKO _ hαN _ hNK⟩
    ⟨1, one_pos, by rintro _ ⟨t, h1, -, rfl⟩; rw [Nat.cast_one, one_mul]; exact hint j t h1⟩
  choose g hg hg' using fun i : Fin ρ => ih (Pi.single i ε) fun l => by
    by_cases hl : l = i
    · rw [hl, Pi.single_eq_same]; exact hεO
    · rw [Pi.single_eq_of_ne hl]; exact O.zero_mem
  let s := Finset.univ.filter (· < j)
  let t : Fin ρ → R := β' • b j - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i
  have hXt : X t = β' • X (b j) - ∑ i ∈ s, (β' * h (X (b j)) (g i)) • X (b i) := by
    simp only [t, map_sub, map_sum, map_smul]
  have htM : X t ∈ M := by
    refine (hM₂ _ ?_).2 fun y hy => ?_
    · rw [hXt, smul_sub, Finset.smul_sum, smul_smul, h1]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [smul_smul, ← mul_assoc, h1]
    · have hy' : y - ∑ i ∈ s, c (h (X (b i)) y) • g i ∈ M :=
        M.sub_mem hy (M.sum_mem fun i _ => hsm (hcO _ (hint i y hy)) (hg i))
      have hK : h (X (b j)) (y - ∑ i ∈ s, c (h (X (b i)) y) • g i) ∈ K := by
        refine ⟨_, hy', fun l hl => ?_, rfl⟩
        rw [map_sub, map_sum, Finset.sum_eq_single l]
        · rw [map_smulₛₗ, hcc, hg' l l hl, Pi.single_eq_same, smul_eq_mul, mul_comm, hOε _ (hint l y hy), sub_self]
        · intro i _ hi
          rw [map_smulₛₗ, hg' i l hl, Pi.single_eq_of_ne hi.symm, smul_zero]
        · intro hl'; exact absurd (by simpa [s] using hl) hl'
      have := h3 _ hK
      convert this using 1
      rw [hXt]
      simp only [map_sub, map_sum, map_smul, map_smulₛₗ, LinearMap.sub_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, smul_eq_mul, hcc, mul_sub, Finset.mul_sum, RingHom.id_apply]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
  have hz : ∀ l, j ≤ l → (∑ i ∈ s, (β' * h (X (b j)) (g i)) • b i) l = 0 := fun l hl => by
    rw [Finset.sum_apply]
    exact Finset.sum_eq_zero fun i hi => by
      rw [Pi.smul_apply, hb₁ i l (lt_of_lt_of_le (Finset.mem_filter.1 hi).2 hl), smul_zero]
  have hβ' : β' ∈ O := by
    have := hJ t (fun l hl => by
      simp only [t]
      rw [Pi.sub_apply, hz l hl.le, Pi.smul_apply, hb₁ j l hl, smul_zero, sub_zero]) htM
    simp only [t] at this
    rw [Pi.sub_apply, hz j le_rfl, Pi.smul_apply, sub_zero, smul_eq_mul] at this
    have e : α' * (β' * b j j) = β' := by linear_combination β' * hα + h1
    rwa [e] at this
  have := hKO _ hβ' _ hβ
  rw [mul_comm, h2] at this
  exact this
end GlobalTheory.IwaFlag
