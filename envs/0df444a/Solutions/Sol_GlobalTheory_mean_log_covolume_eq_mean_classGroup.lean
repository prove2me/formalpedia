-- Prove2me | solution 1 for GlobalTheory.mean_log_covolume_eq_mean_classGroup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:59.249114+00:00
-- url     : https://prove2.me/submissions/01bec06d-1b42-4956-8a52-6d056913db5a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_SumLogNormEmbeddingEqFinrankMulLogAbsNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeCmEqIdealAndCovolume
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_LatticeDeterminedByInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MeanLogCovolumeEqMeanClassGroup
import Theorems.Thm_GlobalTheory_latticeArea_eq_abs_im_mul_conj
import Theorems.Thm_GlobalTheory_latticeNormDisc_eq
import Theorems.Thm_GlobalTheory_IsHomothetic_latticeNormDisc_eq
import Theorems.Thm_GlobalTheory_mem_conjPeriods_lattice
import Theorems.Thm_GlobalTheory_latticeNormDisc_conjPeriods
import Theorems.Thm_GlobalTheory_embedding_eq_or_eq_conjugate
import Theorems.Thm_GlobalTheory_exists_isHomothetic_of_mk0_eq
import Theorems.Thm_GlobalTheory_HasQExpansion_congr
import Theorems.Thm_GlobalTheory_HasQExpansion_mul
import Theorems.Thm_GlobalTheory_lattice_cm_eq_ideal_and_covolume
import Theorems.Thm_GlobalTheory_sum_log_norm_embedding_eq_finrank_mul_log_absNorm
import Theorems.Thm_P2M_GlobalTheory_g__cube_sub_g__sq_ne_zero_9f5991ca482c


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex NumberField
open scoped nonZeroDivisors Real UpperHalfPlane
noncomputable section
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M], Module.finrank ℚ K = 2 →
  ∀ (σ₀ : K →+* ℂ), ¬ NumberField.ComplexEmbedding.IsReal σ₀ →
  ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))) (Lc : ClassGroup (𝓞 K) → PeriodPair), (∀ C, ClassGroup.mk0 (𝔟 C) = C) →
  (∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ₀ (a : K)) →
  ∀ (L₀ : (M →+* ℂ) → PeriodPair) (L : ClassGroup (𝓞 K) → (M →+* ℂ) → PeriodPair) (δ : ClassGroup (𝓞 K) → (𝓞 M)ˣ) (β : ClassGroup (𝓞 K) → M),
  (∀ s (a : 𝓞 K), ∀ z ∈ (L₀ s).lattice, s (algebraMap K M a) * z ∈ (L₀ s).lattice) →
  (∀ C s, (L C s).g₂ ^ 3 - 27 * (L C s).g₃ ^ 2 = s ((δ C : 𝓞 M) : M)) → (∀ C, β C ≠ 0) →
  (∀ C (x : K), (∀ b ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ (x * (b : K))) → IsIntegral ℤ (β C * algebraMap K M x) ∧
    ∀ s, ∀ z ∈ (L₀ s).lattice, s (β C * algebraMap K M x) * z ∈ (L C s).lattice) →
  (∀ C, ∀ y ∈ (𝔟 C : Ideal (𝓞 K)), IsIntegral ℤ ((β C)⁻¹ * algebraMap K M (y : K)) ∧
    ∀ s, ∀ z ∈ (L C s).lattice, s ((β C)⁻¹ * algebraMap K M (y : K)) * z ∈ (L₀ s).lattice) →
  (∑ s : M →+* ℂ, Real.log |((L₀ s).ω₁ * starRingEnd ℂ (L₀ s).ω₂).im|) / Module.finrank ℚ M =
    (∑ C, Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖)) / (6 * Fintype.card (ClassGroup (𝓞 K))) := by
  intro K M _ _ _ _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hLc L₀ L δ β hst hδ hβ h1 h2
  simp only [← latticeNormDisc_eq]
  simp only [← latticeArea_eq_abs_im_mul_conj]
  have hb0 : ∀ C, (𝔟 C : Ideal (𝓞 K)) ≠ ⊥ := fun C => nonZeroDivisors.coe_ne_zero _
  have hnr : ∀ s : M →+* ℂ, ¬ ComplexEmbedding.IsReal (s.comp (algebraMap K M)) := by
    intro s
    rcases embedding_eq_or_eq_conjugate hK h₀ (s.comp (algebraMap K M)) with h | h <;> rw [h]
    · exact h₀
    · rwa [ComplexEmbedding.isReal_conjugate_iff]
  have hlat := fun C s => lattice_cm_eq_ideal_and_covolume K hK (s.comp (algebraMap K M)) (hnr s)
    (L₀ s) (L C s) (hst s)
  have hsβ : ∀ C (s : M →+* ℂ), s (β C) ≠ 0 := fun C s => (map_ne_zero s).2 (hβ C)
  have hdiv := fun C s => (hlat C s).2 (𝔟 C) (s (β C)) (hb0 C) (hsβ C s)
    (fun x hx z hz => by simpa using (h1 C x hx).2 s z hz)
    (fun y hy z hz => by simpa using (h2 C y hy).2 s z hz)

  have hA : ∀ C, ∑ s, Real.log (latticeNormDisc (L C s)) =
      6 * ∑ s, Real.log (latticeArea (L₀ s)) := by
    intro C
    have hN : (Ideal.absNorm (𝔟 C : Ideal (𝓞 K)) : ℝ) ≠ 0 := by
      exact_mod_cast Ideal.absNorm_eq_zero_iff.not.2 (hb0 C)
    have hδ0 : ((δ C : 𝓞 M) : M) ≠ 0 := by exact_mod_cast (δ C).ne_zero
    have e1 : ∑ s : M →+* ℂ, Real.log ‖s ((δ C : 𝓞 M) : M)‖ = 0 := by
      have := sum_log_norm_embedding_eq_finrank_mul_log_absNorm M M ⊤ ((δ C : 𝓞 M) : M)
        top_ne_bot hδ0
        (fun x hx => (RingOfIntegers.isIntegral_coe _).mul (by simpa using hx 1 trivial))
        (fun y _ => by
          have : (((δ C : 𝓞 M) : M))⁻¹ = (((δ C)⁻¹ : (𝓞 M)ˣ) : 𝓞 M) := by
            apply inv_eq_of_mul_eq_one_right
            rw [← map_mul]; simp
          rw [this]
          exact (RingOfIntegers.isIntegral_coe _).mul (RingOfIntegers.isIntegral_coe _))
      simpa using this
    have e2 := sum_log_norm_embedding_eq_finrank_mul_log_absNorm K M (𝔟 C) (β C) (hb0 C) (hβ C)
      (fun x hx => (h1 C x hx).1) (fun y hy => (h2 C y hy).1)
    have e3 : ∀ s : M →+* ℂ, Real.log (latticeNormDisc (L C s)) =
        6 * (2 * Real.log ‖s (β C)‖ + Real.log (latticeArea (L₀ s)) -
          Real.log (Ideal.absNorm (𝔟 C : Ideal (𝓞 K)) : ℝ)) +
          Real.log ‖s ((δ C : 𝓞 M) : M)‖ := by
      intro s
      have h := congrArg Real.log (hdiv C s).2
      rw [← latticeArea_eq_abs_im_mul_conj, ← latticeArea_eq_abs_im_mul_conj,
        Real.log_mul (latticeArea_pos _).ne' hN,
        Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 (hsβ C s))) (latticeArea_pos _).ne',
        Real.log_pow] at h
      rw [latticeNormDisc, Real.log_mul (pow_pos (latticeArea_pos _) _).ne'
        (norm_ne_zero_iff.2 (g₂_cube_sub_g₃_sq_ne_zero _)), Real.log_pow, hδ]
      push_cast at h ⊢
      linarith
    have e4 : (Fintype.card (M →+* ℂ) : ℝ) = 2 * Module.finrank K M := by
      rw [Embeddings.card, ← Module.finrank_mul_finrank ℚ K M, hK]
      push_cast; ring
    simp only [e3, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, e4]
    ring

  have hB : ∀ s, ∑ C, Real.log (latticeNormDisc (L C s)) =
      ∑ C, Real.log (latticeNormDisc (Lc C)) := by
    intro s
    obtain ⟨𝔞, c, h𝔞, hc, hL⟩ := (hlat 1 s).1
    let 𝔞' : (Ideal (𝓞 K))⁰ := ⟨𝔞, mem_nonZeroDivisors_of_ne_zero h𝔞⟩
    refine Fintype.sum_equiv (Equiv.divLeft (ClassGroup.mk0 𝔞')) _ _ fun C => ?_
    congr 1
    have hcl : ClassGroup.mk0 (𝔟 (ClassGroup.mk0 𝔞' / C)) * ClassGroup.mk0 (𝔟 C) =
        ClassGroup.mk0 𝔞' := by
      rw [h𝔟, h𝔟, div_mul_cancel]
    change _ = latticeNormDisc (Lc (ClassGroup.mk0 𝔞' / C))
    rcases embedding_eq_or_eq_conjugate hK h₀ (s.comp (algebraMap K M)) with h | h
    · obtain ⟨κ, H⟩ := exists_isHomothetic_of_mk0_eq (s.comp (algebraMap K M)) 𝔞' _ _ hcl hc
        (hsβ C s) hL (hdiv C s).1 (P := Lc (ClassGroup.mk0 𝔞' / C)) (by rw [h]; exact hLc _)
      exact H.latticeNormDisc_eq
    · obtain ⟨κ, H⟩ := exists_isHomothetic_of_mk0_eq (s.comp (algebraMap K M)) 𝔞' _ _ hcl hc
        (hsβ C s) hL (hdiv C s).1 (P := conjPeriods (Lc (ClassGroup.mk0 𝔞' / C))) (by
          intro z
          rw [h, mem_conjPeriods_lattice, hLc]
          refine exists_congr fun a => and_congr_right fun _ => ?_
          rw [ComplexEmbedding.conjugate_coe_eq]
          constructor
          · intro e; rw [← e]; simp
          · intro e; rw [e]; simp)
      rw [H.latticeNormDisc_eq, latticeNormDisc_conjPeriods]
  have hS := Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
    (f := fun C s => Real.log (latticeNormDisc (L C s)))
  simp only [hA, hB, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Embeddings.card] at hS
  have hm : (Module.finrank ℚ M : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  linear_combination hS
end GlobalTheory
