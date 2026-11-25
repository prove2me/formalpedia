-- Prove2me | solution 1 for GlobalTheory.LatticeCovolumeL2.finrank_int_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:02:07.718165+00:00
-- url     : https://prove2.me/submissions/727a7f25-c920-4773-88d4-e5863a98b25b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsLineBasis

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LatticeCovolumeL2
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.LatticeCovolumeL2
theorem _root_.solution {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X]
    (h : Module.finrank (𝓞 E) X = 1) : Module.finrank ℤ X ≤ Module.finrank ℚ E := by
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  obtain ⟨x, hx⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) (n := 1) h.ge
  have hx0 : ∀ c : 𝓞 E, c • x 0 = 0 → c = 0 := by
    intro c hc
    exact linearIndependent_iff'.1 hx Finset.univ (fun _ => c) (by simpa using hc) 0 (Finset.mem_univ _)
  have key : ∀ y : X, ∃ N : ℤ, N ≠ 0 ∧ ∃ α : 𝓞 E, N • y = α • x 0 := by
    intro y
    have hdep : ¬ LinearIndependent (𝓞 E) ![x 0, y] := by
      intro hli
      have := hli.fintype_card_le_finrank
      rw [h] at this
      simp at this
    rw [LinearIndependent.pair_iff] at hdep
    push Not at hdep
    obtain ⟨s, t, hst, hne⟩ := hdep
    have ht : t ≠ 0 := by
      intro ht0
      rw [ht0, zero_smul, add_zero] at hst
      exact hne (hx0 s hst) ht0
    have hI := Ideal.comap_ne_bot_of_integral_mem (R := ℤ) (I := Ideal.span {t}) ht
      (Ideal.mem_span_singleton_self t) (NumberField.RingOfIntegers.isIntegral t)
    obtain ⟨N, hN, hN0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
    rw [Ideal.mem_comap, Ideal.mem_span_singleton] at hN
    obtain ⟨c, hc⟩ := hN
    refine ⟨N, hN0, -(c * s), ?_⟩
    have hty : t • y = -(s • x 0) := eq_neg_of_add_eq_zero_right hst
    rw [← algebraMap_smul (𝓞 E) N y, hc, mul_comm t c, mul_smul, hty]
    simp [smul_neg, mul_smul]
  obtain ⟨yv, hy⟩ := exists_linearIndependent_of_le_finrank (R := ℤ) (M := X) (le_refl (Module.finrank ℤ X))
  choose N hN α hα using fun i => key (yv i)
  let N0 : ℤ := ∏ i, N i
  have hN0 : N0 ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hN i
  let φ : 𝓞 E →ₗ[ℤ] X := (LinearMap.toSpanSingleton (𝓞 E) X (x 0)).restrictScalars ℤ
  let β : Fin (Module.finrank ℤ X) → 𝓞 E := fun i => ((∏ j ∈ Finset.univ.erase i, N j : ℤ) : 𝓞 E) * α i
  have hβ : ∀ i, φ (β i) = N0 • yv i := by
    intro i
    show (((∏ j ∈ Finset.univ.erase i, N j : ℤ) : 𝓞 E) * α i) • x 0 = N0 • yv i
    rw [mul_smul, ← hα i, Int.cast_smul_eq_zsmul, smul_smul, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  have hli : LinearIndependent ℤ (φ ∘ β) := by
    have hfun : φ ∘ β = fun i => N0 • yv i := funext hβ
    rw [hfun]
    rw [linearIndependent_iff'] at hy ⊢
    intro s g hg i hi
    have := hy s (fun j => g j * N0) (by simpa [smul_smul] using hg) i hi
    exact (mul_eq_zero.1 this).resolve_right hN0
  have := (LinearIndependent.of_comp φ hli).fintype_card_le_finrank
  simpa [NumberField.RingOfIntegers.rank] using this
end GlobalTheory.LatticeCovolumeL2
