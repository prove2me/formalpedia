-- Prove2me | solution 1 for GlobalTheory.ExistsSmulMemRange.exists_coeffs
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:18.851902+00:00
-- url     : https://prove2.me/submissions/21e1a3ba-a961-4bf1-9f16-50249ff5b596

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange
import Theorems.Thm_GlobalTheory_ExistsSmulMemRange_exists_smul_mem_range

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.ExistsSmulMemRange
namespace GlobalTheory.ExistsSmulMemRange
theorem _root_.solution {E : Type} [Field E] [NumberField E] {Λ : Type} [AddCommGroup Λ]
    [Module (RingOfIntegers E) Λ] {r : ℕ} (φ : Λ →ₗ[RingOfIntegers E] Fin r → E)
    (hinj : Function.Injective (⇑φ : Λ → Fin r → E))
    (hspan : Submodule.span E (Set.range (⇑φ : Λ → Fin r → E)) = ⊤)
    (σ : E →+* ℂ) (f : Λ →+ ℂ)
    (hf : ∀ (a : RingOfIntegers E) (x : Λ), f (a • x) = σ (↑a : E) * f x) :
    ∃ (c : Fin r → ℂ), ∀ (v : Λ), f v = ∑ j : Fin r, c j * σ (φ v j) := by
  classical
  have h1 : ∀ j : Fin r, ∃ (a : RingOfIntegers E) (x : Λ), a ≠ 0 ∧
      φ x = a • (Pi.single j (1 : E) : Fin r → E) :=
    fun j => exists_smul_mem_range φ _ (by rw [hspan]; trivial)
  choose a x ha hx using h1
  have hne : ∀ q : RingOfIntegers E, q ≠ 0 → algebraMap (RingOfIntegers E) E q ≠ 0 :=
    fun q hq0 h => hq0 (IsFractionRing.injective (RingOfIntegers E) E (by simpa using h))
  refine ⟨fun j => f (x j) / σ (algebraMap (RingOfIntegers E) E (a j)), fun v => ?_⟩
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors (RingOfIntegers E))
    (fun j : Fin r => φ v j / algebraMap (RingOfIntegers E) E (a j))
  choose b hb using hd
  have hd0 : algebraMap (RingOfIntegers E) E (d : RingOfIntegers E) ≠ 0 :=
    hne _ (nonZeroDivisors.ne_zero d.2)
  have hb' : ∀ j, algebraMap (RingOfIntegers E) E (b j) =
      algebraMap (RingOfIntegers E) E (d : RingOfIntegers E) *
        (φ v j / algebraMap (RingOfIntegers E) E (a j)) := by
    intro j
    rw [hb j, Algebra.smul_def]
  have key : (d : RingOfIntegers E) • v = ∑ j, b j • x j := by
    apply hinj
    rw [map_smul, map_sum]
    funext i
    simp only [map_smul, hx, Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Pi.single_apply]
    rw [Finset.sum_eq_single i]
    · rw [hb' i]
      have := hne _ (ha i)
      simp only [if_true]
      field_simp
    · intro j _ hj
      simp [hj.symm]
    · simp
  have h2 := congrArg f key
  rw [hf, map_sum] at h2
  have hσd : σ (algebraMap (RingOfIntegers E) E (d : RingOfIntegers E)) ≠ 0 :=
    (map_ne_zero σ).2 hd0
  apply mul_left_cancel₀ hσd
  refine h2.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hf]
  change σ (algebraMap (RingOfIntegers E) E (b j)) * _ = _
  rw [hb' j, map_mul, map_div₀]
  ring
end GlobalTheory.ExistsSmulMemRange
