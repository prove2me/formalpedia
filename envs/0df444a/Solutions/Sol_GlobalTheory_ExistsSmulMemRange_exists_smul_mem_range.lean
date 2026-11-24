-- Prove2me | solution 1 for GlobalTheory.ExistsSmulMemRange.exists_smul_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:44:34.167913+00:00
-- url     : https://prove2.me/submissions/e3e6a0c1-c393-48cf-8acc-fa30102fa3a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemRange

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
    (w : Fin r → E) (hw : w ∈ Submodule.span E (Set.range (⇑φ : Λ → Fin r → E))) :
    ∃ (a : RingOfIntegers E) (x : Λ), a ≠ 0 ∧ φ x = a • w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, rfl⟩ := hw
    exact ⟨1, x, one_ne_zero, (one_smul _ _).symm⟩
  | zero => exact ⟨1, 0, one_ne_zero, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, x, ha, hx⟩ := hu
    obtain ⟨b, y, hb, hy⟩ := hv
    refine ⟨a * b, b • x + a • y, mul_ne_zero ha hb, ?_⟩
    rw [map_add, map_smul, map_smul, hx, hy, smul_add, smul_smul, smul_smul, mul_comm b a]
  | smul t u _ hu =>
    obtain ⟨a, x, ha, hx⟩ := hu
    obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := RingOfIntegers E) t
    have hq0 : q ≠ 0 := nonZeroDivisors.ne_zero hq
    have hq1 : algebraMap (RingOfIntegers E) E q ≠ 0 :=
      fun h => hq0 (IsFractionRing.injective (RingOfIntegers E) E (by simpa using h))
    refine ⟨a * q, p • x, mul_ne_zero ha hq0, ?_⟩
    rw [map_smul, hx]
    funext j
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [Algebra.smul_def, map_mul]
    field_simp
end GlobalTheory.ExistsSmulMemRange
