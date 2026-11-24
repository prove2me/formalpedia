-- Prove2me | solution 1 for GlobalTheory.PicDom.finiteDimensional_of_isFractionRing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:27:07.110486+00:00
-- url     : https://prove2.me/submissions/945b3741-d2e5-4d50-b19b-a6942c4eff23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOfFinOrderOfIsOfFinOrderMapRingHomStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PicIsOfFinOrderOfFiniteInt
import Theorems.Thm_GlobalTheory_PicDom_exists_int_mem_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PicDom
variable (B : Type) [CommRing B] [IsDomain B] [Module.Finite ℤ B] [CharZero B]
namespace GlobalTheory.PicDom
theorem _root_.solution (K : Type) [Field K] [Algebra B K] [IsFractionRing B K] [CharZero K] :
    FiniteDimensional ℚ K := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have key : ∀ y : B, algebraMap B K y ∈
      Submodule.span ℚ (algebraMap B K '' (s : Set B)) := fun y => by
    have hy : y ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_zsmul]; exact zsmul_mem hx a
  classical
  refine Module.finite_def.2 ⟨s.image (algebraMap B K), ?_⟩
  rw [Finset.coe_image, eq_top_iff]
  intro x _
  obtain ⟨b, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := B) x
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  obtain ⟨a, ha0, ha⟩ := exists_int_mem_span hd0
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 ha
  have hdK : algebraMap B K d ≠ 0 := by
    rwa [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective B K)]
  have haK : (a : K) ≠ 0 := by exact_mod_cast ha0
  have : algebraMap B K b / algebraMap B K d =
      ((a : ℚ)⁻¹) • algebraMap B K (c * b) := by
    rw [Rat.smul_def, map_mul, Rat.cast_inv, Rat.cast_intCast]
    have h2 : (a : K) = algebraMap B K c * algebraMap B K d := by
      rw [← map_mul, hc, map_intCast]
    have hcK : algebraMap B K c ≠ 0 := by
      intro h; apply haK; rw [h2, h, zero_mul]
    rw [h2]
    field_simp
  rw [this]
  exact Submodule.smul_mem _ _ (key _)
end GlobalTheory.PicDom
