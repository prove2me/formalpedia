-- Prove2me | solution 1 for GlobalTheory.Hk.RayForm.exists_basis_im
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:32:24.99327+00:00
-- url     : https://prove2.me/submissions/ed993238-e4ae-4722-a77d-5d9ee74ac7fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_PlaneLatticeShortBasisOfBoundPowTwo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_RingOfIntegersSqrtNegThreeModFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassIdealCountEqNcardShiftedBinaryForm
import Theorems.Thm_GlobalTheory_eq_I_mul_sqrt_or_of_sq_eq_neg
import Theorems.Thm_GlobalTheory_exists_integer_generator_of_sq_eq_neg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RayForm
open GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RayForm
theorem _root_.solution {d : ℕ} (hp : d.Prime) (hd : d % 4 = 3) {x : K} (hx : x ^ 2 = -(d : K))
    (h2 : Module.finrank ℚ K = 2) (φ : K →+* ℂ) :
    ∃ b : Module.Basis (Fin 2) ℤ (𝓞 K),
      (starRingEnd ℂ (φ (b 0 : K)) * φ (b 1 : K)).im ^ 2 = d / 4 := by
  obtain ⟨w, hw, hall⟩ := GlobalTheory.exists_integer_generator_of_sq_eq_neg h2 (Irreducible.squarefree hp) hd hx
  have hφx : φ x ^ 2 = -(d : ℂ) := by rw [← map_pow, hx]; simp
  have hφw : φ (w : K) = (1 + φ x) / 2 := by
    have := congrArg φ hw
    simp only [map_mul, map_add, map_one, map_ofNat] at this
    linear_combination this / 2
  have hsd : (0 : ℝ) < √(d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
  have him : (φ (w : K)).im = √(d : ℝ) / 2 ∨ (φ (w : K)).im = -(√(d : ℝ) / 2) := by
    rcases GlobalTheory.eq_I_mul_sqrt_or_of_sq_eq_neg hφx with h | h
    · left
      rw [hφw, h]
      simp
    · right
      rw [hφw, h]
      simp
      ring
  have himne : (φ (w : K)).im ≠ 0 := by
    rcases him with h | h <;> rw [h] <;> [exact (by positivity); exact neg_ne_zero.mpr (by positivity)]
  have hli : LinearIndependent ℤ ![(1 : 𝓞 K), w] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 : t = 0 ∨ (φ (w : K)).im = 0 := by
      have := congrArg (fun z : 𝓞 K => (φ (z : K)).im) hst
      simpa [zsmul_eq_mul] using this
    have ht : t = 0 := h1.resolve_right himne
    subst ht
    refine ⟨?_, rfl⟩
    simpa using hst
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) := by
    intro c _
    obtain ⟨m, n, hc⟩ := hall c
    have h1 : (1 : 𝓞 K) ∈ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) :=
      Submodule.subset_span ⟨0, rfl⟩
    have h2' : w ∈ Submodule.span ℤ (Set.range ![(1 : 𝓞 K), w]) :=
      Submodule.subset_span ⟨1, rfl⟩
    have := Submodule.add_mem _ (Submodule.smul_mem _ m h1) (Submodule.smul_mem _ n h2')
    rw [hc]
    simpa [zsmul_eq_mul] using this
  refine ⟨Module.Basis.mk hli hsp, ?_⟩
  have hbw : ((starRingEnd ℂ) (φ (((Module.Basis.mk hli hsp) 0 : 𝓞 K) : K)) *
      φ (((Module.Basis.mk hli hsp) 1 : 𝓞 K) : K)).im = (φ (w : K)).im := by
    simp [Module.Basis.mk_apply]
  rw [hbw]
  have hsq : (√(d : ℝ)) ^ 2 = d := Real.sq_sqrt (Nat.cast_nonneg _)
  rcases him with h | h <;> rw [h] <;> [skip; rw [neg_sq]] <;> rw [div_pow, hsq] <;> norm_num
end GlobalTheory.Hk.RayForm
