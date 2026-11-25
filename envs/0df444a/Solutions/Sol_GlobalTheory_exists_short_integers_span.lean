-- Prove2me | solution 1 for GlobalTheory.exists_short_integers_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:37:33.264866+00:00
-- url     : https://prove2.me/submissions/635fb311-8426-4153-99f6-b525e9b7b12c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GaussianTailBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_ExistsShortIntegersSpan
import Theorems.Thm_GlobalTheory_exists_short_vectors


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.FD
namespace GlobalTheory
theorem _root_.solution :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ (n : ℕ) (ω : Fin n → 𝓞 E),
      (∀ j (σ : E →+* ℂ), ‖σ (ω j)‖ ≤ omStar (E := E)) ∧
        ∀ α : 𝓞 E, (α : E) ∈ Submodule.span ℚ (Set.range fun j => (ω j : E)) := by
  intro E _ _ _
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have hΛ : ∀ x, x ∈ Λ ↔ IsIntegral ℤ (x 0) := by
    intro x
    rw [Submodule.mem_span_singleton]
    constructor
    · rintro ⟨a, rfl⟩
      have : (a • (fun _ => 1 : Fin 1 → E)) 0 = (a : E) := by
        simp [Algebra.smul_def]
      rw [this]
      exact a.isIntegral_coe
    · intro h
      refine ⟨⟨x 0, h⟩, ?_⟩
      funext k
      rw [Subsingleton.elim k 0]
      exact mul_one (x 0)
  have hh : ∀ x y : Fin 1 → E, herm 1 x y = x 0 * cc (y 0) := by
    intro x y
    simp [herm]
  have hc : ∀ x : E, IsIntegral ℤ x → IsIntegral ℤ (cc x) := fun x hx =>
    hx.map (IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom
  obtain ⟨v, hv, -, hsp, hle⟩ := exists_short_vectors Λ (Submodule.fg_span_singleton _)
    (fun x hx y hy => by
      rw [hh]
      exact ((hΛ x).1 hx).mul (hc _ ((hΛ y).1 hy)))
    (fun x hx => by
      have := hx (fun _ => 1) (Submodule.mem_span_singleton_self _)
      rw [hh] at this
      rw [hΛ]
      simpa [cc] using this)
  refine ⟨_, fun j => ⟨v j 0, (hΛ _).1 (hv j)⟩, fun j σ => ?_, fun α => ?_⟩
  · have h := hle j σ
    have he : 2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * ((1 : ℕ) : ℝ) ^ 2 * rdE E = omStar (E := E) := by
      simp only [omStar, Nat.cast_one, one_pow, mul_one]
      rfl
    have h0 : 0 ≤ omStar (E := E) := by
      unfold omStar PT.rd
      positivity
    rw [he, Fin.sum_univ_one] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) h0 two_ne_zero).1 h
  · have h : (fun _ => (α : E) : Fin 1 → E) ∈ Submodule.span ℚ (Set.range v) :=
      hsp ▸ Submodule.mem_top
    have h2 := Submodule.mem_map_of_mem (f := LinearMap.proj (R := ℚ) (φ := fun _ : Fin 1 => E) 0) h
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
end GlobalTheory
