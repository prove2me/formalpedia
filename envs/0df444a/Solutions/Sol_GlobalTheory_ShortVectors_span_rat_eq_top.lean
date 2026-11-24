-- Prove2me | solution 1 for GlobalTheory.ShortVectors.span_rat_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:48:11.35886+00:00
-- url     : https://prove2.me/submissions/f2d1eaa2-c092-4983-a192-e55f4886408f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD Module Submodule
open GlobalTheory
open GlobalTheory.ShortVectors
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [IsCMField E]
namespace GlobalTheory.ShortVectors
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (h : span E (Λ : Set (Fin n → E)) = ⊤) : span ℚ (Λ : Set (Fin n → E)) = ⊤ := by
  have key : ∀ (a : E) (v : Fin n → E), v ∈ Λ → a • v ∈ span ℚ (Λ : Set (Fin n → E)) := by
    intro a v hv
    obtain ⟨m, s, hm, hs⟩ :=
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)).exists_nsmul_eq
        (𝓞 E)
    have hinv : ((m : ℚ)⁻¹) • (m • a) = a := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul]
    have ha : a = ((m : ℚ)⁻¹) • (algebraMap (𝓞 E) E s) := by
      rw [← hs, hinv]
    have hsv : (algebraMap (𝓞 E) E s) • v = s • v := algebraMap_smul E s v
    rw [ha, smul_assoc, hsv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Λ.smul_mem s hv))
  have closed : ∀ (a : E) (x : Fin n → E), x ∈ span ℚ (Λ : Set (Fin n → E)) →
      a • x ∈ span ℚ (Λ : Set (Fin n → E)) := by
    intro a x hx
    induction hx using Submodule.span_induction with
    | mem v hv => exact key a v hv
    | zero => simp
    | add x y _ _ hx hy =>
      rw [smul_add]
      exact add_mem hx hy
    | smul q x _ hx =>
      rw [smul_comm]
      exact Submodule.smul_mem _ q hx
  rw [eq_top_iff]
  rintro w -
  have hw : w ∈ span E (Λ : Set (Fin n → E)) := h ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem v hv => exact Submodule.subset_span hv
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact closed a x hx
end GlobalTheory.ShortVectors
