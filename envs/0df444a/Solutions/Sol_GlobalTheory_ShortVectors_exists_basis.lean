-- Prove2me | solution 1 for GlobalTheory.ShortVectors.exists_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:01:37.44533+00:00
-- url     : https://prove2.me/submissions/5e0e5f14-f230-4bc2-84fb-22717ae69334

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_Transference
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_EmbeddingHermSelf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsLocalizedModuleSubtype
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_TraceHermNondegenerate
import Theorems.Thm_GlobalTheory_ShortVectors_span_rat_eq_top
import Theorems.Thm_GlobalTheory_ShortVectors_finrank_eq

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
namespace GlobalTheory.ShortVectors
theorem _root_.solution {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (h : span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ b : Basis (Fin (2 * fdeg E * n)) ℚ (Fin n → E),
      ∀ x, x ∈ span ℤ (Set.range b) ↔ x ∈ Λ := by
  classical
  have hq := span_rat_eq_top Λ h
  have : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.mpr hfg
  have : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 E) Λ
  let bz := Module.finBasis ℤ Λ
  let u : Fin (finrank ℤ Λ) → Fin n → E := fun i => (bz i : Fin n → E)
  have hspanZ : (Submodule.span ℤ (Set.range u) : Set (Fin n → E)) = Λ := by
    have h1 : Submodule.span ℤ (Set.range u) =
        (⊤ : Submodule ℤ Λ).map (Λ.subtype.restrictScalars ℤ) := by
      rw [← bz.span_eq, Submodule.map_span, ← Set.range_comp]
      rfl
    rw [h1, Submodule.map_top]
    ext x
    simp
  have hliZ : LinearIndependent ℤ u :=
    bz.linearIndependent.map' (Λ.subtype.restrictScalars ℤ)
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hliQ : LinearIndependent ℚ u := (LinearIndependent.iff_fractionRing ℤ ℚ).mp hliZ
  have hspQ : ⊤ ≤ Submodule.span ℚ (Set.range u) := by
    rw [← hq, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (Set.range u) := by
      rw [← SetLike.mem_coe, hspanZ]
      exact hx
    exact Submodule.span_le_restrictScalars ℤ ℚ _ hx'
  let bq : Basis (Fin (finrank ℤ Λ)) ℚ (Fin n → E) := Basis.mk hliQ hspQ
  have hcard : finrank ℤ Λ = 2 * fdeg E * n := by
    have h1 := Module.finrank_eq_card_basis bq
    rw [Fintype.card_fin] at h1
    rw [← h1, Module.finrank_pi_fintype]
    simp [finrank_eq]
    ring
  refine ⟨bq.reindex (finCongr hcard), fun x => ?_⟩
  rw [Basis.range_reindex, Basis.coe_mk, ← SetLike.mem_coe, hspanZ, SetLike.mem_coe]
end GlobalTheory.ShortVectors
