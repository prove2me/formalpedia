-- Prove2me | solution 1 for GlobalTheory.exists_hasProjectiveDimensionLE_of_residueField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:14.742633+00:00
-- url     : https://prove2.me/submissions/03e5458a-6174-4b84-af13-51c213358420

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsHasProjectiveDimensionLEOfResidueField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory IsLocalRing
open GlobalTheory
universe u
namespace GlobalTheory
theorem _root_.solution (R : Type u) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hk : projectiveDimension (ModuleCat.of R (R ⧸ maximalIdeal R)) ≠ ⊤)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  suffices H : ∀ (I : Ideal R) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      I ≤ Module.annihilator R N → ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R N) n from
    H ⊥ M bot_le
  intro I
  induction I using IsNoetherian.induction with
  | hgt I ih =>
  intro N _ _ hN
  induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
  | subsingleton N =>
    intro _
    have := (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)).hasProjectiveDimensionLT_zero
    exact ⟨0, hasProjectiveDimensionLT_of_ge _ 0 _ (Nat.zero_le _)⟩
  | quotient N p f =>
    intro hI
    rw [f.annihilator_eq, Ideal.annihilator_quotient] at hI
    rw [← projectiveDimension_ne_top_iff, projectiveDimension_eq_of_iso f.toModuleIso]
    by_cases hp : p.asIdeal = maximalIdeal R
    · rw [hp]
      exact hk
    have hlt : p.asIdeal < maximalIdeal R := lt_of_le_of_ne (le_maximalIdeal p.2.ne_top) hp
    obtain ⟨x, hx, hxp⟩ := SetLike.exists_of_lt hlt
    have hreg : IsSMulRegular (R ⧸ p.asIdeal) x := by
      intro a b hab
      have hx0 : Ideal.Quotient.mk p.asIdeal x ≠ 0 := by
        rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
      refine mul_left_cancel₀ hx0 ?_
      simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hab
    have hJ : I < p.asIdeal ⊔ Ideal.span {x} := by
      refine lt_of_le_of_lt hI (lt_of_le_of_ne le_sup_left fun e => hxp ?_)
      rw [e]
      exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self x)
    have hq := ih _ hJ (QuotSMulTop x (R ⧸ p.asIdeal)) (sup_le
      (Ideal.annihilator_quotient.ge.trans
        (LinearMap.annihilator_le_of_surjective _ (Submodule.mkQ_surjective _)))
      ((Ideal.span_singleton_le_iff_mem _).mpr (QuotSMulTop.mem_annihilator _ x)))
    rw [← projectiveDimension_ne_top_iff] at hq
    have key := ModuleCat.projectiveDimension_quotSMulTop_eq_succ_of_isSMulRegular
      (ModuleCat.of R (R ⧸ p.asIdeal)) x hreg hx
    intro htop
    apply hq
    rw [htop] at key
    exact key.trans rfl
  | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
    intro hI
    obtain ⟨a, ha⟩ := h₁ (hI.trans (f.annihilator_le_of_injective hf))
    obtain ⟨b, hb⟩ := h₃ (hI.trans (g.annihilator_le_of_surjective hg))
    have hS : (ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero).ShortExact :=
      ModuleCat.shortComplex_shortExact _ hfg hf hg
    exact ⟨a + b, hS.hasProjectiveDimensionLT_X₂ _
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₁) (a + 1) _ (by omega))
      (hasProjectiveDimensionLT_of_ge (ModuleCat.of R N₃) (b + 1) _ (by omega))⟩
end GlobalTheory
