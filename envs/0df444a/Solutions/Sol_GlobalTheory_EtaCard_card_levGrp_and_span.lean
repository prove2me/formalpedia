-- Prove2me | solution 1 for GlobalTheory.EtaCard.card_levGrp_and_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:55:18.594464+00:00
-- url     : https://prove2.me/submissions/bff754a0-bede-4711-8810-fbc89d6a9e28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_IsNullVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_TwoMulPowFourDvdCardGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CardLevGrpAndSpan
import Theorems.Thm_GlobalTheory_EtaCard_nonempty_equiv_mod
import Theorems.Thm_GlobalTheory_EtaCard_nonempty_aut_equiv
import Theorems.Thm_GlobalTheory_EtaCard_span_sup_pow
import Theorems.Thm_GlobalTheory_EtaCard_finite_quot
import Theorems.Thm_GlobalTheory_EtaCard_card_quot
import Theorems.Thm_GlobalTheory_EtaCard_charP_quot
import Theorems.Thm_GlobalTheory_EtaCard_finrank_eq
import Theorems.Thm_GlobalTheory_two_mul_pow_four_dvd_card_generalLinearGroup


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.EtaForm
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaCard
variable (E : Type) [Field E] [NumberField E]
namespace GlobalTheory.EtaCard
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (R : ℕ), 1 < R → Finite (LevGrp Dw (R ^ 4)) ∧ Finite (LatMod Dw R) ∧ Nat.card (LatMod Dw R) = R ^ (2 * FD.fdeg E * (Dw.p + Dw.q)) ∧ Nat.card (LevGrp Dw (R ^ 4)) ≤ R ^ (8 * FD.fdeg E * (Dw.p + Dw.q) ^ 2) ∧ (Odd R → 2 ≤ Dw.p + Dw.q → 2 * R ^ 4 ∣ Nat.card (LevGrp Dw (R ^ 4))) ∧ (∃ x₀ : Fin (Dw.p + Dw.q) → Dw.La, Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤) ∧ ∀ (n : ℕ) (x₀ : Fin n → Dw.La), Submodule.span (𝓞 E) (Set.range x₀) ⊔ (Ideal.span {(R : 𝓞 E)} • ⊤) = ⊤ → ∀ (y : Fin n → LatMod Dw R) (g : LevGrp Dw (R ^ 4)), Submodule.span (𝓞 E) (Set.range fun b => g (shiftFam R x₀ y b)) = ⊤ := by
  intro E _ _ _ H Dw R hR
  have := Dw.fin
  have := Dw.proj
  have hR0 : R ≠ 0 := by omega
  have := finite_quot E R hR0
  have := finite_quot E (R ^ 4) (pow_ne_zero _ hR0)
  obtain ⟨e1⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {(R : 𝓞 E)}) _ Dw.rank
  obtain ⟨e4⟩ := nonempty_equiv_mod (𝓞 E) Dw.La (Ideal.span {((R ^ 4 : ℕ) : 𝓞 E)}) _ Dw.rank
  obtain ⟨g4⟩ := nonempty_aut_equiv _ _ _ _ e4
  refine ⟨Finite.of_equiv _ g4.symm, Finite.of_equiv _ e1.symm.toEquiv, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_congr e1.toEquiv, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul]
  · rw [Nat.card_congr g4]
    refine (Nat.card_le_card_of_injective _ Units.val_injective).trans (le_of_eq ?_)
    change Nat.card (Fin (Dw.p + Dw.q) → Fin (Dw.p + Dw.q) → _) = _
    rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, card_quot, finrank_eq, ← pow_mul, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · intro ho h2
    rw [Nat.card_congr g4]
    exact two_mul_pow_four_dvd_card_generalLinearGroup _ R ho (charP_quot E _) hR _ h2
  · choose x₀ hx using fun i => Submodule.Quotient.mk_surjective _ (e1.symm (Pi.single i 1))
    refine ⟨x₀, ?_⟩
    rw [sup_comm, ← Submodule.map_mkQ_eq_top, eq_top_iff]
    intro z _
    choose c hc using fun i => Ideal.Quotient.mk_surjective (e1 z i)
    refine ⟨∑ i, c i • x₀ i, Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩), e1.injective ?_⟩
    simp only [map_sum, map_smul, Submodule.mkQ_apply, hx, LinearEquiv.apply_symm_apply]
    ext j
    rw [Finset.sum_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi.symm]) (by simp), ← hc]
    simp [Algebra.smul_def]
  · intro n x₀ hx y g
    have h1 : Submodule.span (𝓞 E) (Set.range fun b => x₀ b + R • qRep (y b)) ⊔
        Ideal.span {(R : 𝓞 E)} • ⊤ = ⊤ := by
      refine eq_top_iff.2 (hx.ge.trans (sup_le (Submodule.span_le.2 ?_) le_sup_right))
      rintro _ ⟨b, rfl⟩
      have : x₀ b = (x₀ b + R • qRep (y b)) - (R : 𝓞 E) • qRep (y b) := by
        rw [Nat.cast_smul_eq_nsmul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨b, rfl⟩))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial))
    have h2 := span_sup_pow _ _ _ _ h1 4
    rw [← Nat.cast_pow, sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp] at h2
    have h3 := congrArg (Submodule.map g.toLinearMap) h2
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, LinearEquiv.range] at h3
    exact h3
end GlobalTheory.EtaCard
