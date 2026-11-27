-- Prove2me | solution 1 for GlobalTheory.exists_complete_normal_subring_join
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:37:58.877862+00:00
-- url     : https://prove2.me/submissions/2fbb2501-85fc-404e-9105-60f756293601

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_BetaAtSymm
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_OneLtAbsNormReal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FiniteAlgebraLocalCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_NonemptyPadicIntRingHomOfIsAdicComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralClosureFiniteLocalCompleteMixedCharStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsCompleteNormalSubringJoin
import Theorems.Thm_GlobalTheory_CompleteJoin_not_isUnit_of_norm_lt_one
import Theorems.Thm_GlobalTheory_CompleteJoin_padicInt_ringHom_ext
import Theorems.Thm_GlobalTheory_CompleteJoin_subring_of_finite
import Theorems.Thm_GlobalTheory_CompleteJoin_exists_subring_finite
import Theorems.Thm_GlobalTheory_CompleteJoin_exists_normal_subring
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_GlobalTheory_T_integralClosure_finite_local_complete_mixedChar
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_exists_padicInt_algebra_finite
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_nonempty_padicInt_ringHom_of_isAdicComplete
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_map_maximalIdeal_le_maximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
attribute [local simp] GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open CompleteJoin
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R] (T : Formalism.L2.Pj.CDVR) (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [CharZero C] (f : R →+* C) (g : T.V →+* C) (p : ℕ), p.Prime → ‖(p : C)‖ < 1 → T.FinRes → IsNoetherianRing R → IsAdicComplete (maximalIdeal R) R → (∀ a, ‖f a‖ ≤ 1) → (∀ a ∈ maximalIdeal R, ‖f a‖ < 1) → (∀ a, ‖g a‖ ≤ 1) → (∀ a ∈ maximalIdeal T.V, ‖g a‖ < 1) → ∃ (S : Subring C) (_ : IsLocalRing S), IsNoetherianRing S ∧ IsIntegrallyClosed S ∧ IsAdicComplete (maximalIdeal S) S ∧ (∀ a, f a ∈ S) ∧ (∀ a, g a ∈ S) ∧ (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  intro R _ _ _ _ T C _ _ _ _ f g _ _ _ hT hN hR hf1 hf2 hg1 hg2
  haveI : Finite (ResidueField T.V) := hT
  obtain ⟨q, hq, _, hfin⟩ := exists_padicInt_algebra_finite T.V
  have hqV : (q : T.V) ∈ maximalIdeal T.V := by
    have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[q]) T.V _ (maximalIdeal.isMaximal _)
      (Ideal.mem_map_of_mem _ (show (q : ℤ_[q]) ∈ maximalIdeal _ from
        PadicInt.irreducible_p.not_isUnit))
    rwa [map_natCast] at this
  have hqC : ‖(q : C)‖ < 1 := by simpa using hg2 _ hqV
  have hqR : (q : R) ∈ maximalIdeal R := not_isUnit_of_norm_lt_one f hf1 (by simpa using hqC)
  obtain ⟨φ⟩ := nonempty_padicInt_ringHom_of_isAdicComplete (maximalIdeal R) q hqR
  obtain ⟨S₀, ψ₀, hψ₀, h₀, hg₀⟩ := exists_subring_finite f g φ
    (padicInt_ringHom_ext hqC _ _ (fun x => hf1 _) fun x => hg1 _)
  obtain ⟨_, hN₀, hc₀, -, hm₀⟩ := subring_of_finite S₀ ψ₀ hψ₀ (fun a => h₀ a ▸ hf1 a)
    fun a ha => h₀ a ▸ hf2 a ha
  obtain ⟨S, ψ, hψ, h, hS⟩ := exists_normal_subring S₀
    (GlobalTheory.T.integralClosure_finite_local_complete_mixedChar S₀ q hq.out ((hm₀ _).2 (by simpa using hqC)) hN₀ hc₀).1
  have h' : ∀ a, ((ψ.comp ψ₀ a : S) : C) = f a := fun a => (h _).trans (h₀ a)
  obtain ⟨_, hN₁, hc₁, hle, hm₁⟩ := subring_of_finite S (ψ.comp ψ₀) (hψ.comp hψ₀)
    (fun a => h' a ▸ hf1 a) fun a ha => h' a ▸ hf2 a ha
  exact ⟨S, inferInstance, hN₁, hS, hc₁, fun a => h' a ▸ (ψ.comp ψ₀ a).2,
    fun a => (show ((ψ ⟨g a, hg₀ a⟩ : S) : C) = g a from h _) ▸ (ψ ⟨g a, hg₀ a⟩).2, hle, hm₁⟩
end GlobalTheory
