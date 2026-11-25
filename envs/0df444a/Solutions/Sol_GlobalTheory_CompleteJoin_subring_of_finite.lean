-- Prove2me | solution 1 for GlobalTheory.CompleteJoin.subring_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:11:11.015522+00:00
-- url     : https://prove2.me/submissions/35396eb6-e110-44c4-9f94-87436ffd5b28

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
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_C
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_X
import Theorems.Thm_GlobalTheory_CompleteFiniteExtension_isAdicComplete_of_finite_local
import Theorems.Thm_GlobalTheory_IsPolynomialFunction_comp
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_FiniteAlgebraLocalCompletion_isLocalRing_finite_domain
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
open GlobalTheory.CompleteJoin
variable {C : Type} [NormedField C] [IsUltrametricDist C]
namespace GlobalTheory.CompleteJoin
theorem _root_.solution {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (S : Subring C) (φ : R →+* S) (hφ : φ.Finite)
    (h1 : ∀ a, ‖(φ a : C)‖ ≤ 1) (h2 : ∀ a ∈ maximalIdeal R, ‖(φ a : C)‖ < 1) :
    ∃ _ : IsLocalRing S, IsNoetherianRing S ∧ IsAdicComplete (maximalIdeal S) S ∧
      (∀ z : S, ‖(z : C)‖ ≤ 1) ∧ ∀ z : S, z ∈ maximalIdeal S ↔ ‖(z : C)‖ < 1 := by
  letI := φ.toAlgebra
  haveI : Module.Finite R S := hφ
  haveI : IsLocalRing S := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isLocalRing_finite_domain (R := R) S
  have hle : ∀ z : S, ‖(z : C)‖ ≤ 1 := fun z => by
    let v := NormedField.valuation (K := C)
    let ψ : R →+* v.integer := (S.subtype.comp φ).codRestrict _ fun a => h1 a
    have hz : IsIntegral R z := Algebra.IsIntegral.isIntegral z
    have hz' : IsIntegral v.integer (z : C) := hz.map_of_comp_eq ψ S.subtype rfl
    exact (Valuation.integer.integers v).isIntegral_iff_v_le_one.mp hz'
  refine ⟨inferInstance, IsNoetherianRing.of_finite R S,
    CompleteFiniteExtension.isAdicComplete_of_finite_local R S, hle, fun z => ⟨fun hz => ?_,
      fun hz => not_isUnit_of_norm_lt_one S.subtype hle hz⟩⟩
  let P : Ideal S :=
    { carrier := {z | ‖(z : C)‖ < 1}
      add_mem' := fun {a b} ha hb =>
        (IsUltrametricDist.norm_add_le_max (a : C) b).trans_lt (max_lt ha hb)
      zero_mem' := by simp
      smul_mem' := fun c x hx => by
        change ‖(c : C) * x‖ < 1
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (hle c) (norm_nonneg _) hx }
  have hP : ∀ z : S, z ∈ P ↔ ‖(z : C)‖ < 1 := fun _ => Iff.rfl
  have hP1 : P ≠ ⊤ := by
    rw [Ideal.ne_top_iff_one, hP]
    simp
  haveI : P.IsPrime := ⟨hP1, fun {x y} hxy => by
    by_contra h
    rw [not_or, hP, hP, not_lt, not_lt] at h
    rw [hP, Subring.coe_mul, norm_mul] at hxy
    exact hxy.not_ge (one_le_mul_of_one_le_of_one_le h.1 h.2)⟩
  have hc : maximalIdeal R = P.comap (algebraMap R S) :=
    (maximalIdeal.isMaximal R).eq_of_le (Ideal.comap_ne_top _ hP1) fun a ha => h2 a ha
  have hm : P.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := R) P (hc ▸ maximalIdeal.isMaximal R)
  rw [← eq_maximalIdeal hm] at hz
  exact hz
end GlobalTheory.CompleteJoin
