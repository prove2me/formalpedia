-- Prove2me | solution 1 for GlobalTheory.PeriodChart.exists_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:37:41.006989+00:00
-- url     : https://prove2.me/submissions/0b5a5851-f5b4-46fe-9908-c0d0f385ec59

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
import Theorems.Thm_GlobalTheory_PeriodChart_finrank_of_lattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
namespace GlobalTheory.PeriodChart
section Abstract
variable {V : Type} [AddCommGroup V] [Module ℂ V]
end Abstract
section Mat
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
private theorem discrete_range_toIntLinearMap_of_discrete_range (P : M →+ (Fin g → ℂ)) (hd : DiscreteTopology P.range) :
    DiscreteTopology (LinearMap.range P.toIntLinearMap) := by
  have hm : ∀ x : LinearMap.range P.toIntLinearMap, (x : Fin g → ℂ) ∈ P.range := by
    rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := LinearMap.mem_range.mp hx
    exact AddMonoidHom.mem_range.mpr ⟨a, rfl⟩
  exact DiscreteTopology.of_continuous_injective
    (f := fun x => (⟨x, hm x⟩ : P.range)) (continuous_subtype_val.subtype_mk _)
    (fun x y hxy => Subtype.ext (congrArg Subtype.val hxy))
private theorem module_free_int_of_injective_discrete (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) : Module.Free ℤ M := by
  have : DiscreteTopology (LinearMap.range P.toIntLinearMap) := discrete_range_toIntLinearMap_of_discrete_range P hd
  exact Module.Free.of_equiv (LinearEquiv.ofInjective P.toIntLinearMap hi).symm
end Mat
section Period
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}
end Period
end GlobalTheory.PeriodChart
end

set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {g : ℕ}
variable {M : Type} [AddCommGroup M]
namespace GlobalTheory.PeriodChart
theorem _root_.solution [Module.Finite ℤ M] (P P' : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    ∃ T : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ), ∀ a, T (P a) = P' a := by
  classical
  have := module_free_int_of_injective_discrete P hi hd
  let b := Module.Free.chooseBasis ℤ M
  let v : Module.Free.ChooseBasisIndex ℤ M → (Fin g → ℂ) := fun i => P (b i)
  have hsp : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← hs, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    rw [SetLike.mem_coe, ← b.sum_repr a, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_zsmul]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range_self i) : v i ∈ Submodule.span ℝ (Set.range v)) _
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex ℤ M) = finrank ℝ (Fin g → ℂ) := by
    rw [← Module.finrank_eq_card_chooseBasisIndex ℤ M]
    exact finrank_of_lattice P hi hd hs
  let B := Basis.mk (linearIndependent_of_top_le_span_of_card_eq_finrank hsp hcard) hsp
  refine ⟨B.constr ℝ fun i => P' (b i), fun a => ?_⟩
  have key : ((B.constr ℝ fun i => P' (b i)).toAddMonoidHom.comp P).toIntLinearMap =
      P'.toIntLinearMap := by
    refine b.ext fun i => ?_
    have hB : B i = P (b i) := Basis.mk_apply _ _ _
    show (B.constr ℝ fun i => P' (b i)) (P (b i)) = P' (b i)
    rw [← hB, B.constr_basis]
  exact LinearMap.congr_fun key a
end GlobalTheory.PeriodChart
