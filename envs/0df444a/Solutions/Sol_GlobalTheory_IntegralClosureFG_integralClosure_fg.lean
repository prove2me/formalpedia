-- Prove2me | solution 1 for GlobalTheory.IntegralClosureFG.integralClosure_fg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:55:27.896553+00:00
-- url     : https://prove2.me/submissions/99bee381-07b7-4c17-a1ae-b87b4fe869b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_DiscrMulMemOfIsIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegralClosureFgFiniteEtaleDvr
import Theorems.Thm_GlobalTheory_DiscConductor_det_smul_eq_sum
import Theorems.Thm_GlobalTheory_DiscConductor_isIntegral_trace_of_isIntegral
import Theorems.Thm_GlobalTheory_discr_ne_zero_iff_of_etale


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntegralClosureFG
namespace GlobalTheory.IntegralClosureFG
theorem _root_.solution (O E A : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field E] [Algebra O E] [IsFractionRing O E] [CommRing A] [Algebra O A] [Algebra E A]
    [IsScalarTower O E A] [Module.Finite E A] [Algebra.Etale E A] :
    (Subalgebra.toSubmodule (integralClosure O A)).FG := by
  classical
  let b0 := Module.finBasis E A
  have hex : ∀ i, ∃ d : O, d ≠ 0 ∧ IsIntegral O (d • b0 i) := by
    intro i
    have h : IsAlgebraic E (b0 i) := Algebra.IsAlgebraic.isAlgebraic _
    have h' : IsAlgebraic O (b0 i) := (IsFractionRing.isAlgebraic_iff O E A).2 h
    obtain ⟨d, hd, hi⟩ := h'.exists_integral_multiple
    exact ⟨d, hd, hi⟩
  choose d hd0 hdi using hex
  have hu : ∀ i, IsUnit (algebraMap O E (d i)) := fun i =>
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ (IsFractionRing.injective O E)).2 (hd0 i))
  let b := b0.isUnitSMul hu
  have hb : ∀ i, IsIntegral O (b i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul]
    exact hdi i
  let D : E := (Algebra.traceMatrix E b).det
  have hD : D ≠ 0 := by
    have h1 := (GlobalTheory.discr_ne_zero_iff_of_etale (K := E) (A := A)
      (by simp) (b : Fin (Module.finrank E A) → A)).2 b.linearIndependent
    rwa [Algebra.discr_def] at h1
  have hint : ∀ e : E, IsIntegral O e → ∃ u : O, algebraMap O E u = e := by
    intro e he
    exact IsIntegrallyClosed.isIntegral_iff.1 he
  let S : Submodule O A := Submodule.span O (Set.range fun j => D⁻¹ • b j)
  have hS : S.FG := Submodule.fg_span (Set.finite_range _)
  have hle : Subalgebra.toSubmodule (integralClosure O A) ≤ S := by
    intro x hx
    have hx' : IsIntegral O x := hx
    obtain ⟨v, hv⟩ := GlobalTheory.DiscConductor.det_smul_eq_sum O E A (Fin (Module.finrank E A)) b x
      (fun i j => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        ((hb i).mul (hb j))))
      (fun i => hint _ (GlobalTheory.DiscConductor.isIntegral_trace_of_isIntegral O E A _
        (hx'.mul (hb i))))
    have hx2 : x = ∑ j, v j • (D⁻¹ • b j) := by
      have : x = D⁻¹ • (D • x) := by rw [smul_smul, inv_mul_cancel₀ hD, one_smul]
      rw [this, hv, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [smul_smul, ← algebraMap_smul E (v j) (D⁻¹ • b j), smul_smul, mul_comm]
    rw [hx2]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  haveI : IsNoetherian O S := isNoetherian_of_fg_of_noetherian S hS
  exact isNoetherian_submodule.1 this _ hle
end GlobalTheory.IntegralClosureFG
