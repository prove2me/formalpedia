-- Prove2me | solution 2 for LCAGroup.leftRegularRep_isotypicProjector
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:09:19.886342+00:00
-- url     : https://prove2.me/submissions/726e3e42-8348-4299-ac23-79daf608f504

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace
import Definitions.Def_LCAGroup_LeftRegularRep
import Theorems.Thm_LCAGroup_isotypicSubspace_averaging_projection

open MeasureTheory

set_option autoImplicit false

namespace Sol_LCAGroup_leftRegularRep_isotypicProjector

open LCAGroup

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
    (ν : Measure G) [ν.IsMulLeftInvariant]

theorem lrr_one : leftRegularRep ν 2 (1 : G) = 1 := by
  ext1 f
  rw [ContinuousLinearMap.one_apply, Lp.ext_iff]
  refine (Lp.coeFn_compMeasurePreserving _ _).trans ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simp

theorem lrr_mul (a b : G) :
    leftRegularRep ν 2 (a * b) = leftRegularRep ν 2 a * leftRegularRep ν 2 b := by
  ext1 f
  rw [ContinuousLinearMap.mul_apply, Lp.ext_iff]
  have h1 : (leftRegularRep ν 2 (a * b) f : G → ℂ) =ᵐ[ν] (f : G → ℂ) ∘ (fun x => (a * b)⁻¹ * x) :=
    Lp.coeFn_compMeasurePreserving _ _
  have h2 : (leftRegularRep ν 2 a (leftRegularRep ν 2 b f) : G → ℂ) =ᵐ[ν]
      (leftRegularRep ν 2 b f : G → ℂ) ∘ (fun x => a⁻¹ * x) :=
    Lp.coeFn_compMeasurePreserving _ _
  have h3 : (leftRegularRep ν 2 b f : G → ℂ) ∘ (fun x => a⁻¹ * x) =ᵐ[ν]
      ((f : G → ℂ) ∘ (fun x => b⁻¹ * x)) ∘ (fun x => a⁻¹ * x) :=
    (measurePreserving_mul_left ν a⁻¹).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving _ _)
  refine h1.trans (Filter.EventuallyEq.trans ?_ (h2.trans h3).symm)
  refine Filter.Eventually.of_forall fun x => ?_
  simp [mul_inv_rev, mul_assoc]

theorem lrr_norm (g : G) (f : Lp ℂ 2 ν) : ‖leftRegularRep ν 2 g f‖ = ‖f‖ :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun x => g⁻¹ * x) (measurePreserving_mul_left ν g⁻¹)).norm_map f

end Sol_LCAGroup_leftRegularRep_isotypicProjector

open Sol_LCAGroup_leftRegularRep_isotypicProjector

open LCAGroup in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [ν.Regular]
    (K : Subgroup G) [CompactSpace K] (μK : Measure K) [μK.IsHaarMeasure]
    (ω : PontryaginDual K) (f : Lp ℂ 2 ν) :
    let P : PontryaginDual K → Lp ℂ 2 ν → Lp ℂ 2 ν := fun χ h =>
      (μK.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (χ k : ℂ)) • leftRegularRep ν 2 (k : G) h ∂μK
    P ω f ∈ isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) (fun k => (ω k : ℂ)) ∧
      f - P ω f ∈
        (isotypicSubspace (fun k : K => leftRegularRep ν 2 (k : G)) fun k => (ω k : ℂ))ᗮ ∧
      (∀ g : G, P ω (leftRegularRep ν 2 g f) = leftRegularRep ν 2 g (P ω f)) ∧
      (∀ ψ : PontryaginDual K, ψ ≠ ω → P ψ (P ω f) = 0) := by
  intro P
  let π : K →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :=
    { toFun := fun k => leftRegularRep ν 2 (k : G)
      map_one' := lrr_one ν
      map_mul' := fun a b => lrr_mul ν (a : G) b }
  have hU : ∀ k, π k ∈ unitary (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) := fun k =>
    IsUnit.mem_unitary_of_star_mul_self ((Group.isUnit k).map π)
      ((π k).norm_map_iff_adjoint_comp_self.mp (lrr_norm ν (k : G)))
  have hC : ∀ v : Lp ℂ 2 ν, Continuous fun k => π k v := by
    intro v
    let F : C(K × G, G) := ⟨fun p => ((p.1 : G))⁻¹ * p.2, by fun_prop⟩
    exact Continuous.compMeasurePreservingLp (μ := ν) (ν := ν) (f := fun _ : K => v)
      (g := fun k => F.curry k) continuous_const F.curry.continuous
      (fun k => measurePreserving_mul_left ν (k : G)⁻¹) (by norm_num)
  have hA := fun χ : PontryaginDual K =>
    isotypicSubspace_averaging_projection K μK (Lp ℂ 2 ν) π hU hC χ
  have hint : ∀ (χ : PontryaginDual K) (h : Lp ℂ 2 ν),
      Integrable (fun k : K => (starRingEnd ℂ (χ k : ℂ)) • leftRegularRep ν 2 (k : G) h) μK := by
    intro χ h
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    have h1 : Continuous fun k : K => (starRingEnd ℂ (χ k : ℂ)) := by fun_prop
    exact h1.smul (hC h)
  refine ⟨(hA ω).1 f, (hA ω).2.1 f, ?_, ?_⟩
  · intro g
    show (μK.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (ω k : ℂ)) •
        leftRegularRep ν 2 (k : G) (leftRegularRep ν 2 g f) ∂μK =
      leftRegularRep ν 2 g ((μK.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (ω k : ℂ)) •
        leftRegularRep ν 2 (k : G) f ∂μK)
    rw [ContinuousLinearMap.map_smul_of_tower, ← ContinuousLinearMap.integral_comp_comm _ (hint ω f)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show (starRingEnd ℂ (ω k : ℂ)) • leftRegularRep ν 2 (k : G) (leftRegularRep ν 2 g f) =
      leftRegularRep ν 2 g ((starRingEnd ℂ (ω k : ℂ)) • leftRegularRep ν 2 (k : G) f)
    rw [map_smul, ← ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.mul_apply, ← lrr_mul,
      ← lrr_mul, mul_comm]
  · intro ψ hψ
    have hv : ∀ k : K, leftRegularRep ν 2 (k : G) (P ω f) = (ω k : ℂ) • P ω f := (hA ω).1 f
    have h1 : ∀ k : K, leftRegularRep ν 2 (k : G) (P ψ (P ω f)) = (ψ k : ℂ) • P ψ (P ω f) :=
      (hA ψ).1 (P ω f)
    have hsc : P ψ (P ω f) = (μK.real Set.univ)⁻¹ •
        ((∫ k, (starRingEnd ℂ (ψ k : ℂ)) * (ω k : ℂ) ∂μK) • P ω f) := by
      show (μK.real Set.univ)⁻¹ • ∫ k, (starRingEnd ℂ (ψ k : ℂ)) •
        leftRegularRep ν 2 (k : G) (P ω f) ∂μK = _
      congr 1
      rw [← integral_smul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
      show (starRingEnd ℂ (ψ k : ℂ)) • leftRegularRep ν 2 (k : G) (P ω f) =
        ((starRingEnd ℂ (ψ k : ℂ)) * (ω k : ℂ)) • P ω f
      rw [hv k, smul_smul]
    clear_value P
    have h2 : ∀ k : K, leftRegularRep ν 2 (k : G) (P ψ (P ω f)) = (ω k : ℂ) • P ψ (P ω f) := by
      intro k
      rw [hsc, ContinuousLinearMap.map_smul_of_tower, map_smul, hv k]
      rw [smul_comm (∫ k, (starRingEnd ℂ (ψ k : ℂ)) * (ω k : ℂ) ∂μK) (ω k : ℂ) (P ω f)]
      exact (smul_comm (ω k : ℂ) (μK.real Set.univ)⁻¹ _).symm
    obtain ⟨k, hk⟩ : ∃ k, ψ k ≠ ω k := by
      by_contra hcon
      exact hψ (ContinuousMonoidHom.ext fun k => not_not.mp fun h => hcon ⟨k, h⟩)
    have hz : ((ψ k : ℂ) - (ω k : ℂ)) • P ψ (P ω f) = 0 := by
      rw [sub_smul, ← h1 k, ← h2 k, sub_self]
    rcases smul_eq_zero.mp hz with h | h
    · exact absurd (Circle.ext (sub_eq_zero.mp h)) hk
    · exact h
