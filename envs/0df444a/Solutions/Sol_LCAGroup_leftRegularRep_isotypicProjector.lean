-- Prove2me | solution 1 for LCAGroup.leftRegularRep_isotypicProjector
-- status  : ACCEPTED   (prove)
-- author  : @RSoulat
-- created : 2026-11-22T19:08:55.372029+00:00
-- url     : https://prove2.me/submissions/9e0076a5-4fc5-45ff-ba94-780861840b21

import Mathlib
import Definitions.Def_LCAGroup_IsotypicSubspace
import Definitions.Def_LCAGroup_LeftRegularRep
import Theorems.Thm_LCAGroup_isotypicSubspace_averaging_projection

open MeasureTheory LCAGroup
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1600000

section

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsHaarMeasure] [ν.Regular]

private theorem leftRegularRep_one (v : Lp ℂ 2 ν) : leftRegularRep ν 2 1 v = v := by
  simp only [leftRegularRep_apply, inv_one, one_mul]
  exact Lp.compMeasurePreserving_id_apply v

private theorem leftRegularRep_mul (g h : G) (v : Lp ℂ 2 ν) :
    leftRegularRep ν 2 (g * h) v = leftRegularRep ν 2 g (leftRegularRep ν 2 h v) := by
  simp only [leftRegularRep_apply]
  rw [← Lp.compMeasurePreserving_comp_apply]
  congr 1
  ext x
  simp [Function.comp_def, mul_inv_rev, mul_assoc]

private theorem leftRegularRep_unitary (g : G) :
    leftRegularRep ν 2 g ∈ unitary (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) := by
  let e : Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ν :=
    Lp.compMeasurePreservingₗᵢ ℂ (fun x => g⁻¹ * x) (measurePreserving_mul_left ν g⁻¹)
  have he : Function.Surjective e := by
    intro v
    refine ⟨leftRegularRep ν 2 g⁻¹ v, ?_⟩
    change leftRegularRep ν 2 g (leftRegularRep ν 2 g⁻¹ v) = v
    rw [← leftRegularRep_mul, mul_inv_cancel, leftRegularRep_one]
  let E := LinearIsometryEquiv.ofSurjective e he
  exact (Unitary.linearIsometryEquiv.symm E).property

private theorem continuous_leftRegularRep (v : Lp ℂ 2 ν) :
    Continuous (fun g : G => leftRegularRep ν 2 g v) := by
  let F (g : G) : C(G, G) := ⟨fun x => g⁻¹ * x, continuous_const.mul continuous_id⟩
  have hF : Continuous F := ContinuousMap.continuous_of_continuous_uncurry F (by
    change Continuous (fun p : G × G => p.1⁻¹ * p.2)
    fun_prop)
  exact (continuous_const (y := v)).compMeasurePreservingLp hF
    (fun g => measurePreserving_mul_left ν g⁻¹) (by norm_num)

end

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
      map_one' := ContinuousLinearMap.ext (leftRegularRep_one ν)
      map_mul' := fun g h => ContinuousLinearMap.ext (leftRegularRep_mul ν (g : G) (h : G)) }
  have hπ : ∀ k : K, π k ∈ unitary (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) :=
    fun k => leftRegularRep_unitary ν (k : G)
  have hCont (v : Lp ℂ 2 ν) : Continuous fun k : K => π k v :=
    (continuous_leftRegularRep ν v).comp continuous_subtype_val
  let I (χ : PontryaginDual K) := isotypicSubspace π fun k => (χ k : ℂ)
  have hProj (χ : PontryaginDual K) (v : Lp ℂ 2 ν) :
      P χ v ∈ I χ ∧ v - P χ v ∈ (I χ)ᗮ := by
    obtain ⟨hMem, hPerp, _⟩ := isotypicSubspace_averaging_projection K μK (Lp ℂ 2 ν)
      π hπ hCont χ
    exact ⟨hMem v, hPerp v⟩
  refine ⟨(hProj ω f).1, (hProj ω f).2, ?_, ?_⟩
  · intro g
    have hIntegrable : Integrable
        (fun k : K => (starRingEnd ℂ (ω k : ℂ)) • leftRegularRep ν 2 (k : G) f) μK := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact (continuous_star.comp (continuous_subtype_val.comp ω.continuous)).smul (hCont f)
      · exact HasCompactSupport.of_compactSpace _
    dsimp only [P]
    rw [ContinuousLinearMap.map_smul_of_tower, ← (leftRegularRep ν 2 g).integral_comp_comm hIntegrable]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun k => by
      change (starRingEnd ℂ (ω k : ℂ)) • leftRegularRep ν 2 (k : G) (leftRegularRep ν 2 g f) =
        leftRegularRep ν 2 g ((starRingEnd ℂ (ω k : ℂ)) • leftRegularRep ν 2 (k : G) f)
      rw [map_smul, ← leftRegularRep_mul, ← leftRegularRep_mul, mul_comm (k : G) g]
  · intro ψ hψ
    have hdiff : ∃ k : K, (ψ k : ℂ) ≠ (ω k : ℂ) := by
      by_contra! h
      exact hψ (DFunLike.ext _ _ fun k => Subtype.ext (h k))
    obtain ⟨k, hk⟩ := hdiff
    have hFactor : (starRingEnd ℂ (ψ k : ℂ)) * (ω k : ℂ) ≠ 1 := by
      rw [show starRingEnd ℂ (ψ k : ℂ) = ((ψ k)⁻¹ : Circle) from
        (Circle.coe_inv_eq_conj (ψ k)).symm, Circle.coe_inv]
      intro h
      have h₀ : (ψ k : ℂ) ≠ 0 := Circle.coe_ne_zero _
      apply hk
      calc
        (ψ k : ℂ) = (ψ k : ℂ) * 1 := (mul_one _).symm
        _ = (ψ k : ℂ) * ((ψ k : ℂ)⁻¹ * (ω k : ℂ)) := by rw [h]
        _ = (ω k : ℂ) := by rw [← mul_assoc, mul_inv_cancel₀ h₀, one_mul]
    let w := P ω f
    have hw : w ∈ I ω := (hProj ω f).1
    have hwPerp : w ∈ (I ψ)ᗮ := (Submodule.mem_orthogonal _ _).mpr fun v hv => by
      have hh := Unitary.inner_map_map (⟨π k, hπ k⟩ : unitary (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)) v w
      change ⟪π k v, π k w⟫_ℂ = ⟪v, w⟫_ℂ at hh
      have hvk : π k v = (ψ k : ℂ) • v := hv k
      have hwk : π k w = (ω k : ℂ) • w := hw k
      rw [hvk, hwk, inner_smul_left, inner_smul_right, ← mul_assoc] at hh
      exact (mul_eq_zero.mp (show ((starRingEnd ℂ (ψ k : ℂ)) * (ω k : ℂ) - 1) *
          ⟪v, w⟫_ℂ = 0 by rw [sub_mul, one_mul, hh, sub_self])).resolve_left
        (sub_ne_zero.mpr hFactor)
    have hvPerp : P ψ w ∈ (I ψ)ᗮ := by
      simpa only [sub_sub_cancel] using Submodule.sub_mem _ hwPerp (hProj ψ w).2
    exact inner_self_eq_zero.mp
      (Submodule.inner_right_of_mem_orthogonal (hProj ψ w).1 hvPerp)
