-- Prove2me | solution 1 for GottschalkSurjunctivity.isSurjunctive_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T02:14:51.401377+00:00
-- url     : https://prove2.me/submissions/024542e8-03da-4446-827c-93927f59c774

import Mathlib
import Definitions.Def_GottschalkSurjunctivity_Defs

set_option autoImplicit false

namespace GottschalkSurjunctivity

namespace SubgroupExt8b36

variable {G : Type} [Group G] (H : Subgroup G)

/-- Chosen representative of the left coset `k H`. -/
noncomputable def rep (k : G) : G := (QuotientGroup.mk k : G ⧸ H).out

theorem rep_inv_mul_mem (k : G) : (rep H k)⁻¹ * k ∈ H := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H k
  have e : rep H k = k * h := hh
  rw [e]
  simp

theorem rep_rep_mul (k : G) (h : H) : rep H (rep H k * h) = rep H k := by
  unfold rep
  congr 1
  rw [QuotientGroup.eq]
  have h1 := rep_inv_mul_mem H k
  have h2 : (h : G)⁻¹ ∈ H := H.inv_mem h.2
  have : (rep H k * (h : G))⁻¹ * k = (h : G)⁻¹ * ((rep H k)⁻¹ * k) := by group
  unfold rep at this h1
  rw [this]
  exact H.mul_mem h2 h1

variable {A : Type}

/-- Coset-wise extension of a map on `H → A` to a map on `G → A`. -/
noncomputable def ext (τH : (H → A) → (H → A)) (x : G → A) (k : G) : A :=
  τH (fun h : H => x (rep H k * h)) ⟨(rep H k)⁻¹ * k, rep_inv_mul_mem H k⟩

theorem ext_eq (τH : (H → A) → (H → A)) (x : G → A) (k r : G) (e : rep H k = r)
    (hm : r⁻¹ * k ∈ H) :
    ext H τH x k = τH (fun h : H => x (r * h)) ⟨r⁻¹ * k, hm⟩ := by
  subst e; rfl

theorem ext_rep_mul (τH : (H → A) → (H → A)) (x : G → A) (k : G) (h : H) :
    ext H τH x (rep H k * h) = τH (fun h : H => x (rep H k * h)) h := by
  rw [ext_eq H τH x (rep H k * h) (rep H k) (rep_rep_mul H k h) (by simp)]
  congr 1
  ext
  simp

end SubgroupExt8b36

end GottschalkSurjunctivity

open GottschalkSurjunctivity in
theorem solution (G : Type) [Group G] (hG : IsSurjunctive G)
    (H : Subgroup G) : IsSurjunctive H := by
  intro A _ _ _ _ τH hc heq hinj
  -- the extension
  let τ : (G → A) → (G → A) := SubgroupExt8b36.ext H τH
  have hτc : Continuous τ := by
    refine continuous_pi fun k => ?_
    exact (continuous_apply _).comp (hc.comp (continuous_pi fun h => continuous_apply _))
  have hτe : IsShiftEquivariant G τ := by
    intro g x
    funext k
    show SubgroupExt8b36.ext H τH (shift G g x) k = SubgroupExt8b36.ext H τH x (g⁻¹ * k)
    have hm : (SubgroupExt8b36.rep H (g⁻¹ * k))⁻¹ * g⁻¹ * SubgroupExt8b36.rep H k ∈ H := by
      have h1 := SubgroupExt8b36.rep_inv_mul_mem H (g⁻¹ * k)
      have h2 := H.inv_mem (SubgroupExt8b36.rep_inv_mul_mem H k)
      have : (SubgroupExt8b36.rep H (g⁻¹ * k))⁻¹ * g⁻¹ * SubgroupExt8b36.rep H k
          = ((SubgroupExt8b36.rep H (g⁻¹ * k))⁻¹ * (g⁻¹ * k)) * ((SubgroupExt8b36.rep H k)⁻¹ * k)⁻¹ := by group
      rw [this]
      exact H.mul_mem h1 h2
    let h0 : H := ⟨_, hm⟩
    have hfun : (fun h : H => shift G g x (SubgroupExt8b36.rep H k * h))
        = shift H h0⁻¹ (fun h : H => x (SubgroupExt8b36.rep H (g⁻¹ * k) * h)) := by
      funext h
      simp only [shift_apply, inv_inv, Subgroup.coe_mul, h0]
      congr 1
      group
    unfold SubgroupExt8b36.ext
    rw [hfun, heq, shift_apply]
    congr 1
    ext
    simp only [inv_inv, Subgroup.coe_mul, h0]
    group
  have hτi : Function.Injective τ := by
    intro x y hxy
    funext k
    have hr : (fun h : H => x (SubgroupExt8b36.rep H k * h)) = (fun h : H => y (SubgroupExt8b36.rep H k * h)) := by
      apply hinj
      funext h
      rw [← SubgroupExt8b36.ext_rep_mul H τH x k h, ← SubgroupExt8b36.ext_rep_mul H τH y k h]
      exact congrFun hxy _
    have hk : k = SubgroupExt8b36.rep H k * ((⟨(SubgroupExt8b36.rep H k)⁻¹ * k, SubgroupExt8b36.rep_inv_mul_mem H k⟩ : H) : G) := by
      simp
    rw [hk]
    exact congrFun hr _
  have hs := hG A τ hτc hτe hτi
  intro y
  obtain ⟨x, hx⟩ := hs (fun k => y ⟨(SubgroupExt8b36.rep H k)⁻¹ * k, SubgroupExt8b36.rep_inv_mul_mem H k⟩)
  refine ⟨fun h : H => x (SubgroupExt8b36.rep H 1 * h), ?_⟩
  funext h
  have := congrFun hx (SubgroupExt8b36.rep H 1 * h)
  change SubgroupExt8b36.ext H τH x (SubgroupExt8b36.rep H 1 * h) = _ at this
  rw [SubgroupExt8b36.ext_rep_mul] at this
  rw [this]
  congr 1
  ext
  simp only
  rw [SubgroupExt8b36.rep_rep_mul]
  group
