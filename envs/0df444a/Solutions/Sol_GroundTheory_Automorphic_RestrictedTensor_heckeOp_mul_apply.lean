-- Prove2me | solution 1 for GroundTheory.Automorphic.RestrictedTensor.heckeOp_mul_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:59:26.883132+00:00
-- url     : https://prove2.me/submissions/bb886072-00ed-4a75-8958-12ca15f235d8

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_SmoothRep
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Operators
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_MatrixCoeff
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_Window
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_sub_fixedProj_mem_span
import Theorems.Thm_GroundTheory_Automorphic_RestrictedTensor_heckeOp_apply
import Theorems.Thm_GroundTheory_Automorphic_fixedProj_apply_act


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.RestrictedTensor
open Module Set
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}
variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))
namespace GroundTheory.Automorphic.RestrictedTensor
theorem _root_.solution {a b : G}
    (hab : ∀ h ∈ K, ∃ k ∈ K, k * a = a * k ∧ (k⁻¹ * h) * b = b * (k⁻¹ * h))
    (m : fixedVectors ρ K) :
    heckeOp hρ hKc hKo a (heckeOp hρ hKc hKo b m) = heckeOp hρ hKc hKo (a * b) m := by
  obtain ⟨u, hu⟩ : ∃ u, u = ρ b m := ⟨_, rfl⟩
  have hspan := sub_fixedProj_mem_span hρ hKc hKo u

  have hkill : ∀ y ∈ Submodule.span ℂ (range fun k : K => ρ k u - u),
      fixedProj ρ hρ hKc hKo (ρ a y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨h, hh⟩, rfl⟩ := hy
      obtain ⟨k, hk, hka, hkb⟩ := hab h hh
      have hk' : k⁻¹ * h ∈ K := K.mul_mem (K.inv_mem hk) hh
      have h1 : ρ h u = ρ k u := by
        have : ρ (k⁻¹ * h) u = u := by
          rw [hu, ← Module.End.mul_apply, ← map_mul, hkb, map_mul, Module.End.mul_apply,
            m.2 _ hk']
        calc ρ h u = ρ k (ρ (k⁻¹ * h) u) := by
                rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
          _ = ρ k u := by rw [this]
      simp only
      rw [h1, map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, ← hka, map_mul,
        Module.End.mul_apply, fixedProj_apply_act hρ hKc hKo hk, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, map_smul, hx, smul_zero]
  have := hkill _ hspan
  rw [map_sub, map_sub, sub_eq_zero] at this
  subst hu
  rw [heckeOp_apply, heckeOp_apply, heckeOp_apply, ← this, map_mul, Module.End.mul_apply]
end GroundTheory.Automorphic.RestrictedTensor
