-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.CechAcyclic.of_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:21.980309+00:00
-- url     : https://prove2.me/submissions/7f97f184-1e52-429b-9520-1a826b839b19

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_comp
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_injective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable {P}
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
namespace CechAcyclic
theorem _root_.solution {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (f : F ⟶ I) (g : I ⟶ Q)
    (hfg : f ≫ g = 0)
    (hinj : ∀ {n : ℕ} (i : Fin n → ι), Function.Injective (f.app (op (inter U i))))
    (hex : ∀ {n : ℕ} (i : Fin n → ι) (y : I.obj (op (inter U i))),
      g.app _ y = 0 → ∃ x, f.app _ x = y)
    (hsurj : ∀ {n : ℕ} (i : Fin n → ι), Function.Surjective (g.app (op (inter U i))))
    (hF : CechAcyclic F U) (hI : CechAcyclic I U) : CechAcyclic Q U := by
  intro n σ hσ

  choose τ hτ using fun i => hsurj i (σ i)
  have hτ' : push U g (n + 1) τ = σ := funext hτ

  have h0 : push U g (n + 2) (d I U (n + 1) τ) = 0 := by rw [push_d, hτ', hσ]
  choose ρ hρ using fun j => hex j _ (congrFun h0 j)
  have hρ' : push U f (n + 2) ρ = d I U (n + 1) τ := funext hρ

  have hρc : d F U (n + 2) ρ = 0 := by
    apply push_injective U f (n + 3) (fun j => hinj j)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨α, hα⟩ := hF (n + 1) ρ hρc

  have hc : d I U (n + 1) (τ - push U f (n + 1) α) = 0 := by
    rw [map_sub, ← push_d, hα, hρ', sub_self]
  obtain ⟨β, hβ⟩ := hI n _ hc
  refine ⟨push U g n β, ?_⟩
  rw [← push_d, hβ, map_sub, hτ', push_comp, hfg, push_zero', sub_zero]
end CechAcyclic
end GroundTheory.Arith.SchemeCoh
