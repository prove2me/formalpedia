-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.surjective_of_goodAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:53:36.500806+00:00
-- url     : https://prove2.me/submissions/31992c30-281d-445c-81bb-64995cc04149

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_comp_apply_eq_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_exact_of_shortExact
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_injective_of_shortExact
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_res
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_constCochain
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_glue
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_le
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_le_inter_const
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_d
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
noncomputable section
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w w' u
variable {X : TopCat.{u}}
variable (B : Opens X → Prop) (Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop)
variable {B Good} (hC : IsCoverSystem B Good)
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
include hC hS
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (hF : GoodAcyclic B Good S.X₁) (V : Opens X) (hV : B V) :
    Function.Surjective (S.g.hom.app (op V)) := by
  intro s
  have hls := (TopCat.Sheaf.isLocallySurjective_iff_epi S.g).mpr hS.epi_g
  have hloc := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hls
  choose O hOV ht hxO using fun x : V => hloc V s x.1 x.2
  choose t ht using ht
  obtain ⟨κ, _, U, hgood, hUO⟩ := hC.exists_refinement V hV O hxO
  choose x hx using hUO
  have hUV : ∀ a, U a ≤ V := fun a => (hx a).trans (hOV (x a))
  have hsup : iSup U = V := hC.iSup_eq V U hgood
  let τ0 : Cochain S.X₂.obj U 0 := fun i =>
    res S.X₂.obj ((inter_le U i 0).trans (hx (i 0))) (t (x (i 0)))
  have hτ0 : push U S.g.hom 0 τ0 = constCochain S.X₃.obj U hUV s := by
    funext i
    simp only [push, τ0, constCochain, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [app_res, ht]
    exact res_res _ _ _ s
  have hdτ0 : push U S.g.hom 1 (d _ U 0 τ0) = 0 := by
    rw [push_d, hτ0, d_constCochain]
  choose ρ hρ using fun j => app_exact_of_shortExact hS _ _ (congrFun hdτ0 j)
  have hρ' : push U S.f.hom 1 ρ = d _ U 0 τ0 := funext hρ
  have hρc : d S.X₁.obj U 1 ρ = 0 := by
    apply push_injective U S.f.hom 2 (fun j => app_injective_of_shortExact hS _)
    rw [map_zero, push_d, hρ', d_d]
  obtain ⟨β, hβ⟩ := hF V hV κ U hgood 0 ρ hρc
  have hc : d S.X₂.obj U 0 (τ0 - push U S.f.hom 0 β) = 0 := by
    rw [map_sub, ← push_d, hβ, hρ', sub_self]
  obtain ⟨t', ht'⟩ := exists_glue S.X₂.obj S.X₂.property U V hUV hsup.ge _ hc
  refine ⟨t', ?_⟩
  apply TopCat.Sheaf.eq_of_locally_eq' S.X₃ U V (fun a => homOfLE (hUV a)) hsup.ge
  intro a
  have key : res S.X₃.obj ((inter_le U (fun _ : Fin 1 => a) 0).trans (hUV a))
      (S.g.hom.app _ t') =
      res S.X₃.obj ((inter_le U (fun _ : Fin 1 => a) 0).trans (hUV a)) s := by
    rw [← app_res, ht' (fun _ => a), Pi.sub_apply, map_sub]
    have h1 : S.g.hom.app _ ((push U S.f.hom 0 β) (fun _ => a)) = 0 :=
      app_comp_apply_eq_zero _ _
    rw [h1, sub_zero]
    exact congrFun hτ0 (fun _ => a)
  have := congrArg (res S.X₃.obj (le_inter_const U a)) key
  rw [res_res, res_res] at this
  exact this
end GroundTheory.Arith.SchemeCoh
