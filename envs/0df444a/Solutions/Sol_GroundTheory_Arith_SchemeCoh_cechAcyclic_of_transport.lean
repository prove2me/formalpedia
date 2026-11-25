-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechAcyclic_of_transport
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:47:10.864222+00:00
-- url     : https://prove2.me/submissions/4b11790f-a270-456b-a431-6a72e1fc728a

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_AffineVanishing
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply


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
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
universe w w' u
variable {Y X : TopCat.{u}} {κ : Type w} {P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
  {P' : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (φ : Opens Y → Opens X) (hφ : Monotone φ)
    (e : ∀ W, P'.obj (op W) ≃+ P.obj (op (φ W)))
    (he : ∀ {V W : Opens Y} (h : V ≤ W) (x : P'.obj (op W)),
      e V (res P' h x) = res P (hφ h) (e W x))
    (U : κ → Opens Y) (hinter : ∀ {n : ℕ} (i : Fin (n + 1) → κ), φ (inter U i) = inter (φ ∘ U) i)
    (hU : CechAcyclic P' U) : CechAcyclic P (φ ∘ U) := by
  let E : ∀ n, Cochain P' U n → Cochain P (φ ∘ U) n := fun n σ i =>
    res P (hinter i).ge (e _ (σ i))
  let E' : ∀ n, Cochain P (φ ∘ U) n → Cochain P' U n := fun n σ i =>
    (e _).symm (res P (hinter i).le (σ i))
  have hEE' : ∀ n σ, E n (E' n σ) = σ := fun n σ => funext fun i => by
    simp only [E, E', AddEquiv.apply_symm_apply, res_res, res_refl]
  have hE'E : ∀ n σ, E' n (E n σ) = σ := fun n σ => funext fun i => by
    simp only [E, E', res_res, res_refl, AddEquiv.symm_apply_apply]
  have hE'0 : ∀ n, E' n 0 = 0 := fun n => funext fun i => by
    simp only [E', Pi.zero_apply, map_zero]
  have hEd : ∀ n σ, E (n + 1) (d P' U n σ) = d P (φ ∘ U) n (E n σ) := fun n σ => funext fun i => by
    simp only [E, d_apply, map_sum, map_zsmul, he, res_res]
  intro n σ hσ
  have hσ' : d P' U (n + 1) (E' (n + 1) σ) = 0 := by
    rw [← hE'E (n + 2) (d P' U (n + 1) _), hEd, hEE', hσ, hE'0]
  obtain ⟨τ, hτ⟩ := hU n _ hσ'
  exact ⟨E n τ, by rw [← hEd, hτ, hEE']⟩
end GroundTheory.Arith.SchemeCoh
