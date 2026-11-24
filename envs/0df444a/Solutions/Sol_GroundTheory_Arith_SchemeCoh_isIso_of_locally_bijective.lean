-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isIso_of_locally_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:14.508913+00:00
-- url     : https://prove2.me/submissions/4edf7de3-712f-427b-bc03-ba9c8573c10c

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorToSheaf_tensorLift
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_eq_of_locally
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_exists_glue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [reassoc] GroundTheory.Arith.SchemeCoh.tensorToSheaf_tensorLift

set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory Opposite TensorProduct AlgebraicGeometry TopologicalSpace
universe u
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
variable {X : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {M N : X.Modules} (f : M ⟶ N)
    (hf : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∀ V ≤ U, Function.Bijective (f.app V)) : IsIso f := by
  choose U hxU hU using hf
  have nat : ∀ {V W : X.Opens} (i : W ≤ V) (σ : Γ(M, V)),
      f.app W (M.presheaf.map (homOfLE i).op σ) = N.presheaf.map (homOfLE i).op (f.app V σ) :=
    fun i σ => NatTrans.naturality_apply f.mapPresheaf (homOfLE i).op σ
  have inj : ∀ V : X.Opens, Function.Injective (f.app V) := by
    intro V σ τ hστ
    apply sheaf_eq_of_locally ⟨M.presheaf, M.isSheaf⟩ (V := V)
    intro x hx
    refine ⟨V ⊓ U x, inf_le_left, ⟨hx, hxU x⟩, ?_⟩
    apply (hU x (V ⊓ U x) inf_le_right).1
    change f.app _ (M.presheaf.map _ σ) = f.app _ (M.presheaf.map _ τ)
    rw [nat, nat, hστ]
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨inj V, fun τ => ?_⟩
  have loc : ∀ x : {x : X // x ∈ V}, ∃ σ : Γ(M, V ⊓ U x.1),
      f.app _ σ = N.presheaf.map (homOfLE (inf_le_left : V ⊓ U x.1 ≤ V)).op τ :=
    fun x => (hU x.1 _ inf_le_right).2 _
  choose σ hσ using loc
  obtain ⟨g, hg⟩ := sheaf_exists_glue ⟨M.presheaf, M.isSheaf⟩ (V := V) (ι := {x : X // x ∈ V})
    (fun a => V ⊓ U a.1) (fun _ => inf_le_left) (fun x hx => ⟨⟨x, hx⟩, hx, hxU x⟩) σ (by
      intro a b
      apply inj
      change f.app _ (M.presheaf.map _ (σ a)) = f.app _ (M.presheaf.map _ (σ b))
      rw [nat, nat, hσ, hσ]
      change ((N.presheaf.map _ ≫ N.presheaf.map _) τ) = ((N.presheaf.map _ ≫ N.presheaf.map _) τ)
      rw [← N.presheaf.map_comp, ← N.presheaf.map_comp]
      rfl)
  refine ⟨g, ?_⟩
  apply sheaf_eq_of_locally ⟨N.presheaf, N.isSheaf⟩ (V := V)
  intro x hx
  refine ⟨V ⊓ U x, inf_le_left, ⟨hx, hxU x⟩, ?_⟩
  change N.presheaf.map _ (f.app V g) = _
  rw [← nat]
  have := hg ⟨x, hx⟩
  simp only at this
  rw [this]
  exact hσ ⟨x, hx⟩
end GroundTheory.Arith.SchemeCoh
