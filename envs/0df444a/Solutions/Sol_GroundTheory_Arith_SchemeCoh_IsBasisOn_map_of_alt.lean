-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.IsBasisOn.map_of_alt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:06.179886+00:00
-- url     : https://prove2.me/submissions/756f008b-8cc1-4d63-8660-66e399ca4c92

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ModulesTensor
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_tensorToSheaf_tensorLift
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_eq_of_locally
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_sheaf_exists_glue
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_resM
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_smul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_resM_smul_res
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_resM
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_smul
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
namespace IsBasisOn
theorem _root_.solution {P : PMod X} {F : X.Modules} (φ : P ⟶ (preMod X).obj F)
    (hφ : ModulesTensor.W (Opens.grothendieckTopology X) X.sheaf.obj φ)
    {U : X.Opens} {s : P.obj (op U)} (hs : IsBasisOn P U s) :
    IsBasisOn ((preMod X).obj F) U (φ.app _ s) := by
  obtain ⟨hinj, hsurj⟩ := (ModulesTensor.W_toPresheaf_iff φ).1 hφ
  have hres : ∀ (V : X.Opens) (h : V ≤ U), resM ((preMod X).obj F) h (φ.app _ s) =
      φ.app _ (resM P h s) :=
    fun V h => (PresheafOfModules.naturality_apply φ _ s).symm
  have hsm : ∀ (V : X.Opens) (r : ringOn X V) (x : P.obj (op V)),
      φ.app (op V) (r • x) = r • φ.app (op V) x := fun V r x => (φ.app (op V)).hom.map_smul r x
  have hPsm : ∀ (V W : X.Opens) (i : W ≤ V) (h : V ≤ U) (r : ringOn X V),
      resM P i (r • resM P h s) =
        (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE i).op r • resM P (i.trans h) s := by
    intro V W i h r
    rw [resM, PresheafOfModules.map_smul, resM, ← PresheafOfModules.map_comp_apply]
    rfl
  have inj : ∀ (V : X.Opens) (h : V ≤ U) (r : ringOn X V),
      r • resM ((preMod X).obj F) h (φ.app _ s) = 0 → r = 0 := by
    intro V h r hr
    rw [hres, ← hsm] at hr
    have hz := hinj (op V) _ hr
    apply sheaf_eq_of_locally X.sheaf (V := V) r 0
    intro x hx
    obtain ⟨W, f, hf, hxW⟩ := hz x hx
    refine ⟨W, f.le, hxW, ?_⟩
    have hf' : resM P f.le (r • resM P h s) = 0 := hf
    rw [hPsm] at hf'
    have := (hs W (f.le.trans h)).1 (a₁ := (X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map
      (homOfLE f.le).op r) (a₂ := 0) (by simp only [zero_smul]; exact hf')
    change ((X.sheaf.obj ⋙ forget₂ CommRingCat RingCat).map (homOfLE f.le).op) r = _
    rw [this]
    exact (map_zero _).symm
  intro V h
  constructor
  · intro r₁ r₂ e
    have := inj V h (r₁ - r₂) (by rw [sub_smul]; exact sub_eq_zero.mpr e)
    exact sub_eq_zero.mp this
  · intro σ
    have hσ := hsurj (op V) σ
    choose W f hf hxW using hσ
    choose p hp using hf
    have hWU : ∀ x hx, W x hx ≤ U := fun x hx => (f x hx).le.trans h
    choose rr hrr using fun x hx => (hs (W x hx) (hWU x hx)).2 (p x hx)
    have key : ∀ x hx, rr x hx • resM ((preMod X).obj F) (hWU x hx) (φ.app _ s) =
        resM ((preMod X).obj F) (f x hx).le σ := by
      intro x hx
      have e := hrr x hx
      simp only at e
      rw [← app_resM, ← app_smul, e]
      exact hp x hx
    obtain ⟨r, hr⟩ := sheaf_exists_glue X.sheaf (V := V) (ι := V) (fun a => W a.1 a.2)
      (fun a => (f a.1 a.2).le) (fun x hx => ⟨⟨x, hx⟩, hxW x hx⟩) (fun a => rr a.1 a.2) (by
        intro a b
        have hab : W a.1 a.2 ⊓ W b.1 b.2 ≤ U := inf_le_left.trans (hWU _ _)
        have := inj _ hab (resR inf_le_left (rr a.1 a.2) - resR inf_le_right (rr b.1 b.2)) (by
          rw [sub_smul, sub_eq_zero, ← resM_smul_res _ (hWU a.1 a.2) inf_le_left,
            ← resM_smul_res _ (hWU b.1 b.2) inf_le_right, key, key, resM_resM, resM_resM])
        exact sub_eq_zero.mp this)
    refine ⟨r, ?_⟩
    apply sheaf_eq_of_locally ⟨F.presheaf, F.isSheaf⟩ (V := V)
    intro x hx
    refine ⟨W x hx, (f x hx).le, hxW x hx, ?_⟩
    change resM ((preMod X).obj F) (f x hx).le (r • resM ((preMod X).obj F) h (φ.app _ s)) =
      resM ((preMod X).obj F) (f x hx).le σ
    rw [resM_smul, resM_resM, ← key x hx]
    congr 1
    exact hr ⟨x, hx⟩
end IsBasisOn
end GroundTheory.Arith.SchemeCoh
