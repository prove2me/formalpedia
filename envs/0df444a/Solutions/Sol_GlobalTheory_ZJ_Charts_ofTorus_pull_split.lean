-- Prove2me | solution 1 for GlobalTheory.ZJ.Charts.ofTorus_pull_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:16:25.470011+00:00
-- url     : https://prove2.me/submissions/db5fe141-b04d-4d27-933a-7bcddf093dcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Theorems.Thm_GlobalTheory_ZJ_stable_top
import Theorems.Thm_GlobalTheory_ZJ_hasWt_one
import Theorems.Thm_GlobalTheory_ZJ_hasWt_charUnit
import Theorems.Thm_GlobalTheory_ZJ_HasWt_mem_range_of_id
import Theorems.Thm_GlobalTheory_ZJ_hasWt_iso_iff
import Theorems.Thm_GlobalTheory_splitTorus_baseChange
import Theorems.Thm_GlobalTheory_splitTorus_properties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.ZJ
attribute [instance] Charts.fin Charts.finC
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
private theorem appLE_univ_univ_apply_eq_appTop {A B : Scheme.{0}} (f : A ⟶ B) (u : Γ(B, ⊤)) (h : ⊤ ≤ f ⁻¹ᵁ ⊤) :
    (f.appLE ⊤ ⊤ h).hom u = f.appTop.hom u := by
  show _ = (f.app ⊤).hom u
  rw [Scheme.Hom.app_eq_appLE]
  rfl
private theorem scheme_appTop_comp_apply {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (u : Γ(C, ⊤)) :
    (f ≫ g).appTop.hom u = f.appTop.hom (g.appTop.hom u) :=
  rfl
private theorem over_left_appTop_comp_apply {A B C : Over S} (f : A ⟶ B) (g : B ⟶ C) (u : Γ(C.left, ⊤)) :
    (f ≫ g).left.appTop.hom u = f.left.appTop.hom (g.left.appTop.hom u) := by
  rw [Over.comp_left, scheme_appTop_comp_apply]
example (X : Scheme.{0}) [IsAffine X] (f : Γ(X, ⊤)) :
    ∃ (C : Charts X) (i i' : {i // C.wt i = C.c₀}), C.W i = X.basicOpen f ∧ C.W i' = X.basicOpen (1 - f) := by
  refine ⟨Charts.ofSections X (fun _ : Bool => ()) () (fun b => if b then f else 1 - f) ?_,
    ⟨true, rfl⟩, ⟨false, rfl⟩, rfl, rfl⟩
  have h := X.basicOpen_add_le f (1 - f)
  rw [add_sub_cancel, X.basicOpen_of_isUnit isUnit_one] at h
  exact top_unique (h.trans (sup_le (le_iSup_of_le ⟨true, rfl⟩ le_rfl) (le_iSup_of_le ⟨false, rfl⟩ le_rfl)))
example (S : Scheme.{0}) [IsAffine S] (a) :
    (Charts.ofTorus S 1).r a (some 0) = (charUnit S (Fin 1 → ℤ) (Pi.single 0 1)).val := rfl
end GlobalTheory.ZJ
end
end

set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZJ
attribute [instance] Charts.fin Charts.finC
variable {S : Scheme.{0}} {H : Over S} [GrpObj H] {X : Type} [AddCommGroup X]
namespace GlobalTheory.ZJ
namespace Charts
theorem _root_.solution (S : Scheme.{0}) [IsAffine S] (d : ℕ) {S' : Scheme.{0}} (t : S' ⟶ S)
    [IsAffineHom (pullback.fst (splitTorus S (Fin d → ℤ)).hom t)] :
    Charts.Split (H := (Over.pullback t).obj (splitTorus S (Fin d → ℤ))) (d := d)
      ((Charts.ofTorus S d).pull (pullback.fst (splitTorus S (Fin d → ℤ)).hom t)) some := by
  obtain ⟨e, he, hχ⟩ := splitTorus_baseChange S S' t (Fin d → ℤ)
  have := he
  have : GeometricallyConnected (splitTorus S (Fin d → ℤ)).hom :=
    ((splitTorus_properties S).1 (Fin d → ℤ)).2.2.2.2.2.2.2.1
  refine ⟨?_, e.hom, ?_⟩
  · change GeometricallyConnected (pullback.snd (splitTorus S (Fin d → ℤ)).hom t)
    infer_instance
  · have hr : ∀ k : Fin d, e.hom.left.appTop.hom
        ((pullback.fst (splitTorus S (Fin d → ℤ)).hom t).appTop.hom (charUnit S (Fin d → ℤ) (Pi.single k 1)).val) =
        (charUnit S' (Fin d → ℤ) (Pi.single k 1)).val := by
      intro k
      rw [← hχ]
      rfl
    exact
      { hom := he
        stable := fun _ => stable_top _
        inv := by
          rintro a j hj
          obtain rfl : j = none := hj
          change HasWt e.hom ⊤ ((pullback.fst (splitTorus S (Fin d → ℤ)).hom t).appTop.hom 1) 0
          rw [map_one]
          exact hasWt_one _ _
        wt := by
          rintro a j k hj
          obtain rfl : j = some k := hj
          change HasWt e.hom ⊤ ((pullback.fst (splitTorus S (Fin d → ℤ)).hom t).appTop.hom
            (charUnit S (Fin d → ℤ) (Pi.single k 1)).val) (Pi.single k 1)
          refine (hasWt_iso_iff e _ _).2 ?_
          rw [hr]
          exact hasWt_charUnit _
        bpf := by
          intro k x
          refine ⟨⟨none, rfl⟩, some k, rfl, ?_⟩
          change x ∈ ((Over.pullback t).obj (splitTorus S (Fin d → ℤ))).left.basicOpen
            ((pullback.fst (splitTorus S (Fin d → ℤ)).hom t).appTop.hom (charUnit S (Fin d → ℤ) (Pi.single k 1)).val)
          rw [Scheme.basicOpen_of_isUnit _ ((Units.isUnit _).map _)]
          trivial
        gen := by
          intro a u hu
          obtain ⟨v, hv⟩ := HasWt.mem_range_of_id ((hasWt_iso_iff e u 0).1 hu)
          have hv' := (appLE_univ_univ_apply_eq_appTop _ _ _).symm.trans hv
          refine Subring.subset_closure (Or.inl ⟨v, (appLE_univ_univ_apply_eq_appTop _ _ _).trans ?_⟩)
          have h1 : u = e.inv.left.appTop.hom (e.hom.left.appTop.hom u) :=
            (congrArg (fun φ : (Over.pullback t).obj (splitTorus S (Fin d → ℤ)) ⟶ (Over.pullback t).obj (splitTorus S (Fin d → ℤ)) =>
              (Scheme.Hom.appTop φ.left).hom u) e.inv_hom_id).symm.trans
              (over_left_appTop_comp_apply e.inv e.hom u)
          rw [h1, ← hv', ← scheme_appTop_comp_apply, Over.w e.inv] }
end Charts
end GlobalTheory.ZJ
