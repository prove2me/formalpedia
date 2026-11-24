-- Prove2me | solution 1 for GlobalTheory.RigidTriv.exists_gen_of_rigid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:34:12.935433+00:00
-- url     : https://prove2.me/submissions/6d994c91-b574-4bdf-8c3d-309e0c878bb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Theorems.Thm_GlobalTheory_RigidTriv_exists_locGen
import Theorems.Thm_GlobalTheory_RigidTriv_exists_normalised
import Theorems.Thm_GlobalTheory_RigidTriv_agree_of_rigid
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
namespace GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}
private lemma gm_id_val_eq_germ (W : Z.Opens) (z : Z) (hz : z ∈ W) (u : Γ(Z, W)ˣ) :
    Units.val (gm (𝟙 Z) z W u) = (Z.presheaf.germ W z hz).hom u.1 := by
  simp [gm, hz, pullU]
  rfl
private lemma gm_res_lemma_4 {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Y) y V (Units.map (Y.presheaf.map (homOfLE hVU).op).hom.toMonoidHom a) = gm (𝟙 Y) y U a := by
  ext1
  rw [gm_id_val_eq_germ V y hy, gm_id_val_eq_germ U y (hVU hy)]
  exact TopCat.Presheaf.germ_res_apply ..
private lemma units_eq_of_gm_id_eq_on_open {O : X.Opens} {a b : Γ(X, O)ˣ}
    (h : ∀ x, x ∈ O → gm (𝟙 X) x O a = gm (𝟙 X) x O b) : a = b := by
  ext1
  refine TopCat.Presheaf.section_ext X.sheaf O _ _ fun x hx => ?_
  have hv := congrArg Units.val (h x hx)
  rw [gm_id_val_eq_germ O x hx, gm_id_val_eq_germ O x hx] at hv
  exact hv
private lemma exists_unit_on_open_of_gm_agree_on_cover (V : X.Opens) {κ : Type} (O : κ → X.Opens) (hO : ∀ a, O a ≤ V)
    (hcov : ∀ x ∈ V, ∃ a, x ∈ O a) (u : ∀ a, Γ(X, O a)ˣ)
    (hu : ∀ a b x (_ : x ∈ O a) (_ : x ∈ O b), gm (𝟙 X) x (O a) (u a) = gm (𝟙 X) x (O b) (u b)) :
    ∃ d : Γ(X, V)ˣ, ∀ a x, x ∈ O a → gm (𝟙 X) x V d = gm (𝟙 X) x (O a) (u a) := by
  have hcover : V ≤ iSup O := fun x hx => by
    obtain ⟨a, ha⟩ := hcov x hx
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨a, ha⟩
  have compat : ∀ w : ∀ a, Γ(X, O a), (∀ a b x (ha : x ∈ O a) (hb : x ∈ O b),
      (X.presheaf.germ (O a) x ha).hom (w a) = (X.presheaf.germ (O b) x hb).hom (w b)) →
      TopCat.Presheaf.IsCompatible X.sheaf.1 O w := by
    intro w hw a b
    refine TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => ?_
    exact (TopCat.Presheaf.germ_res_apply X.presheaf _ x hx (w a)).trans
      ((hw a b x hx.1 hx.2).trans (TopCat.Presheaf.germ_res_apply X.presheaf _ x hx (w b)).symm)
  have hval : ∀ a b x (ha : x ∈ O a) (hb : x ∈ O b),
      (X.presheaf.germ (O a) x ha).hom (u a).1 = (X.presheaf.germ (O b) x hb).hom (u b).1 := by
    intro a b x ha hb
    have hv := congrArg Units.val (hu a b x ha hb)
    rw [gm_id_val_eq_germ _ x ha, gm_id_val_eq_germ _ x hb] at hv
    exact hv
  have hinv : ∀ a b x (ha : x ∈ O a) (hb : x ∈ O b),
      (X.presheaf.germ (O a) x ha).hom (u a)⁻¹.1 = (X.presheaf.germ (O b) x hb).hom (u b)⁻¹.1 := by
    intro a b x ha hb
    have hv := congrArg Units.val (congrArg (·⁻¹) (hu a b x ha hb))
    rw [← map_inv, ← map_inv, gm_id_val_eq_germ _ x ha, gm_id_val_eq_germ _ x hb] at hv
    exact hv
  obtain ⟨d0, hd0, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf O V (fun a => homOfLE (hO a)) hcover
    (fun a => (u a).1) (compat _ hval)
  obtain ⟨d1, hd1, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf O V (fun a => homOfLE (hO a)) hcover
    (fun a => (u a)⁻¹.1) (compat _ hinv)
  have g0 : ∀ a x (hx : x ∈ O a), (X.presheaf.germ V x (hO a hx)).hom d0 = (X.presheaf.germ (O a) x hx).hom (u a).1 :=
    fun a x hx => (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hO a)) x hx d0).symm.trans
      (congrArg (X.presheaf.germ (O a) x hx).hom (hd0 a))
  have g1 : ∀ a x (hx : x ∈ O a), (X.presheaf.germ V x (hO a hx)).hom d1 = (X.presheaf.germ (O a) x hx).hom (u a)⁻¹.1 :=
    fun a x hx => (TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE (hO a)) x hx d1).symm.trans
      (congrArg (X.presheaf.germ (O a) x hx).hom (hd1 a))
  have h01 : d0 * d1 = 1 := TopCat.Presheaf.section_ext X.sheaf V _ _ fun x hx => by
    obtain ⟨a, ha⟩ := hcov x hx
    exact calc (X.presheaf.germ V x hx).hom (d0 * d1)
          = (X.presheaf.germ V x hx).hom d0 * (X.presheaf.germ V x hx).hom d1 := RingHom.map_mul _ _ _
      _ = (X.presheaf.germ (O a) x ha).hom (u a).1 * (X.presheaf.germ (O a) x ha).hom (u a)⁻¹.1 := by
          rw [g0 a x ha, g1 a x ha]
      _ = 1 := by rw [← map_mul, Units.mul_inv, map_one]
      _ = (X.presheaf.germ V x hx).hom 1 := (map_one _).symm
  refine ⟨⟨d0, d1, h01, (mul_comm (d1 : Γ(X, V)) d0).trans h01⟩, fun a x hx => ?_⟩
  ext1
  rw [gm_id_val_eq_germ V x (hO a hx), gm_id_val_eq_germ (O a) x hx]
  exact g0 a x hx
private lemma gm_id_res {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Y) y V (res hVU a) = gm (𝟙 Y) y U a :=
  gm_res_lemma_4 hVU y hy a
end GlobalTheory.RigidTriv
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
noncomputable section
open GlobalTheory GlobalTheory.RigidTriv
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.RigidTriv
theorem _root_.solution : ∀ (X : Scheme.{0}) (P : Over X) (e : X ⟶ P.left) (N : LB P.left), e ≫ P.hom = 𝟙 X → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → N.IsLB → (∃ r : (N.pull e).Gen, r.IsGen) → (∀ x : X, ∃ V : X.Opens, x ∈ V ∧ ∃ t : (N.pull (P.hom ⁻¹ᵁ V).ι).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro X P e N he rig hN hr0 hloc
  obtain ⟨r, hr⟩ := hr0
  choose V hxV t ht using hloc
  choose s hs using fun x => exists_locGen (P.hom ⁻¹ᵁ V x) (ht x)
  choose s' hs' hn using fun x => exists_normalised hN he hr (V x) (hs x)
  have glue_i : ∀ i, ∃ T : Γ(P.left, N.U i)ˣ, ∀ x y, y ∈ P.hom ⁻¹ᵁ V x ⊓ N.U i →
      gm (𝟙 _) y (N.U i) T = gm (𝟙 _) y (P.hom ⁻¹ᵁ V x ⊓ N.U i) (s' x i) := fun i =>
    exists_unit_on_open_of_gm_agree_on_cover (N.U i) (fun x => P.hom ⁻¹ᵁ V x ⊓ N.U i) (fun x => inf_le_right)
      (fun y hy => ⟨P.hom y, (show y ∈ P.hom ⁻¹ᵁ V (P.hom y) ⊓ N.U i from ⟨hxV (P.hom y), hy⟩)⟩)
      (fun x => s' x i)
      (fun x x' y hx hx' => agree_of_rigid hN he rig (hs' x) (hs' x')
        (fun x0 h0 h0' j hj => (hn x x0 h0 j hj).trans (hn x' x0 h0' j hj).symm) y hx.1 hx'.1 i hx.2)
  choose T hT using glue_i
  refine ⟨⟨T⟩, fun i j => ?_⟩
  apply units_eq_of_gm_id_eq_on_open
  intro y hy
  have hy' : y ∈ N.U i ⊓ N.U j := hy
  have hx : y ∈ P.hom ⁻¹ᵁ V (P.hom y) := hxV (P.hom y)
  dsimp only
  rw [map_mul, gm_id_res _ y hy', gm_id_res _ y hy', hT i _ y ⟨hx, hy'.1⟩, hT j _ y ⟨hx, hy'.2⟩]
  exact hs' (P.hom y) P.left (𝟙 _) y i j hx hy'.1 hy'.2
end GlobalTheory.RigidTriv
