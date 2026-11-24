-- Prove2me | solution 1 for GlobalTheory.RigidTriv.agree_of_rigid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:56:35.750925+00:00
-- url     : https://prove2.me/submissions/65cb0748-52bb-4968-bcd8-31970febd309

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Theorems.Thm_GlobalTheory_RigidTriv_gm_stalk
import Theorems.Thm_GlobalTheory_RigidTriv_sec_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one

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
private lemma gm_val_eq_germ_app (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    Units.val (gm f z U a) = (Z.presheaf.germ (f ⁻¹ᵁ U) z h).hom (f.app U a.1) := by
  simp [gm, h, pullU]
private lemma gm_res_lemma_4 {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Y) y V (Units.map (Y.presheaf.map (homOfLE hVU).op).hom.toMonoidHom a) = gm (𝟙 Y) y U a := by
  ext1
  rw [gm_id_val_eq_germ V y hy, gm_id_val_eq_germ U y (hVU hy)]
  exact TopCat.Presheaf.germ_res_apply ..
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
private lemma germ_appLE_unit_eq_gm_val (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hVU : V ≤ f ⁻¹ᵁ U) (x : X) (hx : x ∈ V)
    (a : Γ(Y, U)ˣ) : (X.presheaf.germ V x hx).hom ((f.appLE U V hVU).hom a.1) = Units.val (gm f x U a) := by
  rw [gm_val_eq_germ_app f x U (hVU hx)]
  exact TopCat.Presheaf.germ_res_apply ..
private lemma exists_mem_U_of_isLB {N : LB Y} (hN : N.IsLB) (y : Y) : ∃ i, y ∈ N.U i := by
  have hy : y ∈ (⊤ : Y.Opens) := trivial
  rw [← hN.cover] at hy
  exact TopologicalSpace.Opens.mem_iSup.1 hy
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
theorem _root_.solution {N : LB Y} (hN : N.IsLB) {p : Y ⟶ X} {e : X ⟶ Y} (he : e ≫ p = 𝟙 X)
    (rig : ∀ (V : X.Opens) (u : Γ(Y, p ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1)
    {V V' : X.Opens} {s : ∀ i, Γ(Y, p ⁻¹ᵁ V ⊓ N.U i)ˣ} {s' : ∀ i, Γ(Y, p ⁻¹ᵁ V' ⊓ N.U i)ˣ}
    (hs : LocGen N (p ⁻¹ᵁ V) s) (hs' : LocGen N (p ⁻¹ᵁ V') s')
    (h : ∀ x, x ∈ V → x ∈ V' → ∀ i, e x ∈ N.U i →
      gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s i) = gm e x (p ⁻¹ᵁ V' ⊓ N.U i) (s' i))
    (y : Y) (hy : p y ∈ V) (hy' : p y ∈ V') (i : N.ι) (hi : y ∈ N.U i) :
    gm (𝟙 Y) y (p ⁻¹ᵁ V ⊓ N.U i) (s i) = gm (𝟙 Y) y (p ⁻¹ᵁ V' ⊓ N.U i) (s' i) := by
  have h1 : ∀ i, p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i ≤ p ⁻¹ᵁ V ⊓ N.U i := fun i y hy =>
    (show y ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨(show p y ∈ V ⊓ V' from hy.1).1, hy.2⟩)
  have h2 : ∀ i, p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i ≤ p ⁻¹ᵁ V' ⊓ N.U i := fun i y hy =>
    (show y ∈ p ⁻¹ᵁ V' ⊓ N.U i from ⟨(show p y ∈ V ⊓ V' from hy.1).2, hy.2⟩)
  have gmw : ∀ i y (hy : y ∈ p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i),
      gm (𝟙 Y) y _ (Units.map (Y.presheaf.map (homOfLE (h1 i)).op).hom.toMonoidHom (s i) /
        Units.map (Y.presheaf.map (homOfLE (h2 i)).op).hom.toMonoidHom (s' i)) =
      gm (𝟙 Y) y _ (s i) / gm (𝟙 Y) y _ (s' i) := by
    intro i y hy
    rw [map_div, gm_res_lemma_4 (h1 i) y hy, gm_res_lemma_4 (h2 i) y hy]
  obtain ⟨c, hc⟩ := exists_unit_on_open_of_gm_agree_on_cover (p ⁻¹ᵁ (V ⊓ V')) (fun i => p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i) (fun i => inf_le_left)
    (fun y hy => by
      obtain ⟨i, hi⟩ := exists_mem_U_of_isLB hN y
      exact ⟨i, hy, hi⟩)
    (fun i => Units.map (Y.presheaf.map (homOfLE (h1 i)).op).hom.toMonoidHom (s i) /
        Units.map (Y.presheaf.map (homOfLE (h2 i)).op).hom.toMonoidHom (s' i))
    (by
      intro i j y hi hj
      rw [gmw i y hi, gmw j y hj]
      have a1 := h1 i hi
      have a2 := h2 i hi
      have b1 := h1 j hj
      have b2 := h2 j hj
      rw [hs Y (𝟙 Y) y i j a1.1 a1.2 b1.2, hs' Y (𝟙 Y) y i j a2.1 a2.2 b2.2, mul_div_mul_left_eq_div])
  have hle : V ⊓ V' ≤ e ⁻¹ᵁ (p ⁻¹ᵁ (V ⊓ V')) := fun x hx => sec_mem he hx
  have c1 : c.1 = 1 := rig (V ⊓ V') c.1 hle (TopCat.Presheaf.section_ext X.sheaf _ _ _ fun x hx => by
    obtain ⟨i, hi⟩ := exists_mem_U_of_isLB hN (e x)
    have hxO : e x ∈ p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i := ⟨hle hx, hi⟩
    have hx' : x ∈ V ⊓ V' := hx
    have hgm : gm e x (p ⁻¹ᵁ (V ⊓ V')) c = 1 := by
      rw [gm_stalk e x _ (hle hx), hc i (e x) hxO, gmw i (e x) hxO, map_div, ← gm_stalk e x _ (h1 i hxO),
        ← gm_stalk e x _ (h2 i hxO), h x hx'.1 hx'.2 i hi, div_self']
    exact (germ_appLE_unit_eq_gm_val e _ _ hle x hx c).trans (by rw [hgm, Units.val_one]; exact (RingHom.map_one _).symm))
  have hyc : y ∈ p ⁻¹ᵁ (V ⊓ V') ⊓ N.U i := ⟨(show p y ∈ V ⊓ V' from ⟨hy, hy'⟩), hi⟩
  have key := hc i y hyc
  rw [gmw i y hyc, show c = 1 from Units.ext c1, map_one] at key
  exact (div_eq_one.1 key.symm)
end GlobalTheory.RigidTriv
