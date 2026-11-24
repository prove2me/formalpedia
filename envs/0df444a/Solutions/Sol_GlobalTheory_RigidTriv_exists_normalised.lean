-- Prove2me | solution 1 for GlobalTheory.RigidTriv.exists_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:16:49.189821+00:00
-- url     : https://prove2.me/submissions/acf28ae8-d02f-4110-aba3-6baf2cc65a1a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Theorems.Thm_GlobalTheory_RigidTriv_gm_stalk
import Theorems.Thm_GlobalTheory_RigidTriv_gm_pull_id
import Theorems.Thm_GlobalTheory_RigidTriv_pull_gen
import Theorems.Thm_GlobalTheory_RigidTriv_sec_mem
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
private lemma gm_val_eq_germ_app (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) (a : Γ(Y, U)ˣ) :
    Units.val (gm f z U a) = (Z.presheaf.germ (f ⁻¹ᵁ U) z h).hom (f.app U a.1) := by
  simp [gm, h, pullU]
private lemma gm_res_lemma_4 {U V : Y.Opens} (hVU : V ≤ U) (y : Y) (hy : y ∈ V) (a : Γ(Y, U)ˣ) :
    gm (𝟙 Y) y V (Units.map (Y.presheaf.map (homOfLE hVU).op).hom.toMonoidHom a) = gm (𝟙 Y) y U a := by
  ext1
  rw [gm_id_val_eq_germ V y hy, gm_id_val_eq_germ U y (hVU hy)]
  exact TopCat.Presheaf.germ_res_apply ..
private lemma gm_units_map_restrict (f : Z ⟶ Y) (z : Z) {U V : Y.Opens} (hVU : V ≤ U) (hz : f z ∈ V) (a : Γ(Y, U)ˣ) :
    gm f z V (Units.map (Y.presheaf.map (homOfLE hVU).op).hom.toMonoidHom a) = gm f z U a := by
  rw [gm_stalk f z V hz, gm_stalk f z U (hVU hz), gm_res_lemma_4 hVU (f z) hz]
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
private lemma gm_comp_eq_gm_pullU (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) (U : Z.Opens) (h : f x ∈ g ⁻¹ᵁ U) (a : Γ(Z, U)ˣ) :
    gm (f ≫ g) x U a = gm f x (g ⁻¹ᵁ U) (pullU g U a) := by
  ext1
  rw [gm_val_eq_germ_app (f ≫ g) x U h, gm_val_eq_germ_app f x (g ⁻¹ᵁ U) h]
  simp [pullU]
  rfl
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
    {r : (N.pull e).Gen} (hr : r.IsGen) (V : X.Opens) {s : ∀ i, Γ(Y, p ⁻¹ᵁ V ⊓ N.U i)ˣ}
    (hs : LocGen N (p ⁻¹ᵁ V) s) :
    ∃ s', LocGen N (p ⁻¹ᵁ V) s' ∧ ∀ x ∈ V, ∀ i, e x ∈ N.U i →
      gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s' i) = gm (𝟙 X) x ((N.pull e).U (fun _ => i)) (r.s fun _ => i) := by
  have hOe : ∀ i, V ⊓ ((N.pull e).U fun _ => i) ≤ e ⁻¹ᵁ (p ⁻¹ᵁ V ⊓ N.U i) := fun i x hx =>
    (show e x ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨sec_mem he hx.1, Set.mem_iInter.1 hx.2 PUnit.unit⟩)
  have hOr : ∀ i, V ⊓ ((N.pull e).U fun _ => i) ≤ (N.pull e).U fun _ => i := fun i => inf_le_right
  have gmu : ∀ i x (hx : x ∈ V ⊓ ((N.pull e).U fun _ => i)),
      gm (𝟙 X) x _ (Units.map (X.presheaf.map (homOfLE (hOr i)).op).hom.toMonoidHom (r.s fun _ => i) /
        Units.map (X.presheaf.map (homOfLE (hOe i)).op).hom.toMonoidHom (pullU e _ (s i))) =
      gm (𝟙 X) x _ (r.s fun _ => i) / gm e x (p ⁻¹ᵁ V ⊓ N.U i) (s i) := by
    intro i x hx
    rw [map_div, gm_res_lemma_4 (hOr i) x hx, gm_res_lemma_4 (hOe i) x hx, gm_pull_id e x _ (hOe i hx)]
  obtain ⟨d, hd⟩ := exists_unit_on_open_of_gm_agree_on_cover V (fun i => V ⊓ ((N.pull e).U fun _ => i)) (fun i => inf_le_left)
    (fun x hx => by
      obtain ⟨i, hi⟩ := exists_mem_U_of_isLB hN (e x)
      exact ⟨i, hx, Set.mem_iInter.2 fun _ => hi⟩)
    (fun i => Units.map (X.presheaf.map (homOfLE (hOr i)).op).hom.toMonoidHom (r.s fun _ => i) /
        Units.map (X.presheaf.map (homOfLE (hOe i)).op).hom.toMonoidHom (pullU e _ (s i)))
    (by
      intro i j x hi hj
      rw [gmu i x hi, gmu j x hj]
      have hxi : e x ∈ p ⁻¹ᵁ V ⊓ N.U i := hOe i hi
      have hxj : e x ∈ p ⁻¹ᵁ V ⊓ N.U j := hOe j hj
      rw [pull_gen hr x i j hxi.2 hxj.2, hs X e x i j hxi.1 hxi.2 hxj.2, mul_div_mul_left_eq_div])
  refine ⟨fun i => Units.map (Y.presheaf.map (homOfLE (inf_le_left : p ⁻¹ᵁ V ⊓ N.U i ≤ p ⁻¹ᵁ V)).op).hom.toMonoidHom
    (pullU p V d) * s i, ?_, ?_⟩
  · intro Z f z i j hW hi hj
    rw [map_mul, map_mul, gm_units_map_restrict f z inf_le_left (show f z ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨hW, hi⟩),
      gm_units_map_restrict f z inf_le_left (show f z ∈ p ⁻¹ᵁ V ⊓ N.U j from ⟨hW, hj⟩), hs Z f z i j hW hi hj, mul_left_comm]
  · intro x hx i hi
    have hxO : x ∈ V ⊓ ((N.pull e).U fun _ => i) := ⟨hx, Set.mem_iInter.2 fun _ => hi⟩
    rw [map_mul, gm_units_map_restrict e x inf_le_left (show e x ∈ p ⁻¹ᵁ V ⊓ N.U i from ⟨sec_mem he hx, hi⟩),
      ← gm_comp_eq_gm_pullU e p x V (sec_mem he hx) d, he, hd i x hxO, gmu i x hxO, div_mul_cancel]
end GlobalTheory.RigidTriv
