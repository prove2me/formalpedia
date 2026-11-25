-- Prove2me | solution 1 for GlobalTheory.BundleNormalise.exists_iso_normalised
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:28:58.538901+00:00
-- url     : https://prove2.me/submissions/634a3b43-a2f3-4b18-ad6c-eb845b86ca2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsPartialBundleIsoNormalised
import Theorems.Thm_GlobalTheory_BundleNormalise_gm_iso
import Theorems.Thm_GlobalTheory_RigidTriv_pull_gen
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__4da20663a66f
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_id_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_inv

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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
namespace GlobalTheory.BundleNormalise
open GlobalTheory.RigidTriv
variable {X Y : Scheme.{0}}
private theorem gm_res_eq_gm (f : Y ⟶ X) (y : Y) {U V : X.Opens} (h : V ≤ U) (hy : f y ∈ V) (u : Γ(X, U)ˣ) :
    gm f y V (res h u) = gm f y U u := by
  rw [← gm_id_pull f y V hy, pullU_res₂ f h u]
  exact gm_rp₁ f y U (f ⁻¹ᵁ V) (f.preimage_mono h) hy u
private theorem units_ext_of_gm_id_eq {Z : Scheme.{0}} {W : Z.Opens} (u v : Γ(Z, W)ˣ)
    (h : ∀ x ∈ W, gm (𝟙 Z) x W u = gm (𝟙 Z) x W v) : u = v := by
  have key : (Scheme.Hom.app (𝟙 Z) W).hom u.val = (Scheme.Hom.app (𝟙 Z) W).hom v.val := by
    apply TopCat.Presheaf.section_ext Z.sheaf
    intro x hx
    have hx' : (𝟙 Z) x ∈ W := hx
    have e := congrArg Units.val (h x hx)
    simp only [gm, pullU, dif_pos hx', MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at e
    exact e
  ext1
  exact (ConcreteCategory.bijective_of_isIso (Scheme.Hom.app (𝟙 Z) W)).1 key
private theorem res_res_units' {X : Scheme.{0}} {U V W : X.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (u : Γ(X, U)ˣ) :
    res h2 (res h1 u) = res (h2.trans h1) u := by
  ext1
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl
private theorem mem_pull_U_of_mem {X S : Scheme.{0}} (M : LB X) (e : S ⟶ X) (x : S) (a : M.ι) (h : e x ∈ M.U a) :
    x ∈ (M.pull e).U (fun _ => a) :=
  Set.mem_iInter.2 fun _ => h
private theorem comm_mul_mul_inv_mul_mul_inv_inv_eq {G : Type*} [CommGroup G] (g g' a a' w : G) :
    g * a * (g' * a')⁻¹ * (g * g'⁻¹ * w)⁻¹ = a * a'⁻¹ * w⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
private theorem eq_mul_mul_inv_mul_inv_mul {G : Type*} [CommGroup G] (a b w : G) : a = w * (a * b⁻¹ * w⁻¹) * b := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel
end GlobalTheory.BundleNormalise
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.BundleNormalise
open GlobalTheory.RigidTriv
variable {X Y : Scheme.{0}}
namespace GlobalTheory.BundleNormalise
theorem _root_.solution : ∀ (X S : Scheme.{0}) (p : X ⟶ S) (e : S ⟶ X) (V V' : S.Opens) (M M' : LB X) (r : (M.pull e).Gen) (r' : (M'.pull e).Gen), e ≫ p = 𝟙 S → ⨆ a, M.U a = p ⁻¹ᵁ V → ⨆ a, M'.U a = p ⁻¹ᵁ V' → r.IsGen → r'.IsGen → LBIso M' M → ∃ w : LB.Iso M' M, w.IsGen ∧ ∀ (x : S) (a : M.ι) (b : M'.ι), e x ∈ M.U a → e x ∈ M'.U b → gm (𝟙 S) x ((M.pull e).U fun _ => a) (r.s fun _ => a) = gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x ((M'.pull e).U fun _ => b) (r'.s fun _ => b) := by
  intro X S p e V V' M M' r r' he hV hV' hr hr' hw
  obtain ⟨w, hw⟩ := hw
  let O : M.ι × M'.ι → S.Opens := fun k =>
    (M.pull e).U (fun _ => k.1) ⊓ (M'.pull e).U (fun _ => k.2) ⊓ e ⁻¹ᵁ (M.U k.1 ⊓ M'.U k.2)
  let c : ∀ k, Γ(S, O k)ˣ := fun k =>
    res (inf_le_left.trans inf_le_left : O k ≤ _) (r.s fun _ => k.1) *
      (res (inf_le_left.trans inf_le_right : O k ≤ _) (r'.s fun _ => k.2))⁻¹ *
      (res (inf_le_right : O k ≤ _) (pullU e (M.U k.1 ⊓ M'.U k.2) (w.s k)))⁻¹

  have hc : ∀ a b x, x ∈ O (a, b) → gm (𝟙 S) x (O (a, b)) (c (a, b)) =
      gm (𝟙 S) x _ (r.s fun _ => a) * (gm (𝟙 S) x _ (r'.s fun _ => b))⁻¹ *
        (gm e x (M.U a ⊓ M'.U b) (w.s (a, b)))⁻¹ := by
    intro a b x hx
    simp only [c]
    rw [map_mul, map_mul, map_inv, map_inv, gm_res_eq_gm (𝟙 S) x _ hx, gm_res_eq_gm (𝟙 S) x _ hx,
      gm_res_eq_gm (𝟙 S) x _ hx]
    refine congrArg (HMul.hMul _) (congrArg Inv.inv ?_)
    exact gm_id_pull e x _ hx.2 _

  have hcomp : ∀ k l, res (inf_le_left : O k ⊓ O l ≤ O k) (c k) = res (inf_le_right : O k ⊓ O l ≤ O l) (c l) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩
    apply units_ext_of_gm_id_eq
    intro x hx
    have hk := hx.1
    have hl := hx.2
    rw [gm_res_eq_gm (𝟙 S) x _ hx, gm_res_eq_gm (𝟙 S) x _ hx, hc a b x hk, hc a' b' x hl,
      pull_gen hr x a a' hk.2.1 hl.2.1, pull_gen hr' x b b' hk.2.2 hl.2.2,
      gm_iso hw e x a a' b b' ⟨hk.2, hl.2⟩]
    exact comm_mul_mul_inv_mul_mul_inv_inv_eq _ _ _ _ _

  obtain ⟨s0, hs0, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf O (⨆ k, O k)
    (fun i => homOfLE (le_iSup O i)) le_rfl (fun i => (c i).val)
    (fun i j => congrArg Units.val (hcomp i j))
  obtain ⟨t0, ht0, -⟩ := TopCat.Sheaf.existsUnique_gluing' S.sheaf O (⨆ k, O k)
    (fun i => homOfLE (le_iSup O i)) le_rfl (fun i => (c i).inv)
    (fun i j => congrArg Units.inv (hcomp i j))
  have hst : s0 * t0 = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' S.sheaf O (⨆ k, O k) (fun i => homOfLE (le_iSup O i)) le_rfl
    intro i
    rw [map_mul, map_one, hs0 i, ht0 i]
    exact (c i).val_inv
  have hts : t0 * s0 = 1 := by
    apply TopCat.Sheaf.eq_of_locally_eq' S.sheaf O (⨆ k, O k) (fun i => homOfLE (le_iSup O i)) le_rfl
    intro i
    rw [map_mul, map_one, hs0 i, ht0 i]
    exact (c i).inv_val
  let c0 : Γ(S, ⨆ k, O k)ˣ := ⟨s0, t0, hst, hts⟩
  have hc0 : ∀ k, res (le_iSup O k) c0 = c k := fun k => Units.ext (hs0 k)

  have hpe : ∀ x, p (e x) = x := fun x => by
    have := congrArg (fun f => f.base x) he
    simpa using this
  have hk : ∀ k : M.ι × M'.ι, (LB.div M M').U k ≤ p ⁻¹ᵁ (⨆ k, O k) := by
    rintro ⟨a, b⟩ y hy
    have h1 : y ∈ ⨆ a, M.U a := TopologicalSpace.Opens.mem_iSup.2 ⟨a, hy.1⟩
    have h2 : y ∈ ⨆ b, M'.U b := TopologicalSpace.Opens.mem_iSup.2 ⟨b, hy.2⟩
    rw [hV] at h1
    rw [hV'] at h2
    have h3 : e (p y) ∈ p ⁻¹ᵁ V := by
      show p (e (p y)) ∈ V
      rw [hpe]
      exact h1
    have h4 : e (p y) ∈ p ⁻¹ᵁ V' := by
      show p (e (p y)) ∈ V'
      rw [hpe]
      exact h2
    rw [← hV] at h3
    rw [← hV'] at h4
    obtain ⟨a', ha'⟩ := TopologicalSpace.Opens.mem_iSup.1 h3
    obtain ⟨b', hb'⟩ := TopologicalSpace.Opens.mem_iSup.1 h4
    exact TopologicalSpace.Opens.mem_iSup.2
      ⟨(a', b'), ⟨⟨mem_pull_U_of_mem M e _ a' ha', mem_pull_U_of_mem M' e _ b' hb'⟩, ⟨ha', hb'⟩⟩⟩
  refine ⟨⟨fun k => w.s k * res (hk k) (pullU p _ c0)⟩, ?_, ?_⟩
  · intro i j
    dsimp only
    rw [map_mul, map_mul, hw i j, res_res_units', res_res_units', _root_.mul_assoc]
  · intro x a b hxa hxb
    have hx : x ∈ O (a, b) := ⟨⟨mem_pull_U_of_mem M e x a hxa, mem_pull_U_of_mem M' e x b hxb⟩, ⟨hxa, hxb⟩⟩
    have hxab : e x ∈ M.U a ⊓ M'.U b := ⟨hxa, hxb⟩
    have hx0 : x ∈ ⨆ k, O k := le_iSup O (a, b) hx
    have hz : x ∈ e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k)) := by
      show p (e x) ∈ ⨆ k, O k
      rw [hpe]
      exact hx0
    have hP : gm e x (M.U a ⊓ M'.U b) (res (hk (a, b)) (pullU p _ c0)) = gm (𝟙 S) x (O (a, b)) (c (a, b)) := by
      calc gm e x (M.U a ⊓ M'.U b) (res (hk (a, b)) (pullU p _ c0))
          = gm e x (p ⁻¹ᵁ (⨆ k, O k)) (pullU p _ c0) := gm_res_eq_gm e x (hk (a, b)) hxab _
        _ = gm (𝟙 S) x (e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k))) (pullU e _ (pullU p _ c0)) := (gm_id_pull e x _ hz _).symm
        _ = gm (𝟙 S) x (e ⁻¹ᵁ (p ⁻¹ᵁ (⨆ k, O k))) (res le_rfl (pullU e _ (pullU p _ c0))) :=
          (gm_res_eq_gm (𝟙 S) x le_rfl hz _).symm
        _ = gm (e ≫ p) x (⨆ k, O k) c0 := gm_rp₂ e p x _ _ le_rfl hz c0
        _ = gm (𝟙 S) x (⨆ k, O k) c0 := by rw [he]
        _ = gm (𝟙 S) x (O (a, b)) (res (le_iSup O (a, b)) c0) := (gm_res_eq_gm (𝟙 S) x _ hx c0).symm
        _ = gm (𝟙 S) x (O (a, b)) (c (a, b)) := congrArg _ (hc0 (a, b))
    have hw' : gm e x (M.U a ⊓ M'.U b) (w.s (a, b) * res (hk (a, b)) (pullU p _ c0)) =
        gm e x (M.U a ⊓ M'.U b) (w.s (a, b)) * gm (𝟙 S) x (O (a, b)) (c (a, b)) :=
      (map_mul _ _ _).trans (congrArg _ hP)
    refine Eq.trans ?_ (congrArg (· * gm (𝟙 S) x _ (r'.s fun _ => b)) hw'.symm)
    rw [hc a b x hx]
    exact eq_mul_mul_inv_mul_inv_mul _ _ _
end GlobalTheory.BundleNormalise
