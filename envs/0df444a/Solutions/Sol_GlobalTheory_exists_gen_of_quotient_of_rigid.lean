-- Prove2me | solution 1 for GlobalTheory.exists_gen_of_quotient_of_rigid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:36:54.637805+00:00
-- url     : https://prove2.me/submissions/cbed3414-4851-4cf1-9124-55bbb237c4e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
import Theorems.Thm_GlobalTheory_GenDescent_exists_compat
import Theorems.Thm_GlobalTheory_GenDescent_Compat_ratio
import Theorems.Thm_GlobalTheory_GenDescent_exists_gen_of_range
import Theorems.Thm_GlobalTheory_FreeQuotient_coe_toInvariantsTensor
import Theorems.Thm_GlobalTheory_quotient_flat_baseChange
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_id_pull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.FreeQuotient.coe_toInvariantsTensor


section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace GenDescent
variable {Y Y' Z : Scheme.{0}}
private theorem gm_res' {X W : Scheme.{0}} (k : W ⟶ X) (w : W) {V V' : X.Opens} (h : V' ≤ V)
    (u : Γ(X, V)ˣ) (hw : k w ∈ V') : gm k w V' (res h u) = gm k w V u := by
  rw [← gm_id_pull k w V' hw (res h u), pullU_res₂, gm_rp₁ k w V _ _ hw]
private theorem gm_id_val_eq_germ' {Y : Scheme.{0}} {V : Y.Opens} (u : Γ(Y, V)ˣ) (y : Y) (hy : y ∈ V) :
    (gm (𝟙 Y) y V u).val = Y.presheaf.germ V y hy u.val := by
  have hy' : (𝟙 Y) y ∈ V := hy
  simp only [gm, dif_pos hy', pullU, MonoidHom.comp_apply, Units.coe_map]
  rfl
private theorem compat_mul_res_unit_and_gm_mul {Y Z : Scheme.{0}} {N : LB Z} {f : Y ⟶ Z}
    {a : ∀ i, Γ(Y, f ⁻¹ᵁ N.U i)ˣ} (ha : GenDescent.Compat N f a) (c : Γ(Y, ⊤)ˣ) :
    GenDescent.Compat N f (fun i => a i * res (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c) ∧
      ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i →
        gm k w _ (a i * res (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c) = gm k w _ (a i) * gm k w ⊤ c := by
  have h2 : ∀ (W : Scheme.{0}) (k : W ⟶ Y) (w : W) (i : N.ι), f (k w) ∈ N.U i →
      gm k w _ (a i * res (le_top : f ⁻¹ᵁ N.U i ≤ ⊤) c) = gm k w _ (a i) * gm k w ⊤ c :=
    fun W k w i hi => by rw [map_mul, gm_res' _ _ _ _ (show k w ∈ f ⁻¹ᵁ N.U i from hi)]
  refine ⟨fun W k w i j hi hj => ?_, h2⟩
  rw [h2 W k w i hi, h2 W k w j hj, ha W k w i j hi hj, _root_.mul_assoc]
private theorem appLE_unit_val_and_inv_eq_of_gm_invariant {Y : Scheme.{0}} {V : Y.Opens} (σ : Y ⟶ Y) (h : V ≤ σ ⁻¹ᵁ V) (u : Γ(Y, V)ˣ)
    (hu : ∀ y, y ∈ V → gm σ y V u = gm (𝟙 Y) y V u) :
    (σ.appLE V V h).hom u.val = u.val ∧ (σ.appLE V V h).hom (u⁻¹).val = (u⁻¹).val := by
  have key : ∀ v : Γ(Y, V)ˣ, (∀ y, y ∈ V → gm σ y V v = gm (𝟙 Y) y V v) →
      (σ.appLE V V h).hom v.val = v.val := by
    intro v hv
    apply TopCat.Presheaf.section_ext Y.sheaf V
    intro y hy
    exact ((gm_id_val_eq_germ' (res h (pullU σ V v)) y hy).symm.trans
      (congrArg Units.val ((gm_rp₁ σ y V V h hy v).trans (hv y hy)))).trans (gm_id_val_eq_germ' v y hy)
  exact ⟨key u hu, key u⁻¹ fun y hy => by rw [map_inv, map_inv, hu y hy]⟩
end GenDescent
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GenDescent
namespace GlobalTheory
theorem _root_.solution :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (P : Over X) (P' : Over X') (φ : P.left ⟶ P'.left) (e : X ⟶ P.left) (e' : X' ⟶ P'.left) (N : LB P'.left), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ P.hom P'.hom π → Flat P'.hom → e ≫ P.hom = 𝟙 X → e' ≫ P'.hom = 𝟙 X' → e ≫ φ = π ≫ e' → (∀ (V : X.Opens) (u : Γ(P.left, P.hom ⁻¹ᵁ V)) (h : V ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ V)), (e.appLE _ V h).hom u = 1 → u = 1) → N.IsLB → (∃ r : (N.pull e').Gen, r.IsGen) → (∃ t : (N.pull φ).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro Γ _ _ X X' ρ π P P' φ e e' N hq hpb hfl he he' hee hrig hN ⟨r, hr⟩ ⟨t, ht⟩
  have hT : (⊤ : P.left.Opens) ≤ P.hom ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hT' : P.hom ⁻¹ᵁ ⊤ ≤ ⊤ := le_top
  have hTX : (⊤ : X.Opens) ≤ e ⁻¹ᵁ (P.hom ⁻¹ᵁ ⊤) := fun _ _ => trivial
  obtain ⟨⟨τ, hτ⟩, hall⟩ := quotient_flat_baseChange Γ X X' P.left P'.left ρ π φ P.hom P'.hom hq hpb hfl
  obtain ⟨-, -, hφ⟩ := hall τ hτ
  have hρπ : ∀ g, (ρ g).hom ≫ π = π := hq.2.1
  have heτ : ∀ g, e ≫ (τ g).hom = (ρ g).hom ≫ e := fun g => hpb.hom_ext
    (by simp only [Category.assoc, (hτ g).1, hee, reassoc_of% (hρπ g)])
    (by simp only [Category.assoc, (hτ g).2, reassoc_of% he, he, Category.comp_id])
  have hpt : ∀ x, φ (e x) = e' (π x) := fun x => congrArg (fun h : X ⟶ P'.left => h.base x) hee
  have hρpt : ∀ g x, π ((ρ g).hom x) = π x := fun g x => congrArg (fun h : X ⟶ X' => h.base x) (hρπ g)
  have hτpt : ∀ g y, φ ((τ g).hom y) = φ y := fun g y =>
    congrArg (fun h : P.left ⟶ P'.left => h.base y) (hτ g).1
  obtain ⟨a, ha⟩ := exists_compat t ht
  obtain ⟨ar, har⟩ := exists_compat r hr
  obtain ⟨a1, ha1, ha1'⟩ := Compat.pull har π (π ≫ e') rfl
  obtain ⟨a2, ha2, ha2'⟩ := Compat.pull ha e (π ≫ e') hee
  obtain ⟨dX, hdX⟩ := Compat.ratio hN ha2 ha1
  have hc0g : ∀ (W : Scheme.{0}) (k : W ⟶ P.left) (w : W),
      gm k w ⊤ (res hT (pullU P.hom ⊤ dX⁻¹)) =
        (gm (k ≫ P.hom) w ⊤ dX)⁻¹ := by
    intro W k w
    rw [gm_res' _ _ _ _ (show k w ∈ (⊤ : P.left.Opens) from trivial), gm_pullU_eq_gm_comp, map_inv]
  obtain ⟨hA, hAm⟩ := compat_mul_res_unit_and_gm_mul ha
    (res hT (pullU P.hom ⊤ dX⁻¹))
  have hnorm : ∀ (W : Scheme.{0}) (k : W ⟶ X) (w : W) (i : N.ι), e' (π (k w)) ∈ N.U i →
      gm (k ≫ e) w _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤)
        (res hT (pullU P.hom ⊤ dX⁻¹))) =
        gm k w _ (a1 i) := by
    intro W k w i hi
    have hi' : φ ((k ≫ e) w) ∈ N.U i := by
      show φ (e (k w)) ∈ N.U i
      rw [hpt]; exact hi
    rw [hAm W (k ≫ e) w i hi', hc0g, ← ha2' W k w i hi, hdX W k w i hi, Category.assoc, he,
      Category.comp_id, _root_.mul_comm (gm k w ⊤ dX), _root_.mul_inv_cancel_right]
  have hinv : ∀ g (i : N.ι) (y : P.left), φ y ∈ N.U i →
      gm (τ g).hom y _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤)
        (res hT (pullU P.hom ⊤ dX⁻¹))) =
      gm (𝟙 P.left) y _ (a i * res (le_top : φ ⁻¹ᵁ N.U i ≤ ⊤)
        (res hT (pullU P.hom ⊤ dX⁻¹))) := by
    intro g
    obtain ⟨b, hb, hb'⟩ := Compat.pull hA (τ g).hom φ (hτ g).1
    obtain ⟨cg, hcg⟩ := Compat.ratio hN hb hA
    have hcge : ∀ x : X, gm e x ⊤ cg = 1 := by
      intro x
      have hx : e' (π x) ∈ ⨆ i, N.U i := by rw [hN.cover]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
      have hi' : φ (e x) ∈ N.U i := by rw [hpt]; exact hi
      have hiρ : e' (π ((ρ g).hom x)) ∈ N.U i := by rw [hρpt]; exact hi
      have h1 := hcg X e x i hi'
      rw [hb' X e x i hi', heτ g] at h1
      have hid : e' (π ((𝟙 X) x)) ∈ N.U i := hi
      rw [hnorm X (ρ g).hom x i hiρ, ha1' X (ρ g).hom x i hiρ, hρπ,
        ← Category.id_comp e, hnorm X (𝟙 X) x i hid, ha1' X (𝟙 X) x i hid, Category.id_comp] at h1
      exact mul_eq_right.1 h1.symm
    have hcg1 : ∀ y : P.left, gm (𝟙 P.left) y ⊤ cg = 1 := by
      have hu := hrig ⊤ (res hT' cg).val hTX (by
        apply TopCat.Presheaf.section_ext X.sheaf ⊤
        intro x hx
        have e1 : gm (𝟙 X) x ⊤ (res hTX
            (pullU e _ (res hT' cg))) = 1 := by
          rw [gm_rp₁ _ _ _ _ _ hx, gm_res' _ _ _ _ (show e x ∈ P.hom ⁻¹ᵁ ⊤ from trivial)]
          exact hcge x
        have e2 := congrArg Units.val e1
        rw [gm_id_val_eq_germ' _ x hx, Units.val_one] at e2
        exact e2.trans (map_one _).symm)
      intro y
      rw [← gm_res' _ _ hT' _ (show (𝟙 P.left) y ∈ P.hom ⁻¹ᵁ ⊤ from trivial),
        show res hT' cg = 1 from Units.ext (hu.trans Units.val_one.symm), map_one]
    intro i y hy
    have h1 := hcg P.left (𝟙 _) y i hy
    rw [hb' P.left (𝟙 _) y i hy, Category.id_comp, hcg1, _root_.one_mul] at h1
    exact h1
  exact exists_gen_of_range hA (fun V => (hφ V).1)
    (fun i => (hφ (N.U i)).2 _ fun g h => (appLE_unit_val_and_inv_eq_of_gm_invariant (τ g).hom h _ fun y hy => hinv g i y hy).1)
    (fun i => (hφ (N.U i)).2 _ fun g h => (appLE_unit_val_and_inv_eq_of_gm_invariant (τ g).hom h _ fun y hy => hinv g i y hy).2)
end GlobalTheory
