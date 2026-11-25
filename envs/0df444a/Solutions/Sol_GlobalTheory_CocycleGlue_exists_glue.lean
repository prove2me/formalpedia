-- Prove2me | solution 1 for GlobalTheory.CocycleGlue.exists_glue
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:25:07.800813+00:00
-- url     : https://prove2.me/submissions/c301b3dc-1ef2-4e1c-b4fc-5f0c43d642f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GlueSchemesOverOpensAlongCocycle
import Theorems.Thm_GlobalTheory_CocycleGlue_exists_desc
import Theorems.Thm_GlobalTheory_CoverGlue_hom_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CocycleGlue
namespace GlobalTheory.CocycleGlue
theorem _root_.solution {S : Scheme.{0}} {I : Type} (V X : I → Scheme.{0}) (κ : ∀ i, V i ⟶ S)
    (hκ : ∀ i, IsOpenImmersion (κ i)) (g : ∀ i, X i ⟶ V i) (B : I → I → Scheme.{0})
    (a : ∀ i j, B i j ⟶ X i) (b : ∀ i j, B i j ⟶ X j)
    (ha : ∀ i j, IsPullback (a i j) (b i j ≫ g j) (g i ≫ κ i) (κ j))
    (hb : ∀ i j, IsPullback (b i j) (a i j ≫ g i) (g j ≫ κ j) (κ i))
    (hc : ∀ i j k (T : Scheme.{0}) (x : T ⟶ B i j) (y : T ⟶ B j k) (z : T ⟶ B i k),
      x ≫ b i j = y ≫ a j k → x ≫ a i j = z ≫ a i k → y ≫ b j k = z ≫ b i k) :
    ∃ (A : Scheme.{0}) (F : A ⟶ S) (ψ : ∀ i, X i ⟶ A),
      (∀ i, IsPullback (ψ i) (g i) F (κ i)) ∧ ∀ i j, IsPullback (a i j) (b i j) (ψ i) (ψ j) := by
  classical
  have hma : ∀ i j, IsOpenImmersion (a i j) := fun i j =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (ha i j).flip (hκ j)
  have mono_a : ∀ i j, Mono (a i j) := fun i j => by
    have := hma i j
    infer_instance
  have mono_κ : ∀ i, Mono (κ i) := fun i => by
    have := hκ i
    infer_instance
  have ext_a : ∀ i j {T : Scheme.{0}} (x y : T ⟶ B i j), x ≫ a i j = y ≫ a i j → x = y :=
    fun i j _ x y h => (mono_a i j).right_cancellation x y h
  have ext_κ : ∀ i {T : Scheme.{0}} (x y : T ⟶ V i), x ≫ κ i = y ≫ κ i → x = y :=
    fun i _ x y h => (mono_κ i).right_cancellation x y h
  have hbw : ∀ i j, b i j ≫ g j ≫ κ j = a i j ≫ g i ≫ κ i := fun i j => by
    simpa only [Category.assoc] using (hb i j).w
  have iso_a : ∀ i, IsIso (a i i) := fun i => by
    have hw : a i i ≫ g i = b i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (ha i i).w)
    refine ⟨⟨(ha i i).lift (𝟙 _) (g i) (by simp), ?_, (ha i i).lift_fst _ _ _⟩⟩
    apply ext_a i i
    rw [Category.assoc, (ha i i).lift_fst, Category.comp_id, Category.id_comp]
  have iso_b : ∀ i, IsIso (b i i) := fun i => by
    have hw : b i i ≫ g i = a i i ≫ g i := ext_κ i _ _ (by
      rw [Category.assoc]
      exact (hb i i).w)
    have hmb : Mono (b i i) := by
      have := MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hb i i).flip (hκ i)
      infer_instance
    refine ⟨⟨(hb i i).lift (𝟙 _) (g i) (by simp), ?_, (hb i i).lift_fst _ _ _⟩⟩
    apply hmb.right_cancellation
    rw [Category.assoc, (hb i i).lift_fst, Category.comp_id, Category.id_comp]
  have diag : ∀ i, a i i = b i i := fun i => by
    have := iso_a i
    have := iso_b i
    have h := hc i i i (B i i) (𝟙 _) (b i i ≫ inv (a i i)) (𝟙 _) (by simp) (by simp)
    have h2 : inv (a i i) ≫ b i i = 𝟙 _ := by
      rw [← cancel_epi (b i i)]
      simpa using h
    rw [IsIso.inv_comp_eq, Category.comp_id] at h2
    exact h2.symm
  have ht : ∀ i j, ∃ t : B i j ⟶ B j i, t ≫ a j i = b i j ∧ t ≫ b j i = a i j := fun i j => by
    have := iso_a i
    refine ⟨(ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w, (ha j i).lift_fst _ _ _, ?_⟩
    have h := hc i j i (B i j) (𝟙 _) ((ha j i).lift (b i j) (a i j ≫ g i) (hb i j).w)
      (a i j ≫ inv (a i i)) (by rw [IsPullback.lift_fst, Category.id_comp]) (by simp)
    rw [h, ← diag i]
    simp
  choose t ht_a ht_b using ht
  have t_id : ∀ i, t i i = 𝟙 _ := fun i =>
    ext_a i i _ _ (by rw [ht_a, Category.id_comp, diag])
  have t_inv : ∀ i j, t i j ≫ t j i = 𝟙 _ := fun i j =>
    ext_a i j _ _ (by rw [Category.assoc, ht_a, ht_b, Category.id_comp])
  have ht' : ∀ i j k, ∃ τ : pullback (a i j) (a i k) ⟶ pullback (a j k) (a j i),
      τ ≫ pullback.snd _ _ = pullback.fst _ _ ≫ t i j ∧
        τ ≫ pullback.fst _ _ ≫ a j k = pullback.fst _ _ ≫ b i j := fun i j k => by
    have w : (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j =
        (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
      calc (pullback.fst (a i j) (a i k) ≫ b i j) ≫ g j ≫ κ j
          = pullback.fst (a i j) (a i k) ≫ a i j ≫ g i ≫ κ i := by rw [Category.assoc, hbw]
        _ = pullback.snd (a i j) (a i k) ≫ a i k ≫ g i ≫ κ i := by rw [pullback.condition_assoc]
        _ = (pullback.snd (a i j) (a i k) ≫ b i k ≫ g k) ≫ κ k := by
          rw [← hbw]
          simp only [Category.assoc]
    refine ⟨pullback.lift ((ha j k).lift _ _ w) (pullback.fst _ _ ≫ t i j) ?_, pullback.lift_snd _ _ _, ?_⟩
    · rw [IsPullback.lift_fst, Category.assoc, ht_a]
    · rw [pullback.lift_fst_assoc, IsPullback.lift_fst]
  choose t' ht'_snd ht'_fst using ht'
  have cocycle : ∀ i j k, t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _ := fun i j k => by
    have c1 := hc i j k _ (pullback.fst (a i j) (a i k)) (t' i j k ≫ pullback.fst _ _)
      (pullback.snd (a i j) (a i k)) (by rw [Category.assoc, ht'_fst]) pullback.condition
    have c2 : (t' i j k ≫ t' j k i) ≫ pullback.fst _ _ = pullback.snd (a i j) (a i k) ≫ t i k := by
      apply ext_a k i
      simp only [Category.assoc, ht'_fst, ht_a]
      simpa only [Category.assoc] using c1
    have c2' : ∀ {Z : Scheme.{0}} (h : B k i ⟶ Z),
        t' i j k ≫ t' j k i ≫ pullback.fst _ _ ≫ h = pullback.snd (a i j) (a i k) ≫ t i k ≫ h := by
      intro Z h
      simp only [← Category.assoc, c2]
    apply pullback.hom_ext
    · apply ext_a i j
      simp only [Category.assoc, Category.id_comp, ht'_fst]
      rw [c2' (b k i), ht_b]
      exact pullback.condition.symm
    · simp only [Category.assoc, Category.id_comp, ht'_snd]
      rw [c2' (t k i), t_inv, Category.comp_id]
  let D : Scheme.GlueData.{0} :=
    { J := I, U := X, V := fun p => B p.1 p.2, f := a, f_mono := mono_a,
      f_hasPullback := fun _ _ _ => inferInstance, f_id := iso_a, t := t, t_id := t_id,
      t' := t', t_fac := ht'_snd, cocycle := cocycle, f_open := hma }
  obtain ⟨F, hF⟩ := exists_desc D (fun i => g i ≫ κ i) (fun i j => by
    change a i j ≫ g i ≫ κ i = (t i j ≫ a j i) ≫ g j ≫ κ j
    rw [ht_a]
    exact (hbw i j).symm)
  have hV : ∀ i j, IsPullback (a i j) (b i j) (D.ι i) (D.ι j) := fun i j => by
    have h : IsPullback (D.f i j) (D.t i j ≫ D.f j i) (D.ι i) (D.ι j) :=
      IsPullback.of_isLimit (D.vPullbackConeIsLimit i j)
    have e : D.t i j ≫ D.f j i = b i j := ht_a i j
    rw [e] at h
    exact h
  refine ⟨D.glued, F, fun i => D.ι i, fun i => ?_, hV⟩
  have hw : D.ι i ≫ F = g i ≫ κ i := hF i
  have hιi : IsOpenImmersion (D.ι i) := D.ι_isOpenImmersion i
  have hr : ∀ {T : Scheme.{0}} (u : T ⟶ D.glued) (v : T ⟶ V i), u ≫ F = v ≫ κ i →
      Set.range u ⊆ Set.range (D.ι i) := by
    intro T u v huv x hx
    obtain ⟨t0, rfl⟩ := hx
    obtain ⟨j, y, hy⟩ := D.ι_jointly_surjective (u t0)
    have e1 : (g j ≫ κ j) y = κ i (v t0) := by
      have h1 := congrArg (fun φ : T ⟶ S => φ t0) huv
      have h2 := congrArg (fun φ : D.U j ⟶ S => φ y) (hF j)
      simp only [Scheme.Hom.comp_apply] at h1 h2 ⊢
      rw [← h2, hy]
      exact h1
    obtain ⟨z', hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g j ≫ κ j) (g := κ i) y (v t0) e1
    refine ⟨b j i ((ha j i).isoPullback.inv z'), ?_⟩
    have h3 := congrArg (fun φ : pullback (g j ≫ κ j) (κ i) ⟶ D.glued => φ z')
      (congrArg (fun φ => (ha j i).isoPullback.inv ≫ φ) (hV j i).w)
    simp only [Scheme.Hom.comp_apply] at h3
    rw [← h3, ← hy, ← hz1, ← IsPullback.isoPullback_inv_fst (ha j i), Scheme.Hom.comp_apply]
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw
    (fun s => IsOpenImmersion.lift (D.ι i) s.fst (hr s.fst s.snd s.condition)) ?_ ?_ ?_)
  · intro s
    exact IsOpenImmersion.lift_fac _ _ _
  · intro s
    apply ext_κ i
    rw [Category.assoc, ← hw, ← Category.assoc, IsOpenImmersion.lift_fac, s.condition]
  · intro s m h1 _
    apply (cancel_mono (D.ι i)).1
    rw [h1, IsOpenImmersion.lift_fac]
end GlobalTheory.CocycleGlue
