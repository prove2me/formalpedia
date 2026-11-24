-- Prove2me | solution 1 for GlobalTheory.MulUnramified.eq_one_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:19:54.772047+00:00
-- url     : https://prove2.me/submissions/a6095659-c76b-45cc-b202-01008155aaad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_FormallyUnramifiedMulN
import Theorems.Thm_GlobalTheory_MulUnramified_appLE_congr
import Theorems.Thm_GlobalTheory_MulUnramified_preimage_eq
import Theorems.Thm_GlobalTheory_MulUnramified_app_sub_eq_zero
import Theorems.Thm_GlobalTheory_MulUnramified_comp_appLE_apply
import Theorems.Thm_GlobalTheory_MulUnramified_le_preimage_of_comp
import Theorems.Thm_GlobalTheory_MulUnramified_parallelogram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.MulUnramified
variable {S : Scheme.{0}}
namespace GlobalTheory.MulUnramified
theorem _root_.solution (G : Over S) [GrpObj G] {T₀ T : Over S} (j : T₀ ⟶ T)
    (hj : Function.Surjective j.left)
    (hsq : ∀ (W : T.left.Opens), IsAffineOpen W → ∀ s t : Γ(T.left, W),
      j.left.app W s = 0 → j.left.app W t = 0 → s * t = 0)
    (n : ℕ) (hn : IsUnit (n : Γ(S, ⊤))) (z : T ⟶ G) (hz : j ≫ z = 1) (hzn : z ^ n = 1) :
    z = 1 := by
  apply Over.OverMorphism.ext
  refine Scheme.hom_ext_of_forall _ _ fun t ↦ ?_
  let e : T ⟶ G := 1
  have he : j ≫ e = 1 := by simp [e]
  obtain ⟨_, ⟨V, hV, rfl⟩, htV, -⟩ :=
    G.left.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (e.left t)) isOpen_univ
  have hcp : (lift e e).left ≫ (fst G G).left = e.left := by rw [← Over.comp_left, lift_fst]
  have hcq : (lift e e).left ≫ (snd G G).left = e.left := by rw [← Over.comp_left, lift_snd]
  have hcm : (lift e e).left ≫ (μ[G]).left = e.left := by
    rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one]
  obtain ⟨_, ⟨V', hV', rfl⟩, htV', hV'V : V' ≤ _⟩ :=
    (G ⊗ G).left.isBasis_affineOpens.exists_subset_of_mem_open (a := (lift e e).left t)
      (u := ((fst G G).left ⁻¹ᵁ V ⊓ (snd G G).left ⁻¹ᵁ V ⊓ (μ[G]).left ⁻¹ᵁ V : (G ⊗ G).left.Opens))
      ⟨⟨show ((lift e e).left ≫ (fst G G).left) t ∈ V by rwa [hcp],
        show ((lift e e).left ≫ (snd G G).left) t ∈ V by rwa [hcq]⟩,
        show ((lift e e).left ≫ (μ[G]).left) t ∈ V by rwa [hcm]⟩ (TopologicalSpace.Opens.isOpen _)
  have hp : V' ≤ (fst G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_left)
  have hq : V' ≤ (snd G G).left ⁻¹ᵁ V := hV'V.trans (inf_le_left.trans inf_le_right)
  have hm : V' ≤ (μ[G]).left ⁻¹ᵁ V := hV'V.trans inf_le_right
  obtain ⟨_, ⟨W, hW, rfl⟩, htW, hc : W ≤ (lift e e).left ⁻¹ᵁ V'⟩ :=
    T.left.isBasis_affineOpens.exists_subset_of_mem_open (a := t)
      (u := (lift e e).left ⁻¹ᵁ V') htV' (TopologicalSpace.Opens.isOpen _)
  refine ⟨W, htW, ?_⟩
  have heW : W ≤ e.left ⁻¹ᵁ V := hcp ▸ le_preimage_of_comp _ _ hp hc
  have near : ∀ x : T ⟶ G, j ≫ x = 1 → j.left ≫ x.left = j.left ≫ e.left := fun x hx ↦ by
    rw [← Over.comp_left, ← Over.comp_left, hx, he]
  have near₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 →
      j.left ≫ (lift x y).left = j.left ≫ (lift e e).left := fun x y hx hy ↦ by
    rw [← Over.comp_left, ← Over.comp_left, comp_lift, comp_lift, hx, hy, he]
  have hW₁ : ∀ x : T ⟶ G, j ≫ x = 1 → W ≤ x.left ⁻¹ᵁ V := fun x hx ↦ by
    rw [preimage_eq j.left hj (near x hx)]; exact heW
  have hW₂ : ∀ x y : T ⟶ G, j ≫ x = 1 → j ≫ y = 1 → W ≤ (lift x y).left ⁻¹ᵁ V' :=
    fun x y hx hy ↦ by rw [preimage_eq j.left hj (near₂ x y hx hy)]; exact hc
  have add : ∀ (x y : T ⟶ G) (hx : j ≫ x = 1) (hy : j ≫ y = 1) (hxy : j ≫ (x * y) = 1)
      (s : Γ(G.left, V)), (x * y).left.appLE V W (hW₁ _ hxy) s =
        x.left.appLE V W (hW₁ _ hx) s + y.left.appLE V W (hW₁ _ hy) s - e.left.appLE V W heW s := by
    intro x y hx hy hxy s
    have := parallelogram (fst G G).left (snd G G).left
      (fun Z u v h₁ h₂ ↦ pullback.hom_ext h₁ h₂)
      (lift x e).left (lift e y).left (lift e e).left (lift x y).left
      (by simp only [← Over.comp_left, lift_fst]) (by simp only [← Over.comp_left, lift_fst])
      (by simp only [← Over.comp_left, lift_snd]) (by simp only [← Over.comp_left, lift_snd])
      hV hV' hW hp hq (hW₂ _ _ hx he) (hW₂ _ _ he hy) hc (hW₂ _ _ hx hy)
      (fun s t ↦ hsq W hW _ _ (app_sub_eq_zero _ (near₂ _ _ hx he) _ _ _ _ _)
        (app_sub_eq_zero _ (near₂ _ _ he hy) _ _ _ _ _)) ((μ[G]).left.appLE V V' hm s)
    rwa [comp_appLE_apply _ _ (x := (x * y).left) (by rw [← Over.comp_left, ← Hom.mul_def])
        _ _ _ _ _ (hW₁ _ hxy),
      comp_appLE_apply _ _ (x := x.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.mul_one])
        _ _ _ _ _ (hW₁ _ hx),
      comp_appLE_apply _ _ (x := y.left) (by rw [← Over.comp_left, ← Hom.mul_def, _root_.one_mul])
        _ _ _ _ _ (hW₁ _ hy),
      comp_appLE_apply _ _ hcm _ _ _ _ _ heW] at this
  have hpow : ∀ k : ℕ, j ≫ (z ^ k) = 1 := fun k ↦ by rw [comp_pow, hz, one_pow]
  have ind : ∀ (k : ℕ) (s : Γ(G.left, V)), (z ^ k).left.appLE V W (hW₁ _ (hpow k)) s -
      e.left.appLE V W heW s = k * (z.left.appLE V W (hW₁ _ hz) s - e.left.appLE V W heW s) := by
    intro k s
    induction k with
    | zero =>
      rw [appLE_congr (g := e.left) (by rw [pow_zero]) _ _ _ heW]
      simp
    | succ k ih =>
      rw [appLE_congr (g := (z ^ k * z).left) (by rw [pow_succ]) _ _ _
        (hW₁ _ (by rw [← pow_succ]; exact hpow _)), add _ _ (hpow k) hz (by rw [← pow_succ]; exact hpow _)]
      push_cast
      linear_combination ih
  have hn' : IsUnit (n : Γ(T.left, W)) := by
    simpa using hn.map (T.hom.appLE ⊤ W le_top).hom
  have fin : z.left.appLE V W (hW₁ _ hz) = e.left.appLE V W heW := by
    ext s
    have := ind n s
    rw [appLE_congr (g := e.left) (by rw [hzn]) _ _ _ heW, sub_self] at this
    exact sub_eq_zero.mp (hn'.mul_right_eq_zero.mp this.symm)
  rw [← hW.isoSpec_hom_fromSpec, Category.assoc, Category.assoc,
    ← hV.SpecMap_appLE_fromSpec z.left hW (hW₁ _ hz), fin, hV.SpecMap_appLE_fromSpec e.left hW heW]
end GlobalTheory.MulUnramified
