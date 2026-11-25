-- Prove2me | solution 1 for GlobalTheory.RigSq.exists_rescale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:26:21.71333+00:00
-- url     : https://prove2.me/submissions/ca289316-bc9e-4216-a0e9-c50567798d52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleIdentityIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsRescaleRigidifiedSquareIso
import Theorems.Thm_GlobalTheory_RigSq_gm_sq_g
import Theorems.Thm_GlobalTheory_RigSq_gm_rig
import Theorems.Thm_GlobalTheory_RigSq_eSec_comp_toUnit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_unit_ext


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RigSq
namespace GlobalTheory.RigSq
theorem _root_.solution : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L L' : RigLB G)
    (w : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))), w.IsGen →
    ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)), w'.IsGen ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over S)).left) (z : Z) (jL : L.L.ι) (jL' : L'.L.ι),
      eSec G (r z) ∈ L.L.U jL → eSec G (r z) ∈ L'.L.U jL' →
      gm r z _ (L.rig.s (fun _ => jL)) ^ 2 =
        gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z _ (L'.rig.s (fun _ => jL')) ^ 2 := by
  intro S G _ L L' w hw
  have hπ := eSec_comp_toUnit G
  let W : L.L.ι × L'.L.ι → (𝟙_ (Over S)).left.Opens := fun p =>
    (L.L.pull (eSec G)).U (fun _ => p.1) ⊓ (L'.L.pull (eSec G)).U (fun _ => p.2)
  have hWle : ∀ p, W p ≤ eSec G ⁻¹ᵁ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => p.1, fun _ => p.2) :=
    fun p x hx => ⟨Set.mem_iInter.2 fun _ => mem_pull.1 hx.1, Set.mem_iInter.2 fun _ => mem_pull.1 hx.2⟩
  let q : ∀ p, Γ((𝟙_ (Over S)).left, W p)ˣ := fun p =>
    res inf_le_left (L.rig.s (fun _ => p.1)) ^ 2 * (res inf_le_right (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
      (res (hWle p) (pullU (eSec G) _ (w.s (fun _ => p.1, fun _ => p.2))))⁻¹
  have hq : ∀ {Y : Scheme.{0}} (f : Y ⟶ (𝟙_ (Over S)).left) (y : Y) (p : L.L.ι × L'.L.ι), f y ∈ W p →
      gm f y (W p) (q p) = gm f y _ (L.rig.s (fun _ => p.1)) ^ 2 * (gm f y _ (L'.rig.s (fun _ => p.2)) ^ 2)⁻¹ *
        (gv w (f ≫ eSec G) y (fun _ => p.1) (fun _ => p.2))⁻¹ := by
    intro Y f y p hy
    simp only [q, map_mul, map_pow, map_inv]
    rw [gm_res f y _ hy, gm_res f y _ hy, gm_res f y _ hy, gm_pull f (eSec G) y _ (hWle p hy)]
    rfl
  obtain ⟨u, hu⟩ := glue_unit (X := (𝟙_ (Over S)).left) ⊤ W (fun _ => le_top) (fun x _ => by
      obtain ⟨i, hi⟩ := exists_chart L.isLB (eSec G x)
      obtain ⟨i', hi'⟩ := exists_chart L'.isLB (eSec G x)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, i'), mem_pull.2 hi, mem_pull.2 hi'⟩) q (fun p p' x hx => by
      rw [hq _ x p hx.1, hq _ x p' hx.2]
      have h1 : eSec G x ∈ L.L.U p.1 := mem_pull.1 hx.1.1
      have h2 : eSec G x ∈ L'.L.U p.2 := mem_pull.1 hx.1.2
      have h1' : eSec G x ∈ L.L.U p'.1 := mem_pull.1 hx.2.1
      have h2' : eSec G x ∈ L'.L.U p'.2 := mem_pull.1 hx.2.2
      rw [gm_rig L (𝟙 _) x p.1 p'.1 h1 h1', gm_rig L' (𝟙 _) x p.2 p'.2 h2 h2',
        gm_isGen hw (𝟙 _ ≫ eSec G) x (fun _ => p.1) (fun _ => p'.1) (fun _ => p.2) (fun _ => p'.2)
          (Set.mem_iInter.2 fun _ => h1) (Set.mem_iInter.2 fun _ => h1')
          (Set.mem_iInter.2 fun _ => h2) (Set.mem_iInter.2 fun _ => h2'),
        gm_sq_g L.L (𝟙 _ ≫ eSec G) x p.1 p'.1 h1 h1', gm_sq_g L'.L (𝟙 _ ≫ eSec G) x p.2 p'.2 h2 h2']
      generalize gm (𝟙 _ ≫ eSec G) x _ (L.L.g p.1 p'.1) = A
      generalize gm (𝟙 _ ≫ eSec G) x _ (L'.L.g p.2 p'.2) = B
      generalize gm (𝟙 _) x _ (L.rig.s (fun _ => p'.1)) = C
      generalize gm (𝟙 _) x _ (L'.rig.s (fun _ => p'.2)) = D
      generalize gv w (𝟙 _ ≫ eSec G) x (fun _ => p'.1) (fun _ => p'.2) = E
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_pow]
      abel)
  have hT : ∀ p, (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U p ≤ (toUnit G).left ⁻¹ᵁ ⊤ :=
    fun _ _ _ => trivial
  obtain ⟨w', hw'⟩ : ∃ w' : LB.Iso (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)),
      ∀ p, w'.s p = w.s p * res (hT p) (pullU (toUnit G).left ⊤ u) :=
    ⟨⟨fun p => w.s p * res (hT p) (pullU (toUnit G).left ⊤ u)⟩, fun _ => rfl⟩
  refine ⟨w', ?_, ?_⟩
  · intro p p'
    rw [hw', hw']
    apply unit_ext
    intro x hx
    have e := congrArg (gm (𝟙 G.left) x _) (hw p p')
    rw [gm_res (𝟙 G.left) x _ hx, map_mul, gm_res (𝟙 G.left) x _ hx] at e
    simp only [map_mul, gm_res (𝟙 G.left) x _ hx, gm_res (𝟙 G.left) x _ hx.1, gm_res (𝟙 G.left) x _ hx.2]
    rw [e, _root_.mul_assoc]
  · intro Z r z jL jL' h1 h2
    have hy : r z ∈ W (jL, jL') := ⟨mem_pull.2 h1, mem_pull.2 h2⟩
    have hm : (r ≫ eSec G) z ∈ (LB.div (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))
      (LB.LinComb L'.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2))).U (fun _ => jL, fun _ => jL') :=
      hWle (jL, jL') hy
    have hv : gv w' (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') =
        gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') * gm r z ⊤ u := by
      show gm (r ≫ eSec G) z _ (w'.s (fun _ => jL, fun _ => jL')) = _
      erw [hw' (fun _ => jL, fun _ => jL')]
      rw [map_mul, gm_res _ z _ hm, gm_pull (r ≫ eSec G) (toUnit G).left z ⊤ trivial, Category.assoc, hπ,
        Category.comp_id]
      rfl
    rw [hv, ← gm_res r z (le_top : W (jL, jL') ≤ ⊤) hy u, hu (jL, jL'), hq r z (jL, jL') hy]
    generalize gm r z _ (L.rig.s (fun _ => jL)) = A
    generalize gm r z _ (L'.rig.s (fun _ => jL')) = B
    generalize gv w (r ≫ eSec G) z (fun _ => jL) (fun _ => jL') = E
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel
end GlobalTheory.RigSq
