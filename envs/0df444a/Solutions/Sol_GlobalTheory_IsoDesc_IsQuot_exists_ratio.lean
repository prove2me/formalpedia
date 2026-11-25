-- Prove2me | solution 1 for GlobalTheory.IsoDesc.IsQuot.exists_ratio
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:39.365045+00:00
-- url     : https://prove2.me/submissions/d9a4197d-2d34-4171-86e7-07eec59c283d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsCPMapDescends
import Theorems.Thm_GlobalTheory_IsoDesc_IsQuot_trans
import Theorems.Thm_GlobalTheory_UU_TorusCompat_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.IsoDesc
variable {X Y Z : Scheme.{0}}
variable {G B' B : Scheme.{0}} {L : LB G} {M' : LB B'} {M : LB B} {q : G ⟶ B'} {β : B' ⟶ B}
namespace GlobalTheory.IsoDesc
namespace IsQuot
theorem _root_.solution (hL : L.IsLB) (hM' : M'.IsLB) (hM : M.IsLB) {u : LB.Iso L (M'.pull q)}
    {w : LB.Iso L (M.pull (q ≫ β))} (hu : PGen u) (hw : PGen w) {s} (hs : IsQuot u w s)
    (m p : Y ⟶ G) (e : m ≫ q = p ≫ q) : ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : M.ι) (i : M'.ι),
      q (p (r z)) ∈ dom M' M β j i → gm (r ≫ m) z _ (s j i) = gm r z ⊤ a * gm (r ≫ p) z _ (s j i) := by
  have ept : ∀ y, q (m y) = q (p y) := fun y => congrArg (fun g => g y) e
  let W : M.ι × M'.ι → Y.Opens := fun c => p ⁻¹ᵁ q ⁻¹ᵁ dom M' M β c.1 c.2
  have l : ∀ c, W c ≤ m ⁻¹ᵁ q ⁻¹ᵁ dom M' M β c.1 c.2 := fun c y hy => by
    show q (m y) ∈ dom M' M β c.1 c.2
    rw [ept]; exact hy
  obtain ⟨b, hb⟩ : ∃ b : ∀ c, Γ(Y, W c)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) c, r z ∈ W c →
      gm r z (W c) (b c) = gm (r ≫ m) z _ (s c.1 c.2) * (gm (r ≫ p) z _ (s c.1 c.2))⁻¹ :=
    ⟨fun c => res (l c) (pullU m _ (s c.1 c.2)) * (pullU p _ (s c.1 c.2))⁻¹, fun Z r z c hz =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res r z (l c) hz _).trans (gm_pull r m z _ (l c hz) _))
        ((map_inv _ _).trans (congrArg (·⁻¹) (gm_pull r p z _ hz _))))⟩
  obtain ⟨a, ha⟩ := glue_unit ⊤ W (fun _ => le_top) (fun y _ => by
      obtain ⟨j, hj⟩ := exists_chart hM (β (q (p y)))
      obtain ⟨i, hi⟩ := exists_chart hM' (q (p y))
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨(j, i), mem_pull.2 hj, hi⟩) b (fun c c' y hy => by
      rw [hb _ (𝟙 Y) y c hy.1, hb _ (𝟙 Y) y c' hy.2,
        hs.trans hL hu hw (𝟙 Y ≫ m) y c.1 c'.1 c.2 c'.2 (mem_pull.1 (l c hy.1).1) (mem_pull.1 (l c' hy.2).1)
          (l c hy.1).2 (l c' hy.2).2,
        hs.trans hL hu hw (𝟙 Y ≫ p) y c.1 c'.1 c.2 c'.2 (mem_pull.1 hy.1.1) (mem_pull.1 hy.2.1) hy.1.2 hy.2.2,
        Category.id_comp, Category.id_comp, e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
  refine ⟨a, fun Z r z j i hz => ?_⟩
  have := (gm_res r z le_top (show r z ∈ W (j, i) from hz) a).symm.trans
    ((congrArg (gm r z (W (j, i))) (ha (j, i))).trans (hb Z r z (j, i) hz))
  rw [this, inv_mul_cancel_right]
end IsQuot
end GlobalTheory.IsoDesc
