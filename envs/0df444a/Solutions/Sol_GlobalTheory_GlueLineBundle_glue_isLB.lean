-- Prove2me | solution 1 for GlobalTheory.GlueLineBundle.glue_isLB
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:12:43.581935+00:00
-- url     : https://prove2.me/submissions/eab7672c-ca96-4093-96c3-4738d225b26a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
import Theorems.Thm_GlobalTheory_GlueLineBundle_unit_ext_imm
import Theorems.Thm_P2M_GlobalTheory_GlueLineBundle_gm_glue_g__18e2be52006f
import Theorems.Thm_GlobalTheory_GlueLineBundle_eq_of_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_cocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)
variable {V M}
namespace GlobalTheory.GlueLineBundle
theorem _root_.solution (hdisj : ∀ a b x, x ∈ V a → x ∈ V b → a = b) (hcov : ∀ x, ∃ a, x ∈ V a)
    (hM : ∀ a, (M a).IsLB) : (glue V M).IsLB where
  cover := top_le_iff.1 fun x _ => by
    obtain ⟨a, ha⟩ := hcov x
    obtain ⟨w, rfl⟩ : ∃ w : (V a).toScheme, (V a).ι w = x := ⟨⟨x, ha⟩, rfl⟩
    obtain ⟨i, hi⟩ := exists_chart (hM a) w
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨a, i⟩, (V a).ι.apply_mem_image_iff.2 hi⟩
  g_self p := by
    obtain ⟨a, i⟩ := p
    apply unit_ext_imm
    intro x hx
    have hx2 : x ∈ (V a).ι ''ᵁ (M a).U i := hx
    obtain ⟨w, hw, rfl⟩ := hx2
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ := hx
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [gm_res (V a).ι w _ hx', map_one, gm_glue_g' V M a w i i hw hw]
    exact gm_self (hM a) (𝟙 _) w hw
  cocycle p q r := by
    obtain ⟨a, i⟩ := p
    obtain ⟨b, k⟩ := q
    obtain ⟨c, l⟩ := r
    apply unit_ext_imm
    intro x hx
    have h1 : x ∈ (V a).ι ''ᵁ (M a).U i := hx.1.1
    obtain ⟨w, hw, rfl⟩ := h1
    have h2 : (V a).ι w ∈ NU V M ⟨b, k⟩ := hx.1.2
    have h3 : (V a).ι w ∈ NU V M ⟨c, l⟩ := hx.2
    have hb := eq_of_mem hdisj w h2
    have hc := eq_of_mem hdisj w h3
    subst hb hc
    have hx' : (V a).ι w ∈ (glue V M).U ⟨a, i⟩ ⊓ (glue V M).U ⟨a, k⟩ ⊓ (glue V M).U ⟨a, l⟩ := hx
    have hk := (V a).ι.apply_mem_image_iff.1 h2
    have hl := (V a).ι.apply_mem_image_iff.1 h3
    refine ⟨_, (V a).ι, inferInstance, w, rfl, ?_⟩
    rw [map_mul, gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_res (V a).ι w _ hx', gm_glue_g' V M a w i k hw hk,
      gm_glue_g' V M a w k l hk hl, gm_glue_g' V M a w i l hw hl]
    exact gm_cocycle (hM a) (𝟙 _) w hw hk hl
end GlobalTheory.GlueLineBundle
