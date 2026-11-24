-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.glue_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:01.695857+00:00
-- url     : https://prove2.me/submissions/2b000a02-ac31-4959-bf36-586e3012e808

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_ext_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_inj
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution {Y : Scheme.{0}} {ι' : Type} (W : ι' → Y.Opens) (hW : ∀ y, ∃ s, y ∈ W s)
    (c : ∀ s, Γ((W s).toScheme, ⊤)ˣ)
    (agree : ∀ s s' (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (r' : Z ⟶ (W s').toScheme) (z : Z),
      r ≫ (W s).ι = r' ≫ (W s').ι → gm r z ⊤ (c s) = gm r' z ⊤ (c s')) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ s (Z : Scheme.{0}) (r : Z ⟶ (W s).toScheme) (z : Z),
      gm (r ≫ (W s).ι) z ⊤ a = gm r z ⊤ (c s) := by
  choose b hb using fun s => exists_ext_unit (W s).ι ⊤ (c s)
  obtain ⟨a, ha⟩ := glue_unit (⊤ : Y.Opens) _ (fun s => le_top) (fun y _ => by
      obtain ⟨s, hs⟩ := hW y
      exact Opens.mem_iSup.2 ⟨s, ⟨y, hs⟩, trivial, rfl⟩) b (fun s s' y hy => by
      obtain ⟨⟨y₁, h₁, e₁⟩, ⟨y₂, h₂, e₂⟩⟩ := hy
      have hy₁ : y ∈ W s := e₁ ▸ y₁.2
      have hy₂ : y ∈ W s' := e₂ ▸ y₂.2
      let z : (W s ⊓ W s').toScheme := ⟨y, hy₁, hy₂⟩
      let r := Y.homOfLE (inf_le_left : W s ⊓ W s' ≤ W s)
      let r' := Y.homOfLE (inf_le_right : W s ⊓ W s' ≤ W s')
      have f₁ : r ≫ (W s).ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
      have f₂ : r' ≫ (W s').ι = (W s ⊓ W s').ι := Y.homOfLE_ι _
      have b₁ := hb s _ r z trivial
      have b₂ := hb s' _ r' z trivial
      rw [f₁] at b₁
      rw [f₂] at b₂
      have n₁ : (W s ⊓ W s').ι z ∈ (W s).ι ''ᵁ ⊤ := ⟨y₁, h₁, e₁⟩
      have n₂ : (W s ⊓ W s').ι z ∈ (W s').ι ''ᵁ ⊤ := ⟨y₂, h₂, e₂⟩
      exact gm_inj (W s ⊓ W s').ι z n₁ n₂ (b₁.trans ((agree s s' _ r r' z (f₁.trans f₂.symm)).trans b₂.symm)))
  refine ⟨a, fun s Z r z => ?_⟩
  have hm : (r ≫ (W s).ι) z ∈ (W s).ι ''ᵁ ⊤ := ⟨r z, trivial, rfl⟩
  exact (gm_res _ z le_top hm a).symm.trans ((congrArg (gm _ z _) (ha s)).trans (hb s Z r z trivial))
end GlobalTheory.CommutatorPairing
