-- Prove2me | solution 1 for GlobalTheory.PartialCocycle.gm_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:50:59.911869+00:00
-- url     : https://prove2.me/submissions/9dfded21-311d-44af-a1ca-3fc1f1a791e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

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
namespace GlobalTheory.PartialCocycle
private theorem gm_res_eq_gm {X Z : Scheme.{0}} (f : Z ⟶ X) (z : Z) {U V : X.Opens} (hle : V ≤ U)
    (hz : f z ∈ V) (u : Γ(X, U)ˣ) : gm f z V (res hle u) = gm f z U u := by
  have key : X.presheaf.map (homOfLE hle).op ≫ f.app V ≫ Z.presheaf.germ (f ⁻¹ᵁ V) z hz =
      f.app U ≫ Z.presheaf.germ (f ⁻¹ᵁ U) z (hle hz) := by
    rw [← Scheme.Hom.germ_stalkMap, ← Scheme.Hom.germ_stalkMap, ← Category.assoc, TopCat.Presheaf.germ_res]
  unfold gm
  rw [dif_pos hz, dif_pos (hle hz)]
  ext
  simp only [MonoidHom.comp_apply, Units.coe_map]
  unfold res pullU
  have h2 := congrArg (fun g => g.hom (u : Γ(X, U))) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  exact h2
end GlobalTheory.PartialCocycle
end
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
noncomputable section
open GlobalTheory GlobalTheory.PartialCocycle
namespace GlobalTheory.PartialCocycle
theorem _root_.solution {X Z : Scheme.{0}} {L M : LB X} {w : LB.Iso L M} (hw : w.IsGen) (f : Z ⟶ X) (z : Z)
    (a a' : M.ι) (b b' : L.ι) (ha : f z ∈ M.U a) (ha' : f z ∈ M.U a') (hb : f z ∈ L.U b) (hb' : f z ∈ L.U b') :
    gm f z (M.U a ⊓ L.U b) (w.s (a, b)) =
      gm f z (M.U a ⊓ M.U a') (M.g a a') * (gm f z (L.U b ⊓ L.U b') (L.g b b'))⁻¹ *
        gm f z (M.U a' ⊓ L.U b') (w.s (a', b')) := by
  have hz : f z ∈ (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') := ⟨⟨ha, hb⟩, ⟨ha', hb'⟩⟩
  have h₁ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ L.U b := inf_le_left
  have h₂ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a ⊓ M.U a' :=
    le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left)
  have h₃ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ L.U b ⊓ L.U b' :=
    le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right)
  have h₄ : (M.U a ⊓ L.U b) ⊓ (M.U a' ⊓ L.U b') ≤ M.U a' ⊓ L.U b' := inf_le_right
  have h1 := hw (a, b) (a', b')
  calc gm f z (M.U a ⊓ L.U b) (w.s (a, b))
      = gm f z _ (res h₁ (w.s (a, b))) := (gm_res_eq_gm f z h₁ hz _).symm
    _ = gm f z _ (res h₂ (M.g a a') * (res h₃ (L.g b b'))⁻¹ * res h₄ (w.s (a', b'))) := congrArg _ h1
    _ = _ := by
      rw [map_mul, map_mul, map_inv, gm_res_eq_gm f z h₂ hz, gm_res_eq_gm f z h₃ hz]
      exact congrArg _ (gm_res_eq_gm f z h₄ hz _)
end GlobalTheory.PartialCocycle
