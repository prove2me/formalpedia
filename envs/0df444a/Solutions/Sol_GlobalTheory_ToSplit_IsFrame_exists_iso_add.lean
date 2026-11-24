-- Prove2me | solution 1 for GlobalTheory.ToSplit.IsFrame.exists_iso_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:48:24.631811+00:00
-- url     : https://prove2.me/submissions/299cc544-92ff-40c2-ae23-b9ace4ce7189

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtDatumOfSplitTorusExtension
import Theorems.Thm_GlobalTheory_ToSplit_gm_res_pre
import Theorems.Thm_GlobalTheory_ToSplit_exists_gen_descent
import Theorems.Thm_GlobalTheory_ToSplit_exists_act
import Theorems.Thm_GlobalTheory_ToSplit_aux_add
import Theorems.Thm_GlobalTheory_ToSplit_commGroup_weight_cancel_identity
import Theorems.Thm_GlobalTheory_ToSplit_IsFrame_trans_id
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_div


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ToSplit
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]
  {q : G ⟶ B} {i : splitTorus S X ⟶ G} [IsMonHom q] [IsMonHom i]
  [Flat q.left] [Surjective q.left] [QuasiCompact q.left]
  (hk : IsPullback i (toUnit _) q (η[B]))
include hk
omit [IsMonHom i]
namespace GlobalTheory.ToSplit
namespace IsFrame
theorem _root_.solution {χ χ' : X} {O O' O'' : RigLB B}
    {u : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O.L.U j)ˣ} {u' : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O'.L.U j)ˣ}
    {u'' : ∀ j, Γ(G.left, q.left ⁻¹ᵁ O''.L.U j)ˣ} (h : IsFrame q i χ O u)
    (h' : IsFrame q i χ' O' u') (h'' : IsFrame q i (χ + χ') O'' u'') :
    ∃ t : LB.Iso O'.L (LB.div O''.L O.L), t.IsGen := by
  let M : LB B.left := LB.div (LB.div O''.L O.L) O'.L
  let f : ∀ p : (O''.L.ι × O.L.ι) × O'.L.ι,
      Γ(G.left, q.left ⁻¹ᵁ (O''.L.U p.1.1 ⊓ O.L.U p.1.2 ⊓ O'.L.U p.2))ˣ := fun p =>
    (res (q.left.preimage_mono (inf_le_left.trans inf_le_left)) (u'' p.1.1))⁻¹ *
      res (q.left.preimage_mono (inf_le_left.trans inf_le_right)) (u p.1.2) *
      res (q.left.preimage_mono inf_le_right) (u' p.2)
  have hf : ∀ (p : (O''.L.ι × O.L.ι) × O'.L.ι) (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z),
      q.left (r z) ∈ O''.L.U p.1.1 ⊓ O.L.U p.1.2 ⊓ O'.L.U p.2 →
      gm r z _ (f p) = (gm r z _ (u'' p.1.1))⁻¹ * gm r z _ (u p.1.2) * gm r z _ (u' p.2) :=
    fun p Z r z hz => by
      rw [map_mul, map_mul, map_inv, gm_res_pre _ _ _ _ hz, gm_res_pre _ _ _ _ hz,
        gm_res_pre _ _ _ _ hz]
  refine exists_gen_descent q M f (fun p Z g₁ g₂ z e h₁ h₂ => ?_) (fun p p' y h₁ h₂ => ?_)
  · obtain ⟨t, rfl⟩ := exists_act hk e
    refine (hf p _ _ z h₁).trans (Eq.trans ?_ (hf p _ _ z h₂).symm)
    rw [h.1 _ Z t g₂ z h₂.1.2, h'.1 _ Z t g₂ z h₂.2, h''.1 _ Z t g₂ z h₂.1.1, ofAdd_add, map_mul]
    exact commGroup_weight_cancel_identity _ _ _ _ _
  · refine (hf p _ (𝟙 _) y h₁).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      ((gm_div O'.L (LB.div O''.L O.L) q.left y p p' ⟨h₁, h₂⟩).trans (congrArg₂ (· * ·)
        ((gm_div O.L O''.L q.left y p.1 p'.1 ⟨h₁.1, h₂.1⟩).trans (congrArg₂ (· * ·⁻¹)
          (h''.trans_id _ _ y h₁.1.1 h₂.1.1) (h.trans_id _ _ y h₁.1.2 h₂.1.2)))
        (congrArg (·⁻¹) (h'.trans_id _ _ y h₁.2 h₂.2))))
      (hf p' _ (𝟙 _) y h₂)).symm)
    exact aux_add _ _ _ _ _ _
end IsFrame
end GlobalTheory.ToSplit
