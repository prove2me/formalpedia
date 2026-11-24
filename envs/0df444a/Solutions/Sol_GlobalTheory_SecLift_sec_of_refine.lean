-- Prove2me | solution 1 for GlobalTheory.SecLift.sec_of_refine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:37:21.508496+00:00
-- url     : https://prove2.me/submissions/6bf24582-8c31-4711-9160-e9051faa3c78

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_cocycle
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_ext
import Theorems.Thm_GlobalTheory_SmallExtLift_gr_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_glue


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]
namespace GlobalTheory.SecLift
theorem _root_.solution {M : LB X} (hM : M.IsLB) {I : Type} (V : I → X.Opens)
    (cov : ∀ x : X, ∃ a, x ∈ V a)
    (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a)) (w : ∀ a, Γ(X, V a))
    (H : ∀ a b x (ha : (𝟙 X : X ⟶ X) x ∈ V a) (hb : (𝟙 X : X ⟶ X) x ∈ V b),
      gr (𝟙 X) x _ ha (w a) = gr (𝟙 X) x (M.U (j a) ⊓ M.U (j b)) ⟨hj a ha, hj b hb⟩
        (M.g (j a) (j b)).val * gr (𝟙 X) x _ hb (w b)) :
    ∃ s : LB.Sec M, ∀ i a (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (hi : r z ∈ M.U i) (ha : r z ∈ V a),
      gr r z _ hi (s.f i) =
        gr r z (M.U i ⊓ M.U (j a)) ⟨hi, hj a ha⟩ (M.g i (j a)).val * gr r z _ ha (w a) := by
  have glue : ∀ i : M.ι, ∃ s : Γ(X, M.U i), ∀ a (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z)
      (hi : r z ∈ M.U i) (ha : r z ∈ V a), gr r z _ hi s =
        gr r z (M.U i ⊓ M.U (j a)) ⟨hi, hj a ha⟩ (M.g i (j a)).val * gr r z _ ha (w a) := by
    intro i
    let u : ∀ a, Γ(X, M.U i ⊓ V a) := fun a =>
      (X.presheaf.map (homOfLE (inf_le_inf_left _ (hj a))).op).hom (M.g i (j a)).val *
        (X.presheaf.map (homOfLE inf_le_right).op).hom (w a)
    have hu : ∀ a (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (h : r z ∈ M.U i ⊓ V a), gr r z _ h (u a) =
        gr r z (M.U i ⊓ M.U (j a)) ⟨h.1, hj a h.2⟩ (M.g i (j a)).val *
          gr r z _ h.2 (w a) := fun a Z r x h =>
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gr_res _ x _ h _) (gr_res _ x _ h _))
    obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun a => M.U i ⊓ V a) (M.U i)
      (fun a => homOfLE inf_le_left) (fun x hx => by
        obtain ⟨a, ha⟩ := cov x
        exact Opens.mem_iSup.2 ⟨a, hx, ha⟩) u
      (fun a b => gr_ext (V := (M.U i ⊓ V a) ⊓ (M.U i ⊓ V b)) fun x hx => by
        refine (gr_res _ x inf_le_left hx _).trans
          (Eq.trans ?_ (gr_res _ x inf_le_right hx _).symm)
        refine (hu a _ _ x hx.1).trans (Eq.trans ?_ (hu b _ _ x hx.2).symm)
        rw [H a b x hx.1.2 hx.2.2, ← _root_.mul_assoc,
          gr_cocycle hM _ x hx.1.1 (hj a hx.1.2) (hj b hx.2.2)])
    refine ⟨s, fun a Z r x hi ha => ?_⟩
    have hm : r x ∈ M.U i ⊓ V a := ⟨hi, ha⟩
    exact (gr_res _ x inf_le_left hm s).symm.trans
      ((congrArg (gr _ x _ hm) (hs a)).trans (hu a _ r x hm))
  choose s hs using glue
  refine ⟨⟨s, fun i k => gr_ext fun x hx => ?_⟩, hs⟩
  obtain ⟨a, ha⟩ := cov x
  refine (gr_res _ x inf_le_left hx (s i)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gr_res _ x inf_le_right hx (s k)))).symm)
  rw [hs i a _ _ x hx.1 ha, hs k a _ _ x hx.2 ha, ← _root_.mul_assoc,
    ← gr_cocycle hM _ x hx.1 hx.2 (hj a ha)]
end GlobalTheory.SecLift
