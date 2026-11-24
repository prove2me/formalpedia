-- Prove2me | solution 1 for GlobalTheory.PushInv.exists_secOn_pull_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:41:29.394085+00:00
-- url     : https://prove2.me/submissions/3b15fa5e-6398-422a-9701-a41960ea3fe9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsProperRestrictPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PushInvertibleOfDensePart
import Theorems.Thm_GlobalTheory_AbLocusPull_glue_fn
import Theorems.Thm_GlobalTheory_AbLocusPull_gs_secOn
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_iff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.PushInv
open GlobalTheory.AbLocusPull
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.PushInv
theorem _root_.solution {X' : Scheme.{0}} {F : X' ⟶ X} {L : LB X} {L' : LB X'} (hL : L.IsLB) (hL' : L'.IsLB)
    (w : LB.Iso L' (L.pull F)) (hw : w.IsGen) {W : X.Opens} {W' : X'.Opens} (hW : W' ≤ F ⁻¹ᵁ W)
    {θ : ∀ i, Γ(X, W ⊓ L.U i)} (hθ : θ ∈ secOn L W) :
    ∃ θ' ∈ secOn L' W', ∀ k x j, x ∈ W' → x ∈ L'.U k → F x ∈ L.U j →
      gs (𝟙 X') x _ (θ' k) = ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) := by
  have hw := (isGen_iff w).1 hw
  have rel : ∀ (x : X') j j' k k', x ∈ W' → F x ∈ L.U j → F x ∈ L.U j' → x ∈ L'.U k → x ∈ L'.U k' →
      ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) =
        (gm (𝟙 X') x (L'.U k ⊓ L'.U k') (L'.g k k')).val * (((gw w (𝟙 X') x j' k')⁻¹).val * gs F x _ (θ j')) := by
    intro x j j' k k' hx hj hj' hk hk'
    have e := hw _ (𝟙 X') x j j' k k' hj hj' hk hk'
    rw [Category.id_comp] at e
    rw [gs_secOn hθ F x j j' (hW hx) hj hj', e, ← _root_.mul_assoc, ← _root_.mul_assoc, ← Units.val_mul, ← Units.val_mul]
    congr 2
    rw [mul_inv, mul_inv, inv_inv, _root_.mul_comm, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_inv_cancel, _root_.one_mul]
  have ex : ∀ k, ∃ b : Γ(X', W' ⊓ L'.U k), ∀ x j, x ∈ W' → x ∈ L'.U k → F x ∈ L.U j →
      gs (𝟙 X') x _ b = ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) := by
    intro k
    let O : L.ι → X'.Opens := fun j => W' ⊓ ((L.pull F).U (fun _ => j) ⊓ L'.U k)
    have le : ∀ j, O j ≤ F ⁻¹ᵁ (W ⊓ L.U j) := fun j x hx => ⟨hW hx.1, mem_pull.1 hx.2.1⟩
    let u : ∀ j, Γ(X', (L.pull F).U (fun _ => j) ⊓ L'.U k)ˣ := fun j => w.s (fun _ => j, k)
    let a : ∀ j, Γ(X', O j) := fun j => resG X' inf_le_right ((u j)⁻¹).val * resG X' (le j) ((F.app _).hom (θ j))
    have va : ∀ x j, x ∈ O j → gs (𝟙 X') x _ (a j) = ((gw w (𝟙 X') x j k)⁻¹).val * gs F x _ (θ j) := by
      intro x j hx
      refine (gs_mul _ x _ hx _ _).trans ?_
      rw [gs_res _ x _ hx, gs_res _ x _ hx, gs_unit _ x _ hx.2, map_inv, gs_pull _ F x _ (le j hx), Category.id_comp]
      rfl
    obtain ⟨b, hb⟩ := glue_fn (W' ⊓ L'.U k) O (fun j x hx => ⟨hx.1, hx.2.2⟩)
      (fun x hx => (exists_chart hL (F x)).imp fun j hj => ⟨hx.1, mem_pull.2 hj, hx.2⟩) a (fun j j' x hj hj' => by
        rw [va x j hj, va x j' hj', rel x j j' k k hj.1 (mem_pull.1 hj.2.1) (mem_pull.1 hj'.2.1) hj.2.2 hj.2.2,
          gm_self hL' (𝟙 X') x hj.2.2, Units.val_one, _root_.one_mul])
    refine ⟨b, fun x j hx hk hj => ?_⟩
    have hm : x ∈ O j := ⟨hx, mem_pull.2 hj, hk⟩
    exact (hb x j hm).trans (va x j hm)
  choose θ' hθ' using ex
  refine ⟨θ', fun k k' => fn_ext fun x hx => ?_, hθ'⟩
  obtain ⟨j, hj⟩ := exists_chart hL (F x)
  rw [gs_res _ x _ hx, gs_mul _ x _ hx, gs_res _ x _ hx, gs_res _ x _ hx,
    gs_unit (𝟙 X') x (L'.U k ⊓ L'.U k') ⟨hx.1.2, hx.2⟩, hθ' k x j hx.1.1 hx.1.2 hj, hθ' k' x j hx.1.1 hx.2 hj]
  exact rel x j j k k' hx.1.1 hj hj hx.1.2 hx.2
end GlobalTheory.PushInv
