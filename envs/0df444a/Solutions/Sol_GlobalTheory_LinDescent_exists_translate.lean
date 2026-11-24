-- Prove2me | solution 1 for GlobalTheory.LinDescent.exists_translate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:45:13.079389+00:00
-- url     : https://prove2.me/submissions/b71bdb14-2f32-410b-a61b-441daa704fc7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_gs_appLE
import Theorems.Thm_GlobalTheory_LinDescent_glue_sec
import Theorems.Thm_GlobalTheory_LinDescent_mem_twist
import Theorems.Thm_GlobalTheory_LinDescent_uv_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_TLinPf_exists_chart


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X}
namespace GlobalTheory.LinDescent
theorem _root_.solution (hL : L.IsLB) {t : X ⟶ X} {u : LB.Gen (twist L t)} (hu : u.IsGen)
    {W : X.Opens} (hW : W ≤ t ⁻¹ᵁ W) {m : ∀ i, Γ(X, W ⊓ L.U i)} (hm : IsLocSec L W m) :
    ∃ m' : ∀ i, Γ(X, W ⊓ L.U i), IsLocSec L W m' ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) i j, r z ∈ W → r z ∈ L.U i → (r ≫ t) z ∈ L.U j →
        gs r z _ (m' i) = (uv u r z i j).val * gs (r ≫ t) z _ (m j) := by
  let O : L.ι × L.ι → X.Opens := fun p => W ⊓ LB.wchart L (K := Fin 2) ![𝟙 X, t] ![p.1, p.2]
  have hle : ∀ p, O p ≤ t ⁻¹ᵁ (W ⊓ L.U p.2) := fun p x hx => ⟨hW hx.1, (mem_twist.1 hx.2).2⟩
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) p, r z ∈ O p →
      gs r z (O p) (rs inf_le_right (u.s ![p.1, p.2]).val * (t.appLE _ _ (hle p)).hom (m p.2)) =
        (uv u r z p.1 p.2).val * gs (r ≫ t) z _ (m p.2) := fun Z r z p hz =>
    (gs_mul r z _ hz _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z _ hz _).trans (gs_unit r z _ hz.2 _)) (gs_appLE r t z _ _ _ hz _))
  obtain ⟨m', h1, h2⟩ := glue_sec hL W O Prod.fst (fun _ => inf_le_left)
    (fun p x hx => (mem_twist.1 hx.2).1) (fun x hx => by
      obtain ⟨i, hi⟩ := exists_chart hL x
      obtain ⟨j, hj⟩ := exists_chart hL (t x)
      exact ⟨(i, j), hx, mem_twist.2 ⟨hi, hj⟩⟩)
    (fun p => rs inf_le_right (u.s ![p.1, p.2]).val * (t.appLE _ _ (hle p)).hom (m p.2))
    (fun p q x hp hq => by
      have hp' := mem_twist.1 hp.2
      have hq' := mem_twist.1 hq.2
      rw [v _ (𝟙 X) x p hp, v _ (𝟙 X) x q hq, uv_trans hu (𝟙 X) x hp'.1 hp'.2 hq'.1 hq'.2,
        hm _ (𝟙 X ≫ t) x p.2 q.2 (hW hp.1) hp'.2 hq'.2, ← mul_assoc, ← mul_assoc,
        ← Units.val_mul, ← Units.val_mul, mul_right_comm, inv_mul_cancel_right])
  refine ⟨m', h1, fun Z r z i j hz hi hj => ?_⟩
  have hp : r z ∈ O (i, j) := ⟨hz, mem_twist.2 ⟨hi, hj⟩⟩
  rw [h2 Z r z i (i, j) hi hp, v Z r z _ hp, gg, gm_self hL r z hi, Units.val_one, one_mul]
end GlobalTheory.LinDescent
