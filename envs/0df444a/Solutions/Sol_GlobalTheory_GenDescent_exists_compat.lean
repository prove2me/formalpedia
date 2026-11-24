-- Prove2me | solution 1 for GlobalTheory.GenDescent.exists_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:58:54.963794+00:00
-- url     : https://prove2.me/submissions/60134506-981a-4b12-837a-83c4ef869c83

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsActionOfIsPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsGenOfQuotientOfRigid
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_rp__e27165827f88
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_Geo_Tor_pullU_res__268497da66fb
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_id_pull

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace GenDescent
variable {Y Y' Z : Scheme.{0}}
private theorem gm_res' {X W : Scheme.{0}} (k : W ⟶ X) (w : W) {V V' : X.Opens} (h : V' ≤ V)
    (u : Γ(X, V)ˣ) (hw : k w ∈ V') : gm k w V' (res h u) = gm k w V u := by
  rw [← gm_id_pull k w V' hw (res h u), pullU_res₂, gm_rp₁ k w V _ _ hw]
end GenDescent
end GlobalTheory
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.GenDescent
variable {Y Y' Z : Scheme.{0}}
namespace GlobalTheory.GenDescent
theorem _root_.solution {N : LB Z} {f : Y ⟶ Z} (t : (N.pull f).Gen) (ht : t.IsGen) :
    ∃ a, Compat N f a := by
  unfold LB.Gen.IsGen at ht
  have hle : ∀ i : N.ι, f ⁻¹ᵁ N.U i ≤ (N.pull f).U (fun _ => i) := fun i x hx =>
    Set.mem_iInter.2 fun _ => hx
  refine ⟨fun i => res (hle i) (t.s fun _ => i), fun W k w i j hi hj => ?_⟩
  have hwi : k w ∈ f ⁻¹ᵁ N.U i := hi
  have hwj : k w ∈ f ⁻¹ᵁ N.U j := hj
  have hO : k w ∈ (N.pull f).U (fun _ => i) ⊓ (N.pull f).U (fun _ => j) := ⟨hle i hwi, hle j hwj⟩
  have e := congrArg (gm k w _) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, gm_res' _ _ _ _ hO, gm_res' _ _ _ _ hO] at e
  rw [gm_res' _ _ _ _ hwi, gm_res' _ _ _ _ hwj, e]
  congr 1
  have hOle : (N.pull f).U (fun _ => i) ⊓ (N.pull f).U (fun _ => j) ≤ f ⁻¹ᵁ (N.U i ⊓ N.U j) :=
    fun x hx => ⟨Set.mem_iInter.1 hx.1 PUnit.unit, Set.mem_iInter.1 hx.2 PUnit.unit⟩
  have hg : (N.pull f).g (fun _ => i) (fun _ => j) = res hOle (pullU f _ (N.g i j)) :=
    (Fintype.prod_unique (fun _ : PUnit => res hOle (pullU f _ (N.g i j)) ^ (1 : ℤ))).trans (zpow_one _)
  rw [hg, gm_res' _ _ _ _ hO, gm_pullU_eq_gm_comp]
end GlobalTheory.GenDescent
