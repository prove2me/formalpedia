-- Prove2me | solution 1 for GlobalTheory.existsUnique_secOn_of_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:15:30.415109+00:00
-- url     : https://prove2.me/submissions/d46147cc-ffa2-486f-b4d3-9ec82062cade

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Theorems.Thm_P2M_GlobalTheory_bijective___appLE_4ffb2aed58ba
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open GlobalTheory
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution (L : LB X) (W : X.Opens) (r : (L.pull W.ι).Sec) :
    ∃! s : ∀ i, Γ(X, W ⊓ L.U i), s ∈ secOn L W ∧ ∀ j : PUnit.{1} → L.ι,
      (W.ι.appLE (W ⊓ L.U (j PUnit.unit)) _ (lb_pull_ι_U L W j).le).hom (s (j PUnit.unit)) =
        r.f j := by
  have hb (j : PUnit.{1} → L.ι) := bijective_ι_appLE W inf_le_left (lb_pull_ι_U L W j)
  choose s hs using fun i : L.ι ↦ (hb fun _ ↦ i).2 (r.f fun _ ↦ i)
  refine ⟨s, ⟨fun i j ↦ ?_, fun j ↦ hs (j PUnit.unit)⟩,
    fun t ht ↦ funext fun i ↦ (hb fun _ ↦ i).1 ((ht.2 fun _ ↦ i).trans (hs i).symm)⟩
  apply (bijective_ι_appLE W (V := W ⊓ L.U i ⊓ L.U j) (inf_le_left.trans inf_le_left)
    (T := (L.pull W.ι).U (fun _ ↦ i) ⊓ (L.pull W.ι).U (fun _ ↦ j))
    (congrArg₂ (· ⊓ ·) (lb_pull_ι_U L W fun _ ↦ i) (lb_pull_U L W.ι fun _ ↦ j))).1
  have := r.compat (fun _ ↦ i) (fun _ ↦ j)
  rw [← hs, ← hs, lb_pull_g L W.ι (fun _ ↦ i) (fun _ ↦ j)] at this
  erw [res_appLE_apply, res_appLE_apply] at this
  rw [map_mul]
  erw [appLE_res_apply, appLE_res_apply, appLE_res_apply]
  exact this
end GlobalTheory
