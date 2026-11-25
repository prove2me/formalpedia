-- Prove2me | solution 1 for GlobalTheory.SqLB.exists_sq_up
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:16:41.398017+00:00
-- url     : https://prove2.me/submissions/91088192-6439-4ff1-acd3-357683a87bb0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSquareGeneratorThroughSquareIso
import Theorems.Thm_GlobalTheory_SqLB_trF_two
import Theorems.Thm_GlobalTheory_SqLB_pq_trans
import Theorems.Thm_GlobalTheory_SqLB_exists_pq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_chart
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_glue_unit
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGen_of_gm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_trF_self


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SqLB
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
namespace GlobalTheory.SqLB
theorem _root_.solution {w : LB.Iso (sq L') ((sq L).pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) :
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) (fun k => 2 * ε k)), t.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι), r z ∈ LB.wchart L (fun k => φ' k ≫ F) p →
        r z ∈ LB.wchart L' φ' q → gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
  choose u hu using fun p q => exists_pq w φ' ε p q
  have glue : ∀ p : K → L.ι, ∃ s : Γ(Y, LB.wchart L (fun k => φ' k ≫ F) p)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 := by
    intro p
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) q, r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ (u p q * res inf_le_right (a.s q) ^ 2) =
          pq w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) ^ 2 :=
      fun Z r z q hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) (hu p q Z r z hz)
        ((map_pow _ _ _).trans (congrArg (· ^ 2) (gm_res r z _ hz _))))
    obtain ⟨s, hs⟩ := glue_unit _ (fun q => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q) (fun _ => inf_le_left)
      (fun y hy => by
        choose q hq using fun k => exists_chart hL' (φ' k y)
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨q, hy, Set.mem_iInter.2 hq⟩) (fun q => u p q * res inf_le_right (a.s q) ^ 2)
      (fun q q' y hy => by
        rw [hv _ _ y q hy.1, hv _ _ y q' hy.2, pq_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.1.1 hy.1.2 hy.2.2,
          trF_self hL _ _ (𝟙 Y) y hy.1.1, trF_two, gen_trans ha (𝟙 Y) y hy.1.2 hy.2.2]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow, ofMul_one]
        abel)
    refine ⟨s, fun Z r z q h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res r z inf_le_left hz s).symm.trans ((congrArg (gm r z _) (hs q)).trans (hv Z r z q hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q => hs p Z r z q⟩
  choose q hq using fun k => exists_chart hL' (φ' k y)
  have m : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L' φ' q := Set.mem_iInter.2 hq
  refine (hs j _ (𝟙 Y) y q hj m).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y q hj' m)).symm)
  rw [pq_trans hw φ' ε (𝟙 Y) y hj hj' m m, trF_self hL' _ _ (𝟙 Y) y m, inv_one, _root_.mul_one, _root_.mul_assoc]
end GlobalTheory.SqLB
