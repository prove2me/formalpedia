-- Prove2me | solution 1 for GlobalTheory.exists_sec_of_gen_diff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:00:50.159894+00:00
-- url     : https://prove2.me/submissions/1bcb8b90-134e-42bc-850a-aede6db2abd8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIsGenTranslDiffComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_KernelPolarisationTrivialOfSectionsVanishZero
import Theorems.Thm_GlobalTheory_exists_pull_sec_sval
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_sec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_sval_pullMulSec
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_invGen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (θ : L.Sec) (ψ φ : Y ⟶ X)
    (d : LB.Gen (LB.LinComb L (K := Fin 2) ![ψ, φ] ![1, -1])) (hd : d.IsGen) :
    ∃ s : (L.pull φ).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s r z J = 0 → gs (r ≫ ψ) z (L.U (J (r ≫ ψ))) (θ.f (J (r ≫ ψ))) = 0 := by
  obtain ⟨s₀, hs₀⟩ := exists_pull_sec_sval θ ψ
  have hF : FormEq (Sum.elim (fun _ : PUnit => 𝟙 Y ≫ ψ) ![ψ, φ])
      (Sum.elim (fun _ => 1) (fun k => -(![1, -1] : Fin 2 → ℤ) k)) (fun _ : PUnit => φ) (fun _ => 1) := by
    intro U _ h
    simp [Fintype.prod_sum_type, Fin.prod_univ_two]
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec s₀ (𝟙 Y) (LB.invGen L _ _ d) (LB.isGen_invGen L _ _ d hd))
  refine ⟨s, fun Z r z J hJ H => ?_⟩
  rw [hs Z r z J hJ, sval_pullMulSec _ _ _ _ r z hJ, Category.comp_id, hs₀ Z r z J hJ] at H
  exact (Units.mul_left_eq_zero _).1 H
end GlobalTheory
