-- Prove2me | solution 1 for GlobalTheory.UU.PackageDescent.exists_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:36:21.875267+00:00
-- url     : https://prove2.me/submissions/e681aad9-783c-48d1-839f-296a88b660e2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CubeDescendsAlongEtaleIsogeny
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsDescendThrough
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_mulGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_pullGen_isGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_exists_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_pull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.UU GlobalTheory.UU.PackageDescent
variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] {i : H ⟶ G}
namespace GlobalTheory.UU.PackageDescent
theorem _root_.solution {L : RigLB G} {c : CubicalStr G L} (s : BiTriv c i) (σ : CubTriv c i) :
    ∃ a : LB.Gen (LB.LinComb L.L (K := Fin 2) ![((fst H G ≫ i) * snd H G).left, (snd H G).left] ![1, -1]), a.IsGen ∧
      ∀ (T : Over S) (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J), Good L.L z J →
        val a (lift t x).left z J = val s.s (lift t x).left z J * val σ.s t.left z J := by
  obtain ⟨a, ha, va⟩ := exists_gen L.isLB (φ' := ![((fst H G ≫ i) * snd H G).left, (snd H G).left]) (ε' := ![1, -1])
    (fun U _ h => by
      have e : (fst H G).left ≫ (1 : H ⟶ G).left = (1 : H ⊗ G ⟶ G).left := by
        rw [← Over.comp_left, MonObj.comp_one]
      rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h ((fst H G ≫ i) * snd H G).left ^ (1 : ℤ) * h (fst H G ≫ i).left ^ (-1 : ℤ) * h (snd H G).left ^ (-1 : ℤ) *
        h (1 : H ⊗ G ⟶ G).left ^ (1 : ℤ) * (h (fst H G ≫ i).left ^ (1 : ℤ) *
          h ((fst H G).left ≫ (1 : H ⟶ G).left) ^ (-1 : ℤ)) =
        h ((fst H G ≫ i) * snd H G).left ^ (1 : ℤ) * h (snd H G).left ^ (-1 : ℤ)
      rw [e]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ s.s (LB.pullGen L.L _ _ σ.s (fst H G).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ s.gen (DVR.pullGen_isGen _ _ _ _ σ.gen _))
  refine ⟨a, ha, fun T t x z J hJ => ?_⟩
  rw [va _ _ z J hJ, val_mul hJ, val_pull hJ, ← Over.comp_left, lift_fst]
end GlobalTheory.UU.PackageDescent
