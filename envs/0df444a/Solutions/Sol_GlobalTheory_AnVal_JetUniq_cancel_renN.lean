-- Prove2me | solution 1 for GlobalTheory.AnVal.JetUniq.cancel_renN
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:07.249629+00:00
-- url     : https://prove2.me/submissions/a8b08cc9-567b-4d3c-944c-30371000e73b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FderivEqOfJetOf
import Theorems.Thm_GlobalTheory_AnVal_JetUniq_renInv_renN

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetUniq
namespace GlobalTheory.AnVal.JetUniq
theorem _root_.solution {Y : Scheme.{0}} (n g m : ℕ) (x y : Sp (Jet ℂ (Fin 1 × Fin (n * g)) m) ⟶ Y)
    (h : spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ x =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ y) : x = y := by
  have hc : spMap (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) ≫
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) = 𝟙 _ := by
    unfold spMap
    rw [← Spec.map_comp]
    have hid : CommRingCat.ofHom (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        CommRingCat.ofHom (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) = 𝟙 _ := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro a
      exact renInv_renN n g m a
    rw [hid, Spec.map_id]
  calc x = (spMap (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) ≫
        spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)) ≫ x := by
        rw [hc, Category.id_comp]
    _ = (spMap (renInv n g m : Jet ℂ (Fin n × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) ≫
        spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m)) ≫ y := by
        rw [Category.assoc, h, ← Category.assoc]
    _ = y := by rw [hc, Category.id_comp]
end GlobalTheory.AnVal.JetUniq
