-- Prove2me | solution 1 for GlobalTheory.AnVal.spMap_jetCopy_jetPt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:54:59.408693+00:00
-- url     : https://prove2.me/submissions/3b8f7fcb-da10-486e-af6f-aaff400fc16c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsHolFamPullbackLiftOfCommonBase
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CmFrameJetPointsAreExponentialJets
import Theorems.Thm_GlobalTheory_AnVal_renN_colPr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_anSpMap_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_isLocalHom_jetMap
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetOf_comp_anLin
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_jetPt_precompD


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
open GlobalTheory GlobalTheory.AnVal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AnVal
theorem _root_.solution {Y : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (n m : ℕ) (i : Fin n) :
    spMap (jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt e hol m =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt (fun v => e (colPr n g i v)) (isHolFam_precomp_clm e hol _) m := by
  have hring : ((jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) =
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m).comp
        ((jetMap (anLin (colPr n g i)) (anLin_mem _) :
          Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m) :
          Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) :=
    RingHom.ext fun a => (renN_colPr n g m i a).symm
  rw [hring, anSpMap_comp, Category.assoc]
  congr 1
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin (colPr n g i)) (anLin_mem _)
  refine jetPt_precompD _ _ hol _ (by show e (colPr n g i 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) (colPr n g i)).symm
end GlobalTheory.AnVal
