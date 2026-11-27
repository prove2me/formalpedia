-- Prove2me | solution 1 for GlobalTheory.JetLinSub.jetPt_clm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:35:11.008687+00:00
-- url     : https://prove2.me/submissions/d1cfd5fe-dc54-4311-a136-9cfcde618800

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub
namespace GlobalTheory.JetLinSub
theorem _root_.solution {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) (e' : (Fin N' → ℂ) → (Sp ℂ ⟶ Y)) (hol' : IsHolFam e')
    (he : ∀ v, e' v = e (T v)) (m : ℕ) :
    spMap ((jetMap (anLin T) (anLin_mem T) : Jet ℂ (Fin 1 × Fin N) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin N') m) :
      Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ (Fin 1 × Fin N') m) ≫ jetPt e hol m = jetPt e' hol' m := by
  obtain rfl : e' = fun v => e (T v) := funext he
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin T) (anLin_mem T)
  refine jetPt_precompD _ _ hol hol' (by show e (T 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) T).symm
end GlobalTheory.JetLinSub
