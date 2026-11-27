-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.jetN_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:42:06.715409+00:00
-- url     : https://prove2.me/submissions/c8f3c473-0173-479c-bd52-dff54783c54b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_Formalism_MainNotions_ModuliIntegralCharts_H1_FBIdJet_psJet_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_PullbackSections_TM_taylor_multiplication

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
namespace GlobalTheory.AnVal.JetAlg
private lemma jetN_eq_renN_psJet_tay {n g : ℕ} (m : ℕ) (f : (Fin n → Fin g → ℂ) → ℂ) :
    jetN m f = renN n g m (psJet m (tay (fun v => f (colsOf n g v)) 0)) := by
  rfl
section
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}
variable {K : Type} [Fintype K] {φ : K → (Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left)}
  {Λ : K → (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
end
end GlobalTheory.AnVal.JetAlg
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
namespace GlobalTheory.AnVal.JetAlg
theorem _root_.solution {n g : ℕ} (m : ℕ) {f h : (Fin n → Fin g → ℂ) → ℂ} (hf : AnO f) (hh : AnO h) :
    jetN m (fun w => f w * h w) = jetN m f * jetN m h := by
  rw [jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, jetN_eq_renN_psJet_tay, ← map_mul, ← FBIdJet.psJet_mul]
  congr 2
  exact (TM.taylor_multiplication.1 _ _ _ hf hh).1
end GlobalTheory.AnVal.JetAlg
