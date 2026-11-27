-- Prove2me | solution 1 for GlobalTheory.AnVal.JetAlg.anO_fr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:09:12.890178+00:00
-- url     : https://prove2.me/submissions/f9e2299a-1c52-4542-8aa7-a0d5e68efa3a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetRdMulInvPow
import Theorems.Thm_GlobalTheory_AnVal_JetAlg_origin_mem
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_osgood


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
open scoped ContDiff
open GlobalTheory GlobalTheory.AnVal GlobalTheory.AnVal.JetAlg
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {n m : ℕ}
namespace GlobalTheory.AnVal.JetAlg
theorem _root_.solution {ψ : Sp (Jet ℂ (Fin n × Fin g) m) ⟶ A.left} {Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)}
    (hψ : Φ.JetMap m ψ Λ) {j : L.L.ι} (hU : ⊤ ≤ ψ ⁻¹ᵁ L.L.U j) : AnO fun w => Φ.fr j (Λ w) := by
  have h0 := origin_mem Φ hψ hU
  have hopen := (Φ.hol (L.L.U j) 0).1
  have han : AnalyticAt ℂ (Φ.fr j) (Λ (colsOf n g 0)) :=
    ReciprocityTheory.AnForm.Osgood.osgood g _ _ hopen (Φ.fr_hol j) _ h0
  have hc : ContDiff ℂ ω (fun v : Fin (n * g) → ℂ => colsOf n g v) := by
    unfold colsOf
    fun_prop
  have hΛ : ContDiff ℂ ω (fun x : Fin n → Fin g → ℂ => Λ x) := (LinearMap.toContinuousLinearMap Λ).contDiff
  show ContDiffAt ℂ ω (fun v => Φ.fr j (Λ (colsOf n g v))) 0
  exact han.contDiffAt.comp (x := 0) (hΛ.comp hc).contDiffAt
end GlobalTheory.AnVal.JetAlg
