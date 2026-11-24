-- Prove2me | solution 1 for GlobalTheory.RawChartBC.basis_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:51:47.782613+00:00
-- url     : https://prove2.me/submissions/0464ea01-565a-4ba2-a2a5-090b9032c219

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_GermCut
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_JetSubstPCompJetBC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IsRawChartBaseChangeJetPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.RawChartBC
open ReciprocityTheory.ChartRestriction.G.PullbackSections
namespace GlobalTheory.RawChartBC
theorem _root_.solution {S S' : Type} [CommRing S] [CommRing S'] (ψ : S →+* S') {σ κ : Type} [Fintype σ] [Fintype κ]
    (U : σ → κ → S) (h : ∀ v : κ → S, ∃! a : σ → S, ∀ j, ∑ ℓ, a ℓ * U ℓ j = v j) (v : κ → S') :
    ∃! a : σ → S', ∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j := by
  classical
  choose N hN hNu using fun k : κ => h (Pi.single k 1)
  let M : Matrix σ κ S := Matrix.of U
  let P : Matrix κ σ S := Matrix.of N
  have h1 : P * M = 1 := by
    ext k j
    rw [Matrix.mul_apply, Matrix.one_apply]
    refine (hN k j).trans ?_
    simp [Pi.single_apply, eq_comm]
  have h2 : M * P = 1 := by
    ext ℓ ℓ'
    have e : (fun i => (M * P) ℓ i) = fun i => (1 : Matrix σ σ S) ℓ i := by
      refine (h (U ℓ)).unique (fun j => ?_) (fun j => ?_)
      · have : (M * P * M) ℓ j = M ℓ j := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
        rw [Matrix.mul_apply] at this
        exact this
      · have : ((1 : Matrix σ σ S) * M) ℓ j = M ℓ j := by rw [Matrix.one_mul]
        rw [Matrix.mul_apply] at this
        exact this
    exact congrFun e ℓ'
  have h1' : P.map ψ * M.map ψ = 1 := by rw [← Matrix.map_mul, h1]; simp
  have h2' : M.map ψ * P.map ψ = 1 := by rw [← Matrix.map_mul, h2]; simp
  have key : ∀ a : σ → S', (∀ j, ∑ ℓ, a ℓ * ψ (U ℓ j) = v j) ↔ Matrix.vecMul a (M.map ψ) = v := by
    intro a
    rw [funext_iff]
    rfl
  refine ⟨Matrix.vecMul v (P.map ψ), (key _).2 ?_, fun a ha => ?_⟩
  · rw [Matrix.vecMul_vecMul, h1', Matrix.vecMul_one]
  · rw [← (key a).1 ha, Matrix.vecMul_vecMul, h2', Matrix.vecMul_one]
end GlobalTheory.RawChartBC
