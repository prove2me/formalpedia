-- Prove2me | solution 1 for GlobalTheory.map_mem_HHa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:29:49.96771+00:00
-- url     : https://prove2.me/submissions/2661e778-121b-438a-b450-cd2203763f80

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IsLevMove
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AllTest
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_CIndBC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AdmissibleColumnsLeAndHarmonicMapCover
import Theorems.Thm_GlobalTheory_map_lap_one
import Theorems.Thm_GlobalTheory_map_rowShift

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
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {T : Type} (r : T → ℕ) (n : ℕ) {k k' : Type} [Field k] [Field k'] (f : k →+* k')
    (hf : Function.Surjective f) (cc : T → T) (isX : T → Prop) (a : T → ℕ → ℕ)
    (P : MvPolynomial (Letter T r n) k) (hP : P ∈ HHa r n k cc isX a) :
    MvPolynomial.map f P ∈ HHa r n k' cc isX a := by
  obtain ⟨h1, h2, h3⟩ := hP
  refine ⟨?_, ?_, ?_⟩
  · simp only [harmK, Submodule.mem_iInf, LinearMap.mem_ker] at h1 ⊢
    intro τ hτ b b'
    rw [map_lap_one, h1 τ hτ b b', map_zero]
  · intro σ i i' hi t
    obtain ⟨s, rfl⟩ := hf t
    rw [map_rowShift, h2 σ i i' hi s]
  · intro m hm
    exact h3 m (MvPolynomial.support_map_subset f P hm)
end GlobalTheory
