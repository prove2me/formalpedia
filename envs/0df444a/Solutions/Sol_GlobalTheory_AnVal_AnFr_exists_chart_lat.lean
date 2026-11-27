-- Prove2me | solution 1 for GlobalTheory.AnVal.AnFr.exists_chart_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:39:58.19125+00:00
-- url     : https://prove2.me/submissions/398fafff-fb23-4300-b9db-fd6b19961cc3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppellHumbertFrameSemicharacter

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnVal
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
namespace GlobalTheory.AnVal
namespace AnFr
theorem _root_.solution : ∃ j, ∀ a ∈ Φ.lat, ⊤ ≤ (Φ.e a).left ⁻¹ᵁ L.L.U j := by
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := inferInstanceAs (Nonempty (PrimeSpectrum ℂ))
  obtain ⟨j, hj⟩ : ∃ j, (Φ.e 0).left pt ∈ L.L.U j :=
    TopologicalSpace.Opens.mem_iSup.1 (L.isLB.cover.ge (Set.mem_univ _))
  have hj0 : ⊤ ≤ (Φ.e 0).left ⁻¹ᵁ L.L.U j := fun z _ => by
    have hz : z = pt := Subsingleton.elim (α := PrimeSpectrum ℂ) z pt
    rw [hz]
    exact hj
  refine ⟨j, fun a ha => ?_⟩
  rw [(Φ.e_ker a).2 ha, ← (Φ.e_ker 0).2 Φ.lat.zero_mem]
  exact hj0
end AnFr
end GlobalTheory.AnVal
