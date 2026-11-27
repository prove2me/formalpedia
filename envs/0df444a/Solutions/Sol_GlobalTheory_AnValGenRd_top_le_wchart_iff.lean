-- Prove2me | solution 1 for GlobalTheory.AnValGenRd.top_le_wchart_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:51.336782+00:00
-- url     : https://prove2.me/submissions/df68e2e9-88e0-49d3-ba11-342afd134adb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsHolomorphicGeneratorReadingAutomorphy
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
namespace GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
private theorem preimage_eq_univ_iff_forall_mem {W : Scheme.{0}} (x : Sp ℂ ⟶ W) (U : W.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ ∀ p, x p ∈ U := by
  constructor
  · intro h p
    exact h (show p ∈ (⊤ : (Sp ℂ).Opens) from trivial)
  · intro h p _
    exact h p
section LC
variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
end LC
section Rd
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)
  {Z : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Z ⟶ A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L.L φ ε))
end Rd
end GlobalTheory.AnValGenRd
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.AnValGenRd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open ReciprocityTheory.ChartRestriction.G.TB.ValAt
attribute [local instance] Over.cartesianMonoidalCategory
variable {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K]
namespace GlobalTheory.AnValGenRd
theorem _root_.solution (φ : K → (Y ⟶ X)) (j : K → L.ι) (x : Sp ℂ ⟶ Y) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L φ j ↔ ∀ k, ⊤ ≤ (x ≫ φ k) ⁻¹ᵁ L.U (j k) := by
  simp only [preimage_eq_univ_iff_forall_mem]
  unfold LB.wchart
  constructor
  · intro h k p
    exact Set.mem_iInter.1 (h p) k
  · intro h p
    exact Set.mem_iInter.2 fun k => h k p
end GlobalTheory.AnValGenRd
