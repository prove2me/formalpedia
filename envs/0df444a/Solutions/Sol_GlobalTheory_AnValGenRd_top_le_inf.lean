-- Prove2me | solution 1 for GlobalTheory.AnValGenRd.top_le_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:41:41.543167+00:00
-- url     : https://prove2.me/submissions/f3022d37-cafc-4082-b37c-128d669ef425

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
theorem _root_.solution {x : Sp ℂ ⟶ Y} {U V : Y.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (h' : ⊤ ≤ x ⁻¹ᵁ V) :
    ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) := by
  rw [preimage_eq_univ_iff_forall_mem] at h h' ⊢
  intro p
  exact TopologicalSpace.Opens.mem_inf.2 ⟨h p, h' p⟩
end GlobalTheory.AnValGenRd
