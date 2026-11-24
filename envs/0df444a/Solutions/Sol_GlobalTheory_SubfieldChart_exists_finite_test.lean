-- Prove2me | solution 1 for GlobalTheory.SubfieldChart.exists_finite_test
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:58:39.94959+00:00
-- url     : https://prove2.me/submissions/a4eb0253-23ba-4b51-8a87-af6dced9a934

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHolomorphicChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.SubfieldChart
open Filter Topology
namespace GlobalTheory.SubfieldChart
theorem _root_.solution {A : Type} {e : A → ℂ} {N : Set (A → ℂ)} (hN : N ∈ 𝓝 e) :
    ∃ (n : ℕ) (r : Fin n → A) (ε : ℝ), 0 < ε ∧ ∀ u : A → ℂ, (∀ i, ‖u (r i) - e (r i)‖ < ε) → u ∈ N := by
  rw [nhds_pi, Filter.mem_pi] at hN
  obtain ⟨I, hI, t, ht, hsub⟩ := hN
  obtain ⟨n, r, hr⟩ := hI.fin_param
  have h1 : Set.pi Set.univ (fun i => t (r i)) ∈ 𝓝 (fun i => e (r i)) :=
    set_pi_mem_nhds Set.finite_univ fun i _ => ht (r i)
  obtain ⟨ε, hε, hb⟩ := Metric.mem_nhds_iff.1 h1
  refine ⟨n, r, ε, hε, fun u hu => hsub fun a ha => ?_⟩
  rw [← hr.2] at ha
  obtain ⟨i, rfl⟩ := ha
  refine hb (a := fun i => u (r i)) ?_ i trivial
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  intro j
  rw [dist_eq_norm]
  exact hu j
end GlobalTheory.SubfieldChart
