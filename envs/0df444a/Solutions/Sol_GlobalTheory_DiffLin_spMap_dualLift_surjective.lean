-- Prove2me | solution 1 for GlobalTheory.DiffLin.spMap_dualLift_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:22:09.503905+00:00
-- url     : https://prove2.me/submissions/acac489e-6b1d-4ca7-956f-05016bc74987

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_ChartLawPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_IsDiffSumSmulOfIsLieComb
import Theorems.Thm_GlobalTheory_DiffLin_fst_dualLift
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
open GlobalTheory.DiffLin
open ReciprocityTheory.ChartRestriction.G.Chart (JetR zR jetAug dualLift dualLift_zR fstD_comp_dualLift ker_jetAug_pow)
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.DiffLin
theorem _root_.solution (t : Fin n → R) :
    Function.Surjective (spMap (dualLift t : JetR R (Fin n) 1 →+* DualNumber R)) := by
  intro p
  have hs : Function.Surjective (jetAug R (Fin n) 1 : JetR R (Fin n) 1 →+* R) := fun a =>
    ⟨algebraMap R _ a, (jetAug R (Fin n) 1).commutes a⟩
  have hp : (p : PrimeSpectrum (JetR R (Fin n) 1)) ∈
      Set.range (PrimeSpectrum.comap (jetAug R (Fin n) 1 : JetR R (Fin n) 1 →+* R)) := by
    rw [range_comap_of_surjective _ _ hs]
    intro a ha
    apply (PrimeSpectrum.isPrime p).mem_of_pow_mem (1 + 1)
    have : a ^ (1 + 1) ∈ (RingHom.ker (jetAug R (Fin n) 1)) ^ (1 + 1) := Ideal.pow_mem_pow ha _
    rw [ker_jetAug_pow, Ideal.mem_bot] at this
    rw [this]
    exact Ideal.zero_mem _
  obtain ⟨q, rfl⟩ := hp
  refine ⟨PrimeSpectrum.comap (TrivSqZeroExt.fstHom R R R).toRingHom q, ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun y => ?_)
  change (dualLift t y).fst ∈ q.asIdeal ↔ jetAug R (Fin n) 1 y ∈ q.asIdeal
  rw [fst_dualLift]
end GlobalTheory.DiffLin
