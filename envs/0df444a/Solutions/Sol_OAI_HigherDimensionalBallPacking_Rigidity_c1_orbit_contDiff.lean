-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:54:52.746664+00:00
-- url     : https://prove2.me/submissions/a62a2a0d-ab99-441b-9b1e-24460fadbcc5

import Mathlib
import Definitions.Def_OAIQ10Bp008
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_c1_shift_value_continuous
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_holder_shift_value_hasFDerivAt

section
-- module Solutions.OAIQ10_BP.BallPacking_Necessity_OrbitRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff Topology
open Set Function Filter
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
open Set Function MeasureTheory
open Set Function
open SymplecticBallPacking.Hamiltonian (Plane planarCurl)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm radiusSq planarArea planarArea_apply)
open SymplecticBallPacking.Hamiltonian (Plane planarCurl angularOneForm)
open SymplecticBallPacking.Hamiltonian (Plane angularOneForm)
open SymplecticBallPacking.Hamiltonian
open SymplecticBallPacking.Hamiltonian (Plane)
open Set Filter Function
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Finset
open scoped ContDiff Topology Classical
open Set Filter
open scoped BoundedContinuousFunction ContDiff Topology
open Set Function Filter Topology
open scoped NNReal
open scoped ContDiff Topology BoundedContinuousFunction
open Function
open scoped Topology ContDiff
open scoped ContDiff Topology Convolution
open Set Filter Function MeasureTheory _root_.ContinuousLinearMap
open Set Filter Function MeasureTheory

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function
namespace HigherDimensionalBallPacking.Rigidity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderGroup
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitHolderSpace
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Group
attribute [local instance] OAI.HigherDimensionalBallPacking.Rigidity.orbitC1Space
theorem orbit_response_comp (α : ℝ) (k : ℕ) (f : C1HolderSpace E α) (x : ℂ)
    (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
    (hΦ : ContDiffAt ℝ ∞ Φ (x,holderShift α x (c1HolderValue α f)))
    (heq : (fun h => c1HolderShift α h f)=ᶠ[𝓝 x] fun h => Φ (h,holderShift α h (c1HolderValue α f)))
    (hG : ContDiffAt ℝ (k:ℕ∞ω) (fun h => holderShift α h (c1HolderValue α f)) x) :
    ContDiffAt ℝ (k:ℕ∞ω) (fun h => c1HolderShift α h f) x := by
  have hk : (k:ℕ∞ω) ≤ ∞ := by exact_mod_cast (le_top : (k:ℕ∞) ≤ ⊤)
  exact ((hΦ.of_le hk).comp x (contDiffAt_id.prodMk hG)).congr_of_eventuallyEq heq

 theorem orbit_gain (α : ℝ) (f : C1HolderSpace E α) (k : ℕ) (x : ℂ)
    (hF : ContDiffAt ℝ (k:ℕ∞ω) (fun h => c1HolderShift α h f) x)
    (hDG : ∀ᶠ h in 𝓝 x, HasFDerivAt (fun h => holderShift α h (c1HolderValue α f))
      (holderTranspose α (holderShift α h (c1HolderDeriv α f))) h) :
    ContDiffAt ℝ (k+1) (fun h => holderShift α h (c1HolderValue α f)) x := by
  apply contDiffAt_succ_iff_hasFDerivAt.mpr
  refine ⟨fun h => holderTranspose α (holderShift α h (c1HolderDeriv α f)),?_,?_⟩
  · exact ⟨{h | HasFDerivAt (fun h => holderShift α h (c1HolderValue α f))
        (holderTranspose α (holderShift α h (c1HolderDeriv α f))) h},hDG,fun _ h => h⟩
  · have hdL : ContDiff ℝ (k:ℕ∞ω) (c1HolderDeriv (E := E) α) := ContinuousLinearMap.contDiff _
    have htL : ContDiff ℝ (k:ℕ∞ω) (holderTranspose (X := ℂ) (E := E) α) := ContinuousLinearMap.contDiff _
    exact htL.contDiffAt.comp x (hdL.contDiffAt.comp x hF)

 theorem c1_orbit_contDiff_oai (α : ℝ) (hα : 0<α) (f : C1HolderSpace E α)
    (U : Set ℂ) (hU : IsOpen U)
    (Φ : ℂ × HolderSpace ℂ E α → C1HolderSpace E α)
    (hΦ : ∀ h∈U, ContDiffAt ℝ ∞ Φ (h,holderShift α h (c1HolderValue α f)))
    (heq : ∀ h∈U, c1HolderShift α h f=Φ (h,holderShift α h (c1HolderValue α f))) :
    ∀ h∈U, ContDiffAt ℝ ∞ (fun h => c1HolderShift α h f) h := by
  let F := fun h : ℂ => c1HolderShift α h f
  let G := fun h : ℂ => holderShift α h (c1HolderValue α f)
  have he (h : ℂ) (hh : h∈U) : F=ᶠ[𝓝 h] fun x => Φ (x,G x) := by
    filter_upwards [hU.mem_nhds hh] with x hx
    exact heq x hx
  have hG0 : ContDiff ℝ 0 G := contDiff_zero.mpr (c1_shift_value_continuous α hα f)
  have hF0 : ∀ h∈U, ContDiffAt ℝ 0 F h := by
    intro h hh
    exact orbit_response_comp α 0 f h Φ (hΦ h hh) (he h hh) hG0.contDiffAt
  have hDG : ∀ h∈U, HasFDerivAt G (holderTranspose α (holderShift α h (c1HolderDeriv α f))) h := by
    intro h hh
    apply holder_shift_value_hasFDerivAt α hα f h
    exact (c1HolderDeriv (E := E) α).continuous.continuousAt.comp (hF0 h hh).continuousAt
  have hn : ∀ k : ℕ, ∀ h∈U, ContDiffAt ℝ k F h := by
    intro k
    induction k with
    | zero => exact hF0
    | succ k ih =>
      intro h hh
      have hkG := orbit_gain α f k h (ih h hh) (by
        filter_upwards [hU.mem_nhds hh] with x hx
        exact hDG x hx)
      exact orbit_response_comp α (k+1) f h Φ (hΦ h hh) (he h hh) hkG
  intro h hh
  exact contDiffAt_infty.mpr (fun k => hn k h hh)

end HigherDimensionalBallPacking.Rigidity

 

 

open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function





open scoped ContDiff Topology BoundedContinuousFunction
open Set Filter Function

end

end OAI
end

theorem solution : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_contDiff_oai := @OAI.HigherDimensionalBallPacking.Rigidity.c1_orbit_contDiff_oai
