-- Prove2me | solution 1 for GlobalTheory.exists_lift_cechCocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:17.345975+00:00
-- url     : https://prove2.me/submissions/5691eb33-f0eb-484d-9cb6-9c6cdc22269c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PresheafCubeExactAtSuccOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsAddEquivOfSurjectiveOfKerIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CechModulesFunctorShortExactOfAcyclic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace Opposite
universe v u
noncomputable section
open GlobalTheory
variable {ι : Type} [LinearOrder ι] {R : Type v} [Ring R]
namespace GlobalTheory
theorem _root_.solution {S : ShortComplex (Cube.{u} ι R)}
    (hS : (S.map (cechFunctor ι R)).ShortExact) (p : ℕ)
    (x₃ : LinearMap.ker (Cube.d S.X₃ (p + 1))) :
    ∃ (x₂ : Cube.Term S.X₂ (p + 1)) (x₁ : LinearMap.ker (Cube.d S.X₁ (p + 1 + 1))),
      Cube.termMap S.g (p + 1) x₂ = x₃.1 ∧
      Cube.termMap S.f (p + 1 + 1) x₁.1 = Cube.d S.X₂ (p + 1) x₂ := by
  have h q := (HomologicalComplex.shortExact_iff_degreewise_shortExact _).1 hS q
  have hg : Function.Surjective (Cube.termMap S.g (p + 1)) :=
    (ModuleCat.epi_iff_surjective _).1 (h p).epi_g
  have hf : Function.Injective (Cube.termMap S.f (p + 1 + 1 + 1)) :=
    (ModuleCat.mono_iff_injective _).1 (h (p + 1 + 1)).mono_f
  have he : Function.Exact (Cube.termMap S.f (p + 1 + 1)) (Cube.termMap S.g (p + 1 + 1)) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1 (h (p + 1)).exact
  obtain ⟨x₂, h₂⟩ := hg x₃.1
  obtain ⟨x₁, h₁⟩ := (he (Cube.d S.X₂ (p + 1) x₂)).1 (by rw [Cube.termMap_d, h₂]; exact x₃.2)
  refine ⟨x₂, ⟨x₁, hf ?_⟩, h₂, h₁⟩
  rw [Cube.termMap_d, h₁, Cube.d_d, map_zero]
end GlobalTheory
