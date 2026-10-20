-- Prove2me | solution 2 for OAI.Cotype.paired_frames_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:15:23.356669+00:00
-- url     : https://prove2.me/submissions/34ab72af-0d1d-4150-8d40-43f6d078c73b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FrameOrbit.lean:L50-L66
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.paired_frames_orbit. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Theorems.Thm_OAI_Cotype_exists_paired_extension

-- ---- from OAI.Analysis.Cotype.FrameOrbit ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {𝕜 : Type*} [Field 𝕜]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

theorem frame_evaluation_surjective (V : κ → Module.Dual 𝕜 E)
    (hV : LinearIndependent 𝕜 V) : Function.Surjective (LinearMap.pi V) := by
  apply LinearMap.dualMap_injective_iff.mp
  intro φ ψ h
  obtain ⟨c,rfl⟩ := coordinateDual.surjective φ
  obtain ⟨d,rfl⟩ := coordinateDual.surjective ψ
  congr 1
  apply hV.fintypeLinearCombination_injective
  have he (a : κ → 𝕜) :
      (LinearMap.pi V).dualMap (coordinateDual a) = Fintype.linearCombination 𝕜 V a := by
    ext x
    simp [coordinateDual_apply, Fintype.linearCombination_apply]
  rwa [he, he] at h

theorem paired_frames_orbit [FiniteDimensional 𝕜 E]
    (U U' : ι → E) (V V' : κ → Module.Dual 𝕜 E)
    (hU : LinearIndependent 𝕜 U) (hU' : LinearIndependent 𝕜 U')
    (hV : LinearIndependent 𝕜 V) (hV' : LinearIndependent 𝕜 V')
    (hpair : ∀ i j, V j (U i) = V' j (U' i)) :
    ∃ H : E ≃ₗ[𝕜] E, (∀ i, H (U i) = U' i) ∧ ∀ j x, V' j (H x) = V j x := by
  let f := Fintype.linearCombination 𝕜 U
  let f' := Fintype.linearCombination 𝕜 U'
  have hp : (LinearMap.pi V).comp f = (LinearMap.pi V').comp f' := by
    ext c j
    simp [f, f', Fintype.linearCombination_apply, hpair]
  obtain ⟨H,hH,hpH⟩ := exists_paired_extension f f' (LinearMap.pi V) (LinearMap.pi V')
    hU.fintypeLinearCombination_injective hU'.fintypeLinearCombination_injective
    (frame_evaluation_surjective V hV) (frame_evaluation_surjective V' hV') hp
  refine ⟨H, ?_, fun j x => congrFun (hpH x) j⟩
  intro i
  simpa [f, f', Fintype.linearCombination_apply] using hH (Pi.single i 1)

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.paired_frames_orbit := @_root_.OAI.Cotype.paired_frames_orbit
