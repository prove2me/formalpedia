-- Prove2me | solution 2 for OAI.Cotype.walsh_paired_frames_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:17:11.84375+00:00
-- url     : https://prove2.me/submissions/db107fe0-efb2-467a-b4cb-39b7a660e173

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshFrameOrbit.lean:L37-L68
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.walsh_paired_frames_orbit. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Theorems.Thm_OAI_Cotype_paired_frames_orbit

-- ---- from OAI.Analysis.Cotype.BinaryCoordinates ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
theorem binarySign_injective : Function.Injective binarySign := by
  intro a b h
  rcases binary_eq_zero_or_one a with rfl | rfl <;>
    rcases binary_eq_zero_or_one b with rfl | rfl <;> norm_num [binarySign] at *

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshFrameOrbit ----
namespace OAI

noncomputable section

namespace Cotype
variable {n r s : ℕ}

theorem walsh_paired_frames_orbit (U U' : Fin r → Cube n) (V V' : Fin s → Cube n)
    (hU : BinaryFrame U) (hU' : BinaryFrame U')
    (hV : BinaryFrame V) (hV' : BinaryFrame V')
    (hpair : ∀ i j, character (V j) (U i) = character (V' j) (U' i)) :
    ∃ g : WalshSymmetry n,
      (∀ i, primalSymmetry g (U i) = U' i) ∧ ∀ j, dualSymmetry g (V j) = V' j := by
  have hv : LinearIndependent (ZMod 2) (fun j => coordinateDual (cubeBinaryEquiv n (V j))) :=
    hV.map' coordinateDual.toLinearMap (LinearMap.ker_eq_bot.mpr coordinateDual.injective)
  have hv' : LinearIndependent (ZMod 2) (fun j => coordinateDual (cubeBinaryEquiv n (V' j))) :=
    hV'.map' coordinateDual.toLinearMap (LinearMap.ker_eq_bot.mpr coordinateDual.injective)
  have hp (i) (j) : coordinateDual (cubeBinaryEquiv n (V j)) (cubeBinaryEquiv n (U i)) =
      coordinateDual (cubeBinaryEquiv n (V' j)) (cubeBinaryEquiv n (U' i)) := by
    apply binarySign_injective
    simpa only [← character_binary_dot] using hpair i j
  obtain ⟨H,hHu,hHv⟩ := paired_frames_orbit
    (fun i => cubeBinaryEquiv n (U i)) (fun i => cubeBinaryEquiv n (U' i))
    (fun j => coordinateDual (cubeBinaryEquiv n (V j)))
    (fun j => coordinateDual (cubeBinaryEquiv n (V' j))) hU hU' hv hv' hp
  refine ⟨walshSymmetryOfLinear H, ?_, ?_⟩
  · intro i
    change (cubeBinaryEquiv n).symm (H (cubeBinaryEquiv n (U i))) = U' i
    rw [hHu, Equiv.symm_apply_apply]
  · intro j
    apply (cubeBinaryEquiv n).injective
    change cubeBinaryEquiv n ((cubeBinaryEquiv n).symm
      (binaryContragredient H (cubeBinaryEquiv n (V j)))) = _
    rw [Equiv.apply_symm_apply]
    apply coordinateDual.injective
    apply LinearMap.ext
    intro x
    obtain ⟨y,rfl⟩ := H.surjective x
    exact (binaryContragredient_pairing H y _).trans (hHv j y).symm

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.walsh_paired_frames_orbit := @_root_.OAI.Cotype.walsh_paired_frames_orbit
