-- Prove2me | solution 2 for OAI.Cotype.rectangle_injective_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:00:33.394985+00:00
-- url     : https://prove2.me/submissions/0a314f9f-ad64-4688-b740-ef795e75f61e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/Rectangles.lean:L23-L40
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.rectangle_injective_nonempty. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.Rectangles ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
theorem rectangle_injective_nonempty {s s' : Finset ι} {t t' : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) (h : rectangle s t = rectangle s' t') :
    s = s' ∧ t = t' := by
  have he (i : ι) (j : κ) : (i ∈ s ∧ j ∈ t) ↔ (i ∈ s' ∧ j ∈ t') := by
    have hh := congrFun h (i,j)
    apply Iff.of_eq
    simpa only [rectangle, decide_eq_true_eq] using congrArg (fun b : Bool => b = true) hh
  obtain ⟨i₀, hi₀⟩ := hs
  obtain ⟨j₀, hj₀⟩ := ht
  have h₀ := (he i₀ j₀).mp ⟨hi₀, hj₀⟩
  constructor
  · ext i
    exact ⟨fun hi => ((he i j₀).mp ⟨hi, hj₀⟩).1,
      fun hi => ((he i j₀).mpr ⟨hi, h₀.2⟩).1⟩
  · ext j
    exact ⟨fun hj => ((he i₀ j).mp ⟨hi₀, hj⟩).2,
      fun hj => ((he i₀ j).mpr ⟨h₀.1, hj⟩).2⟩

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.rectangle_injective_nonempty := @_root_.OAI.Cotype.rectangle_injective_nonempty
