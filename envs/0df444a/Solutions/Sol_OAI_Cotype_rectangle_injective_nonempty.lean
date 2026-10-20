-- Prove2me | solution 1 for OAI.Cotype.rectangle_injective_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T20:52:51.66798+00:00
-- url     : https://prove2.me/submissions/daeea395-e3dd-4da3-8f61-b1022883b5e6

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

open OAI OAI.Cotype
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]


omit [Fintype ι] [Fintype κ] in
theorem solution {s s' : Finset ι} {t t' : Finset κ}
    (hs : s.Nonempty) (ht : t.Nonempty) (h : rectangle s t = rectangle s' t') :
    s = s' ∧ t = t' := by
  have mem : ∀ (a : Finset ι) (b : Finset κ) i k, rectangle a b (i, k) = true ↔ i ∈ a ∧ k ∈ b := by
    intro a b i k; simp [rectangle]
  obtain ⟨i0, hi0⟩ := hs
  obtain ⟨k0, hk0⟩ := ht
  have h0 : i0 ∈ s' ∧ k0 ∈ t' := by rw [← mem, ← h, mem]; exact ⟨hi0, hk0⟩
  constructor
  · ext i; constructor
    · intro hi; have := (mem s' t' i k0).mp (by rw [← h, mem]; exact ⟨hi, hk0⟩); exact this.1
    · intro hi; have := (mem s t i k0).mp (by rw [h, mem]; exact ⟨hi, h0.2⟩); exact this.1
  · ext k; constructor
    · intro hk; have := (mem s' t' i0 k).mp (by rw [← h, mem]; exact ⟨hi0, hk⟩); exact this.2
    · intro hk; have := (mem s t i0 k).mp (by rw [h, mem]; exact ⟨h0.1, hk⟩); exact this.2

