-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.FD.exists_real_basis
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:20:14.476236+00:00
-- url     : https://prove2.me/submissions/99cbc3ef-b65f-45b7-8b0e-b2b71fb97c49

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.CompanionTheory.SW.FD
theorem _root_.solution {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] (A : Matrix ι ι ℝ) (h : A.det ≠ 0) :
    ∃ b : Module.Basis ι ℝ (ι → ℝ), ∀ i, b i = A i := by
  have hl : LinearIndependent ℝ A.row :=
    Matrix.linearIndependent_rows_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 h))
  refine ⟨basisOfLinearIndependentOfCardEqFinrank hl (by simp), fun i => ?_⟩
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  rfl
end GlobalTheory.CompanionTheory.SW.FD
