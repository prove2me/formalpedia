-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HeckeAdj.isInvInvariant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:34:37.364859+00:00
-- url     : https://prove2.me/submissions/7261c8b2-7162-416a-9d7d-1cdb19447d0a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_SatakeExponents_UniformizerValuations_SubOfNonNil
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteOutNeZero
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_inv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SplitFlip
noncomputable section
open MeasureTheory GlobalTheory.SmGL GlobalTheory.PRep PositivityTheory.Rg.BcN.F2
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeAdj
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.HeckeAdj
theorem _root_.solution [MeasurableSpace F] [BorelSpace F] (μ : Measure (GL ι F)) [μ.IsHaarMeasure]
    (K : Subgroup (GL ι F)) (hKo : IsOpen (K : Set (GL ι F))) (hKc : IsCompact (K : Set (GL ι F))) :
    μ.IsInvInvariant := by
  refine ⟨?_⟩
  have hc := Measure.isMulLeftInvariant_eq_smul μ.inv μ
  have hne : μ (K : Set (GL ι F)) ≠ 0 := (hKo.measure_pos μ ⟨1, K.one_mem⟩).ne'
  have hnt : μ (K : Set (GL ι F)) ≠ ⊤ := hKc.measure_lt_top.ne
  have h2 := congrArg (fun m : Measure (GL ι F) => m (K : Set (GL ι F))) hc
  have hKi : (K : Set (GL ι F))⁻¹ = K := by
    ext x
    simp
  simp only [Measure.inv_apply, hKi, Measure.coe_nnreal_smul_apply] at h2
  have h3 : ((Measure.haarScalarFactor μ.inv μ : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
  have h4 : Measure.haarScalarFactor μ.inv μ = 1 := by exact_mod_cast h3
  rw [hc, h4, one_smul]
end GlobalTheory.CompanionTheory.HeckeAdj
