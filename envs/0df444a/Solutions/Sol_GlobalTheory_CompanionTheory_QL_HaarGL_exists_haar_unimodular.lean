-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.QL.HaarGL.exists_haar_unimodular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:52.437415+00:00
-- url     : https://prove2.me/submissions/95a0142f-ad51-4c4e-ac7c-db853281e398

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpenStatement
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearUnimodularHaar
import Theorems.Thm_GlobalTheory_T_generalLinear_integral_compact_open
import Theorems.Thm_GroundTheory_Automorphic_Measures_inv_eq_self_GL


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QL GlobalTheory.CompanionTheory.QL.HaarGL
namespace GlobalTheory.CompanionTheory.QL.HaarGL
theorem _root_.solution : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n : ℕ, (∃ κ : Measure (GL (Fin n) F), κ.IsMulLeftInvariant ∧ κ (GLint O n : Set (GL (Fin n) F)) = 1) ∧ ∀ μ : Measure (GL (Fin n) F), μ.IsHaarMeasure → μ.IsMulRightInvariant ∧ μ.IsInvInvariant := by
  intro F _ _ _ _ O ϖ nrm q hLF n
  obtain ⟨hKo, hKc, hlc, _hsc, ht2, -, -⟩ := GlobalTheory.T.generalLinear_integral_compact_open hLF n
  haveI := hlc
  haveI := ht2
  haveI : BorelSpace (GL (Fin n) F) := GlobalTheory.CompanionTheory.QL.instBorelGL n
  refine ⟨?_, fun μ hμ => ?_⟩
  · let μ₀ : Measure (GL (Fin n) F) := Measure.haar
    have hpos : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ 0 :=
      hKo.measure_ne_zero μ₀ ⟨1, (GLint O n).one_mem⟩
    have hfin : μ₀ (GLint O n : Set (GL (Fin n) F)) ≠ ⊤ := hKc.measure_lt_top.ne
    refine ⟨(μ₀ (GLint O n : Set (GL (Fin n) F)))⁻¹ • μ₀, inferInstance, ?_⟩
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.inv_mul_cancel hpos hfin]
  · haveI := hμ
    exact ⟨GroundTheory.Automorphic.Measures.isMulRightInvariant_GL F n μ,
      ⟨GroundTheory.Automorphic.Measures.inv_eq_self_GL F n μ⟩⟩
end GlobalTheory.CompanionTheory.QL.HaarGL
