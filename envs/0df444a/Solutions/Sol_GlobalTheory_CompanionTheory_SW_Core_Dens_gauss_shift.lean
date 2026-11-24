-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.Core.Dens.gauss_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T13:13:58.090262+00:00
-- url     : https://prove2.me/submissions/37ccecef-e178-4391-baa7-c09c21eaba97

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGaussianFourierStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SchurFunctionCompactSupportModuloUnipotentStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_QuadraticLevelSetDensity

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Core GlobalTheory.CompanionTheory.SW.Core.Dens
variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.SW.Core.Dens
theorem _root_.solution (B : Matrix ι ι F) (ρ : InfinitePlace F → (F →+* ℝ))
    (P : InfinitePlace F → Matrix ι ι ℝ) (t : InfinitePlace F → ℝ) (v : InfinitePlace F → ι → ℝ) :
    gauss B ρ P (fun w => (t w : ℂ) + Complex.I) v =
      (gW P v : ℂ) * Complex.exp ((2 * (Real.pi : ℂ) * Complex.I) *
        ((∑ w, qMap B ρ v w * t w : ℝ) : ℂ)) := by
  simp only [gauss, gW, qMap]
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, add_zero, zero_add, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [sub_eq_add_neg, add_comm, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring
  · exact Finset.sum_congr rfl fun w _ => by push_cast; ring
end GlobalTheory.CompanionTheory.SW.Core.Dens
