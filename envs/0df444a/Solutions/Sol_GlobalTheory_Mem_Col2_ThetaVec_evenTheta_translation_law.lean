-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.evenTheta_translation_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:23.580812+00:00
-- url     : https://prove2.me/submissions/16151766-be2d-43c9-be6d-55eaaeb45104

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_periodLatticeSesquilinearForm_isHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_th0Char_eq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_sigmaSign_sq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_law_iff
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_chi_half
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_thetaZero_periodLattice_eq
import Theorems.Thm_GlobalTheory_ThetaInter_opU_comm
import Theorems.Thm_GlobalTheory_ThetaInter_opU_mul
import Theorems.Thm_GlobalTheory_canonicalSigma_add


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.ThetaVec
open Formalism.L2.Th1 Formalism.L2.Th1.H Complex GlobalTheory.ThetaInter
open scoped BigOperators ComplexConjugate Real
variable (L : PeriodPair)
namespace GlobalTheory.Mem.Col2.ThetaVec
theorem _root_.solution (ω₀ : ℂ) {ω : ℂ} (hω : ω ∈ L.lattice) (z : ℂ) :
    F.thetaZeroCharacter L ω₀ ω * opU (form1 L) ω (F.th0 L (ω₀ / 2)) z = F.th0 L (ω₀ / 2) z := by
  have e : F.th0 L (ω₀ / 2) = fun z => (opU (form1 L) (ω₀ / 2) (canonicalSigma L) 0)⁻¹ *
      opU (form1 L) (ω₀ / 2) (canonicalSigma L) z := by
    funext z; rw [thetaZero_periodLattice_eq, div_eq_inv_mul]
  have e2 : opU (form1 L) ω (canonicalSigma L) = fun z => sigmaSign L ω * canonicalSigma L z := by
    funext z
    rw [← (law_iff L _ ω z).2 (canonicalSigma_add L hω z), ← mul_assoc, sigmaSign_sq, one_mul]
  rw [e, opU_mul, opU_comm (periodLatticeSesquilinearForm_isHerm L), e2, opU_mul, th0Char_eq]
  have h1 := chi_half L ω ω₀
  have h2 := sigmaSign_sq L ω
  set c := (opU (form1 L) (ω₀ / 2) (canonicalSigma L) 0)⁻¹ * opU (form1 L) (ω₀ / 2) (canonicalSigma L) z
  linear_combination (c * sigmaSign L ω * sigmaSign L ω) * h1 + c * h2
end GlobalTheory.Mem.Col2.ThetaVec
