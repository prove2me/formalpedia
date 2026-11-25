-- Prove2me | solution 1 for GlobalTheory.Mem.Col2.ThetaVec.evenTheta_spans_thetaSpace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:00:22.478662+00:00
-- url     : https://prove2.me/submissions/81bada63-5d4f-4636-9c9e-cbe257e907b2

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_ProductThetaMem
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodLatticeSesquilinearFormIsHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_periodLatticeSesquilinearForm_isHerm
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_th0Char_eq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_law_iff
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_chi_half
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_thetaZero_periodLattice_eq
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_const_ne
import Theorems.Thm_GlobalTheory_Mem_Col2_ThetaVec_opU_zero
import Theorems.Thm_GlobalTheory_ThetaInter_altE_swap
import Theorems.Thm_GlobalTheory_ThetaInter_chi_add_right
import Theorems.Thm_GlobalTheory_ThetaInter_differentiable_opU
import Theorems.Thm_GlobalTheory_ThetaInter_opU_comm
import Theorems.Thm_GlobalTheory_ThetaInter_opU_mul
import Theorems.Thm_GlobalTheory_ThetaInter_opU_opU
import Theorems.Thm_GlobalTheory_exists_eq_mul_canonicalSigma


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
theorem _root_.solution {ω₀ : ℂ} (h0 : ω₀ / 2 ∉ L.lattice) {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hlaw : ∀ ω ∈ L.lattice, ∀ z, F.thetaZeroCharacter L ω₀ ω * opU (form1 L) ω G z = G z) (z : ℂ) :
    G z = G 0 * F.th0 L (ω₀ / 2) z := by
  set t := ω₀ / 2 with ht
  obtain ⟨c, hc⟩ := exists_eq_mul_canonicalSigma L (differentiable_opU (H := form1 L) hG (-t)) fun w hw z => by
    rw [← law_iff, opU_comm (periodLatticeSesquilinearForm_isHerm L)]
    conv_rhs => rw [← funext (hlaw w hw)]
    rw [opU_mul, th0Char_eq]
    have h1 := chi_half L w ω₀
    have h2 : chi (form1 L) w (-t) * chi (form1 L) w t = 1 := by
      rw [← chi_add_right]; simp [chi, altE]
    set u := sigmaSign L w * opU (form1 L) (-t) (opU (form1 L) w G) z
    linear_combination (-u * chi (form1 L) w (-t)) * h1 + u * cexp (π * I * (altE (form1 L) w ω₀ : ℂ)) * h2
  have key : ∀ z, G z = c * opU (form1 L) t (canonicalSigma L) z := by
    intro z
    rw [← opU_mul, ← funext hc, opU_opU (periodLatticeSesquilinearForm_isHerm L), add_neg_cancel, opU_zero]
    have : altE (form1 L) t (-t) = 0 := by
      have := altE_swap (periodLatticeSesquilinearForm_isHerm L) t t
      simp only [altE, map_neg, neg_im] at this ⊢
      linarith
    simp [this]
  rw [key z, key 0, thetaZero_periodLattice_eq]
  have := const_ne L h0
  field_simp
end GlobalTheory.Mem.Col2.ThetaVec
