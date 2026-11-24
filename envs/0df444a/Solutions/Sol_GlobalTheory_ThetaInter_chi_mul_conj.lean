-- Prove2me | solution 1 for GlobalTheory.ThetaInter.chi_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:31:11.186618+00:00
-- url     : https://prove2.me/submissions/29c5c91d-0b95-4978-a16a-f4085a43aed3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_IsSemiChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IntegralDensEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThetaInter
open Formalism.L2.Th1.H Complex
open scoped BigOperators ComplexConjugate
variable {V : Type*} [AddCommGroup V] [Module ℂ V] {H : Sesq V}
namespace GlobalTheory.ThetaInter
theorem _root_.solution (x y y' : V) : chi H x y * conj (chi H x y') = chi H x (y - y') := by
  simp only [chi, ← Complex.exp_conj, ← Complex.exp_add, altE, map_sub, sub_im, map_neg, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_ofNat]
  congr 1; push_cast; ring
end GlobalTheory.ThetaInter
