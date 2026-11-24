-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.SplitPair.loc_mul_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:05:25.915579+00:00
-- url     : https://prove2.me/submissions/b304af97-f64a-4d10-b019-31b0776daf66

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SplitsInCMFieldTwoPrimesDegreeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeCharUnramifiedInverseSplitPair
import Theorems.Thm_GlobalTheory_CMVal_Euler_mem_aboveF


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler GlobalTheory.CMVal.Euler.SplitPair
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler.SplitPair
theorem _root_.solution {χ : HChar E} (hF : TrivOnF χ) {v : HeightOneSpectrum (OF E)} {P P' : HeightOneSpectrum (𝓞 E)}
    (hP : Over P v) (hP' : Over P' v) (hne : P ≠ P') (h2 : ∀ R, Over R v → R = P ∨ R = P') (a : OF E) (ha : a ≠ 0) :
    χ.loc P (locF P a ha) * χ.loc P' (locF P' a ha) = 1 := by
  classical
  have hS : Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v = {P, P'} := by
    ext R
    rw [mem_aboveF, Finset.mem_insert, Finset.mem_singleton]
    refine ⟨h2 R, ?_⟩
    rintro (rfl | rfl)
    · exact hP
    · exact hP'
  have h := hF.1 v (unitF a ha)
  unfold Formalism.L2.Host.HChar.resFin at h
  rw [MonoidHom.finsetProd_apply, hS, Finset.prod_pair hne] at h
  exact h
end GlobalTheory.CMVal.Euler.SplitPair
