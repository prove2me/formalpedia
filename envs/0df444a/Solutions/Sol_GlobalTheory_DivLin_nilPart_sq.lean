-- Prove2me | solution 1 for GlobalTheory.DivLin.nilPart_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:41:08.163069+00:00
-- url     : https://prove2.me/submissions/e012a4bf-fa67-46e9-a294-16d961edb4eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ScaledRestrictionEndomorphisms
import Theorems.Thm_P2M_GlobalTheory_DivLin_baseChange_mul__56c41815aef1
import Theorems.Thm_GlobalTheory_DivLin_nilPart_eq
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.DivLin
variable {O : Type} [CommRing O] {H : Type} [AddCommGroup H] [Module O H] {I : Type} [Fintype I]
  (R : Type) [CommRing R] [Algebra O R]
namespace GlobalTheory.DivLin
theorem _root_.solution {M : I → Module.End O H} (hMM : ∀ i j, M i * M j = 0) (l : ℕ) (t : I → R) :
    nilPart l M R t * nilPart l M R t = 0 := by
  have hSS : (∑ i, t i • (M i).baseChange R) * (∑ i, t i • (M i).baseChange R) = 0 := by
    simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, ← baseChange_mul', hMM,
      LinearMap.baseChange_zero, smul_zero, Finset.sum_const_zero]
  rw [nilPart_eq, smul_mul_smul_comm, hSS, smul_zero]
end GlobalTheory.DivLin
