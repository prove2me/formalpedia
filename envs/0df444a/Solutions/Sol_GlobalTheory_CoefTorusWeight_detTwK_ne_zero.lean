-- Prove2me | solution 1 for GlobalTheory.CoefTorusWeight.detTwK_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:16:00.670488+00:00
-- url     : https://prove2.me/submissions/4a7b774e-d242-492a-856c-92f1851102dc

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_CoefMod
import Definitions.Def_Formalism_GradedWeylDivisibility_DualWeylDominanceOf
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WeylTensorCoefSpaceEndomorphismPreservesTorusWei

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix
open GlobalTheory GlobalTheory.CoefTorusWeight
namespace GlobalTheory.CoefTorusWeight
theorem _root_.solution {K ι : Type} [Field K] [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (h : ι → GL (Fin n) K) : detTwK lam h ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Units.ne_zero _
end GlobalTheory.CoefTorusWeight
