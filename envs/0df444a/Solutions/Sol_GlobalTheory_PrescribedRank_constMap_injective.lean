-- Prove2me | solution 1 for GlobalTheory.PrescribedRank.constMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:24.140372+00:00
-- url     : https://prove2.me/submissions/befa2816-8636-4776-a9fc-0610f72ae939

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_DataG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ConstMapInjective
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.MainNotions.G MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.PrescribedRank
variable (p : ℕ) (O Kf : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
namespace GlobalTheory.PrescribedRank
theorem _root_.solution (d : ℕ) (hinj : Function.Injective (algebraMap O Kf)) :
    Function.Injective (constMap p O Kf d) := by
  rw [injective_iff_map_eq_zero]
  intro c hc
  funext i
  have h : c i • (1 : (noPlaces p O Kf).Xsp) = 0 := congrFun (congrFun hc i) (fun v => isEmptyElim v)
  have h2 := congrArg (MvPolynomial.coeff 0) h
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero_one, MvPolynomial.coeff_zero,
    Algebra.smul_def, mul_one] at h2
  apply hinj
  rw [h2]
  simp
end GlobalTheory.PrescribedRank
