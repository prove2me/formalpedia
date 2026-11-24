-- Prove2me | solution 1 for GlobalTheory.SerConj.normRev_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:25.143801+00:00
-- url     : https://prove2.me/submissions/aa85d61c-27f0-4eb8-97fe-22f7024540f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.L2.Host.restr_apply



set_option autoImplicit false
noncomputable section
open Polynomial CategoryTheory
open GlobalTheory GlobalTheory.SerConj
open Formalism.IrreducibleCountingLemmas.TYPES
variable {K : Type} [Field K]
namespace GlobalTheory.SerConj
theorem _root_.solution {α : Type} (s : Finset α) (P : α → K[X]) :
    C ((∏ c ∈ s, P c).coeff 0)⁻¹ * (∏ c ∈ s, P c).reverse = ∏ c ∈ s, C ((P c).coeff 0)⁻¹ * (P c).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reverse]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, mul_coeff_zero, mul_inv, C_mul, reverse_mul_of_domain]
    ring
end GlobalTheory.SerConj
