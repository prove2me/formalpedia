-- Prove2me | solution 1 for GlobalTheory.SerConj.normRev_normRev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:28:09.063807+00:00
-- url     : https://prove2.me/submissions/631a60f7-d38b-4007-9ba9-6826d75a7790

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_CoeffZeroNeOfMonicIrr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IrreducibleCharacterSeries_ConjugateCharacterFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RootsReverseProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_StarCoeffEisensteinSeriesReversePoly
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_L2_Host_restr_apply
import Theorems.Thm_GlobalTheory_DualLabel_eq_of_rootsBar_eq
import Theorems.Thm_GlobalTheory_DualLabel_monic_normRev
import Theorems.Thm_GlobalTheory_DualLabel_rootsBar_normRev
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
theorem _root_.solution {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    C ((C (f.coeff 0)⁻¹ * f.reverse).coeff 0)⁻¹ * (C (f.coeff 0)⁻¹ * f.reverse).reverse = f := by
  have h1 : (C (f.coeff 0)⁻¹ * f.reverse).coeff 0 ≠ 0 := by
    rw [coeff_C_mul, coeff_zero_reverse, hm.leadingCoeff, mul_one]
    exact inv_ne_zero h0
  refine GlobalTheory.DualLabel.eq_of_rootsBar_eq (GlobalTheory.DualLabel.monic_normRev h1) hm ?_
  rw [GlobalTheory.DualLabel.rootsBar_normRev (GlobalTheory.DualLabel.monic_normRev h0) h1, GlobalTheory.DualLabel.rootsBar_normRev hm h0,
    Multiset.map_map]
  simp
end GlobalTheory.SerConj
