-- Prove2me | solution 1 for GlobalTheory.TorusNormal.pm_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:11:24.467966+00:00
-- url     : https://prove2.me/submissions/58929592-4268-460c-a2af-03bb5d08ad6c

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory GlobalTheory.TorusNormal
open Formalism.UG.P
variable {L : Type} [Field L]
namespace GlobalTheory.TorusNormal
theorem _root_.solution {n : ℕ} (f g f' g' : Fin n → L) :
    pm f g * pm f' g' = pm (fun i => f i * f' i + g i * g' (Fin.rev i))
      (fun i => f i * g' i + g i * f' (Fin.rev i)) := by
  ext i k
  simp only [pm, Matrix.mul_apply, Matrix.of_apply, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Fin.rev_rev]
  by_cases h1 : k = i <;> by_cases h2 : k = Fin.rev i <;> simp [h1, h2] <;>
    by_cases h3 : i = Fin.rev i <;>
    first
    | (simp only [if_pos h3, if_pos h3.symm]; ring)
    | (simp only [if_neg h3, if_neg (Ne.symm h3)]; ring)
end GlobalTheory.TorusNormal
