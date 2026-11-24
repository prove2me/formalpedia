-- Prove2me | solution 1 for GlobalTheory.TestLat.Model.sumGram_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:49.275703+00:00
-- url     : https://prove2.me/submissions/d9d2af71-70f1-42b0-8a03-01330ab80a85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsSelfDualE
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_NotIsSelfDualETwo
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
open NumberField
open Formalism.BasicNotions Formalism.L2.DIV
open scoped Matrix ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.TestLat GlobalTheory.TestLat.Model
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
open NumberField
open scoped Matrix ComplexOrder
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n N : ℕ} {C : Type}
omit [NumberField K]
namespace GlobalTheory.TestLat.Model
namespace _root_.GlobalTheory.TestLat.Model
theorem _root_.solution [StarRing K] [Fintype C] (lam : ι → _root_.Formalism.BasicNotions.DomWeight n)
    (e : Fin N ≃ C × _root_.Formalism.L2.DIV.VVIdx lam)
    (G : ι → Matrix (Fin n) (Fin n) K) (u w : Fin N → K) :
    star u ⬝ᵥ (_root_.GlobalTheory.TestLat.sumGram lam e G *ᵥ w) =
      ∑ c, _root_.Formalism.L2.DIV.pairK lam G (_root_.GlobalTheory.TestLat.valAt lam e c u)
        (_root_.GlobalTheory.TestLat.valAt lam e c w) := by
  classical
  simp only [dotProduct, Matrix.mulVec, _root_.GlobalTheory.TestLat.sumGram, Matrix.of_apply, Pi.star_apply]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [_root_.GlobalTheory.TestLat.valAt, LinearMap.comp_apply, LinearMap.funLeft_apply,
    LinearEquiv.coe_coe, Module.Basis.equivFun_symm_apply, map_sum, map_smulₛₗ,
    LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Equiv.apply_symm_apply]
  rw [Finset.sum_eq_single c (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [if_pos rfl]
  simp only [RingHom.id_apply, starRingEnd_apply]
  ring
end _root_.GlobalTheory.TestLat.Model
end GlobalTheory.TestLat.Model
