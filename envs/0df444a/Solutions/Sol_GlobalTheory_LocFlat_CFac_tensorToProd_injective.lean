-- Prove2me | solution 1 for GlobalTheory.LocFlat.CFac.tensorToProd_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:46:40.014442+00:00
-- url     : https://prove2.me/submissions/50b08e76-db93-4cf9-afe3-b5a0b8974445

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ProdFnMemSB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsLinearOfBilinearSchwartzBruhatProduct
import Theorems.Thm_GlobalTheory_LocFlat_CFac_tensorToProd_tmul
import Theorems.Thm_GlobalTheory_LocFlat_CFac_mulLC_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.LocFlat.CFac.mulLC_apply



set_option autoImplicit false
open GlobalTheory.SplitWeil GlobalTheory.LocFlat.CFac
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.LocFlat GlobalTheory.LocFlat.CFac
namespace GlobalTheory.LocFlat.CFac
theorem _root_.solution (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Function.Injective (tensorToProd X Y) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro t ht
  let b := Module.Free.chooseBasis ℂ (SB X)
  set c := TensorProduct.equivFinsuppOfBasisLeft b t with hc
  have ht' : t = c.sum fun i n => b i ⊗ₜ n := by
    rw [hc, ← TensorProduct.equivFinsuppOfBasisLeft_symm_apply, LinearEquiv.symm_apply_apply]
  have hm : ∀ x y, ∑ i ∈ c.support, (b i).1 x * (c i).1 y = 0 := by
    intro x y
    have := congrArg (fun F : SB (X × Y) => F.1 (x, y)) ht
    simp only [ht', Finsupp.sum, map_sum, tensorToProd_tmul] at this
    simpa [Submodule.coe_sum, Finset.sum_apply] using this
  have hzero : c = 0 := by
    ext i y
    by_cases hi : i ∈ c.support
    · have hli := (linearIndependent_iff'.mp b.linearIndependent) c.support (fun i => (c i).1 y)
        (by
          ext x
          simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ZeroMemClass.coe_zero, Pi.zero_apply]
          rw [← hm x y]
          exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)) i hi
      simpa using hli
    · simp [Finsupp.notMem_support_iff.mp hi]
  rw [ht', hzero]
  simp
end GlobalTheory.LocFlat.CFac
