-- Prove2me | solution 1 for GlobalTheory.EigenLattice.tensAct_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:44:37.281717+00:00
-- url     : https://prove2.me/submissions/9714466a-11f2-49c9-af9a-950bd8e9ef46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralThird
import Theorems.Thm_GlobalTheory_EigenLattice_tensAct_tmul
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
noncomputable section
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {c : Ideal (OF E)}
variable {O : Type} [CommRing O] {K : Type} [Field K] [Algebra O K]
variable {H : Type} [AddCommGroup H] [Module O H]
namespace GlobalTheory.EigenLattice
theorem _root_.solution (ρ : orderC c →+* Module.End O H) (σ : E →+* K) (v : K ⊗[O] H)
    (hv : v ∈ eigK ρ σ) (t : orderC c ⊗[ℤ] O) :
    ((tensAct ρ t).baseChange K) v = coordAt O c σ t • v := by
  have hv' : ∀ a : orderC c, (ρ a).baseChange K v = σ a • v := fun a =>
    Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hv a)
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tensAct_tmul, LinearMap.baseChange_smul, LinearMap.smul_apply, hv' a]
    show x • ((σ a : K) • v) = (σ a * algebraMap O K x) • v
    rw [mul_smul, algebraMap_smul, smul_comm]
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add, LinearMap.baseChange_add, LinearMap.add_apply, h₁, h₂, map_add, add_smul]
end GlobalTheory.EigenLattice
