-- Prove2me | solution 1 for GlobalTheory.DRFil.TensInj.tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:15:06.120707+00:00
-- url     : https://prove2.me/submissions/217e8403-0323-4351-9da9-a2a9e1550321

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.DRFil.actVdR_tmul



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.DRFil
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    {V' : Type} [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']
    {V'' : Type} [AddCommGroup V''] [Module LL V''] [Module Qp V''] [IsScalarTower Qp LL V'']
variable {PD}
namespace GlobalTheory.DRFil
namespace TensInj
theorem _root_.solution (h : TensInj PD) (m : ℕ) (c : Fin m → K) (hc : LinearIndependent K₀ c)
    (x : Fin m → V ⊗[Qp] B)
    (hx : ∑ i, mulR Qp F LL V (algebraMap K F (c i)) (ιV PD (LL := LL) (V := V) (x i)) = 0) (i : Fin m) :
    x i = 0 := by
  classical
  let b := Basis.ofVectorSpace Qp V
  have key : ∀ (a : F) (y : V ⊗[Qp] B) j, TensorProduct.equivFinsuppOfBasisLeft (N := F) b
      (mulR Qp F LL V a (ιV PD (LL := LL) (V := V) y)) j =
        a * PD.ι (TensorProduct.equivFinsuppOfBasisLeft (N := B) b y j) := by
    intro a y j
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      have hsm : ∀ (q : Qp) (b : B), PD.ι (q • b) = q • PD.ι b := fun q b =>
        (PD.ι.toLinearMap.restrictScalars Qp).map_smul q b
      simp [ιV, hsm]
    | add a b ha hb => simp only [map_add, ha, hb, Finsupp.add_apply, mul_add]
  apply (TensorProduct.equivFinsuppOfBasisLeft (N := B) b).injective
  ext j
  have := congrArg (fun z => TensorProduct.equivFinsuppOfBasisLeft (N := F) b z j) hx
  simp only [map_sum, Finsupp.finset_sum_apply, key, map_zero, Finsupp.zero_apply] at this
  simpa using h m c hc _ this i
end TensInj
end GlobalTheory.DRFil
