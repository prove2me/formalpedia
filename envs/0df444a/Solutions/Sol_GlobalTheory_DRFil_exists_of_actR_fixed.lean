-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_of_actR_fixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T14:09:22.055265+00:00
-- url     : https://prove2.me/submissions/563bcc9d-b8ff-4092-ad64-2788906446f2

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
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
namespace GlobalTheory.DRFil
theorem _root_.solution (x : LL ⊗[Qp] F) (hx : ∀ g, actR PD LL g x = x) :
    ∃ (n : ℕ) (a : Fin n → LL) (c : Fin n → K), x = ∑ i, a i ⊗ₜ[Qp] algebraMap K F (c i) := by
  classical
  let b := Module.Basis.ofVectorSpace Qp LL
  let e := TensorProduct.equivFinsuppOfBasisLeft (N := F) b
  have he : ∀ g y i, e (actR PD LL g y) i = PD.actdR g (e y i) := by
    intro g y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul v c =>
      have : ∀ (q : Qp) (z : F), PD.actdR g (q • z) = q • PD.actdR g z := fun q z =>
        ((PD.actdR g).toLinearMap.restrictScalars Qp).map_smul q z
      simp [e, this]
    | add a b ha hb => simp only [map_add, Finsupp.add_apply, ha, hb]
  have hx' : x = (e x).sum fun i c => b i ⊗ₜ[Qp] c := by
    rw [← TensorProduct.equivFinsuppOfBasisLeft_symm_apply]
    exact (e.symm_apply_apply x).symm
  choose c hc using fun i => PD.invdR (e x i) fun g => by rw [← he, hx]
  let s := (e x).support
  refine ⟨s.card, fun j => b (s.equivFin.symm j), fun j => c (s.equivFin.symm j), ?_⟩
  conv_lhs => rw [hx']
  rw [Finsupp.sum, ← Finset.sum_coe_sort]
  refine Fintype.sum_equiv s.equivFin _ _ fun i => ?_
  simp [hc]
end GlobalTheory.DRFil
