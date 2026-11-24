-- Prove2me | solution 1 for GlobalTheory.DRFil.spans_resRep_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:33.146518+00:00
-- url     : https://prove2.me/submissions/ed448553-3e6c-49bb-8550-c1410784c948

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsFinBasisSubsetOfIsField
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
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct Module
variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
variable {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
namespace GlobalTheory.DRFil
theorem _root_.solution (ρ : Representation LL G V) : Spans PD (resRep Qp ρ) ↔ Spans PD ρ := by
  have hm : ∀ (b : F) (y : V ⊗[Qp] F), mulR Qp F Qp V b y = mulR Qp F LL V b y := by
    intro b y
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul v c => simp [mulR]
    | add x z hx hz => rw [map_add, map_add, hx, hz]
  have hd : ∀ y : V ⊗[Qp] F, y ∈ DdR PD (resRep Qp ρ) ↔ y ∈ DdR PD ρ := by
    intro y
    have ha : ∀ g, actVdR PD (resRep Qp ρ) g y = actVdR PD ρ g y := by
      intro g
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul v c => simp [actVdR, resRep]
      | add x z hx hz => rw [map_add, map_add, hx, hz]
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, ha]
  unfold Spans
  simp only [hd, hm]
end GlobalTheory.DRFil
