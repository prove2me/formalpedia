-- Prove2me | solution 1 for GlobalTheory.DRFil.sub_sm_idem_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:33.865957+00:00
-- url     : https://prove2.me/submissions/7758bb14-ec0d-4fbb-95bb-1cb71b282eae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_idem_repr
import Theorems.Thm_GlobalTheory_DRFil_sm_tmul_left
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
variable [FiniteDimensional Qp K] [CharZero Qp]
namespace GlobalTheory.DRFil
theorem _root_.solution (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {y : V ⊗[Qp] F} (hy : y ∈ DdR PD ρ) :
    y - sm Qp F LL V (idem F τ) y ∈ Submodule.span LL
      {z | ∃ (c : K), ∃ y ∈ DdR PD ρ, z = mulR Qp F LL V (algebraMap K F c) y - τ c • y} := by
  obtain ⟨n, a, c, h, h1⟩ := idem_repr F τ
  have : y - sm Qp F LL V (idem F τ) y =
      ∑ i, (-a i) • (mulR Qp F LL V (algebraMap K F (c i)) y - τ (c i) • y) := by
    rw [h, map_sum, LinearMap.sum_apply]
    simp only [sm_tmul_left, smul_sub, smul_smul, neg_smul, neg_mul, Finset.sum_sub_distrib,
      Finset.sum_neg_distrib, ← Finset.sum_smul, h1, one_smul]
    abel
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c i, y, hy, rfl⟩)
end GlobalTheory.DRFil
