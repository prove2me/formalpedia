-- Prove2me | solution 1 for GlobalTheory.DRFil.spans_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:32.025401+00:00
-- url     : https://prove2.me/submissions/30c9ccfa-c380-4789-ae66-6ba5e5bee455

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
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
theorem _root_.solution (ρ : Representation LL G V) : Spans PD ρ ↔
    ∀ y, y ∈ Submodule.span LL {z | ∃ (b : F), ∃ d ∈ DdR PD ρ, z = mulR Qp F LL V b d} := by
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · obtain ⟨m, b, d, hd, rfl⟩ := h y
    exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨b i, d i, hd i, rfl⟩
  · obtain ⟨m, c, z, rfl⟩ := Submodule.mem_span_set'.1 (h y)
    choose b d hd hz using fun i => (z i).2
    exact ⟨m, b, fun i => c i • d i, fun i => Submodule.smul_mem _ _ (hd i), by simp only [hz, map_smul]⟩
end GlobalTheory.DRFil
