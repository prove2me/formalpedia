-- Prove2me | solution 1 for GlobalTheory.DRFil.Adapted.isJumpV_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:31:46.821498+00:00
-- url     : https://prove2.me/submissions/f43323bc-667e-4cd8-9d37-c494c1259f48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_Adapted_fil_eq
import Theorems.Thm_GlobalTheory_DRFil_Adapted_multV_eq
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
variable [FiniteDimensional Qp K] [CharZero Qp]
open GlobalTheory.DRFil.Adapted
variable {PD} {ρ : Representation LL G V} {τ : K →ₐ[Qp] LL} {ι : Type} [Fintype ι]
    {d : ι → V ⊗[Qp] F} {k : ι → ℤ} (h : Adapted PD ρ τ d k)
include h
namespace GlobalTheory.DRFil.Adapted
theorem _root_.solution (a : ℤ) : IsJumpV PD ρ τ a ↔ ∃ i, k i = a := by
  refine ⟨fun hj => ?_, fun ⟨i, hi⟩ hj => ?_⟩
  · by_contra hn
    push Not at hn
    apply hj
    rw [h.fil_eq, h.fil_eq]
    congr 2
    ext i
    have := hn i
    simp only [Set.mem_setOf_eq]
    omega
  · have h1 := h.multV_eq a
    rw [multV, hj, sub_self] at h1
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 h1.symm i (Finset.mem_univ i)
    simp [hi] at this
end GlobalTheory.DRFil.Adapted
