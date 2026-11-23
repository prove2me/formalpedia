-- Prove2me | solution 1 for GlobalTheory.DRFil.exists_ext_mem_FilV
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:33:08.541076+00:00
-- url     : https://prove2.me/submissions/6d6bea32-78bc-4a1f-ba50-93a7cdb37089

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_FilV_induction
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_tmul_mem_FilV
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
theorem _root_.solution (g : V →ₗ[LL] V') (hg : Function.Surjective g) {a : ℤ} {y : V' ⊗[Qp] F}
    (hy : y ∈ FilV PD (LL := LL) (V := V') a) : ∃ x ∈ FilV PD (LL := LL) (V := V) a, ext Qp F g x = y := by
  refine FilV_induction PD (p := fun y => ∃ x ∈ FilV PD (LL := LL) (V := V) a, ext Qp F g x = y)
    ⟨0, Submodule.zero_mem _, map_zero _⟩ (fun w b hb => ?_) ?_ hy
  · obtain ⟨v, rfl⟩ := hg w
    exact ⟨v ⊗ₜ b, tmul_mem_FilV PD v hb, by simp⟩
  · rintro _ _ ⟨x, hx, rfl⟩ ⟨x', hx', rfl⟩
    exact ⟨x + x', Submodule.add_mem _ hx hx', map_add _ _ _⟩
end GlobalTheory.DRFil
