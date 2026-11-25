-- Prove2me | solution 1 for GlobalTheory.DRFil.adapted_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:41:59.196284+00:00
-- url     : https://prove2.me/submissions/06ea23a8-cae1-4bd9-8667-68afb83a6884

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_sm_self
import Theorems.Thm_GlobalTheory_DRFil_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_actVdR_tmul
import Theorems.Thm_GlobalTheory_DRFil_idem_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_sm_idem_mem_DdRE
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
theorem _root_.solution (τ : K →ₐ[Qp] LL) :
    Adapted PD (Representation.trivial LL G LL) τ (fun _ : Unit => idem F τ) (fun _ => 0) where
  mem _ := by
    refine ⟨?_, idem_mem_FilV PD τ⟩
    have := sm_idem_mem_DdRE PD (Representation.trivial LL G LL) τ (x := 1)
      ((mem_DdR PD _ _).2 fun g => by simp [Algebra.TensorProduct.one_def])
    rwa [sm_self, mul_one] at this
  indep r h i := by
    rw [mul_comm]
    simpa [sm_self] using h
  span n y hy := ⟨fun _ => y, fun _ => by simpa using hy, by simp [sm_self, mul_comm]⟩
end GlobalTheory.DRFil
