-- Prove2me | solution 1 for GlobalTheory.DRFil.sm_idem_mem_DdRE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:17:37.201803+00:00
-- url     : https://prove2.me/submissions/4ef4adf7-d6b7-4b9a-bef0-e7bbeb80030a

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_LocCoh
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Theorems.Thm_GlobalTheory_DRFil_mulR_sm_idem
import Theorems.Thm_GlobalTheory_DRFil_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_mem_DdRE
import Theorems.Thm_GlobalTheory_DRFil_act_sm
import Theorems.Thm_GlobalTheory_DRFil_actR_idem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
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
theorem _root_.solution (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) {x : V ⊗[Qp] F}
    (hx : x ∈ DdR PD ρ) : sm Qp F LL V (idem F τ) x ∈ DdRE PD ρ τ := by
  rw [mem_DdRE, mem_DdR]
  refine ⟨fun g => ?_, fun c => mulR_sm_idem τ c x⟩
  rw [act_sm, actR_idem, (mem_DdR PD ρ x).1 hx]
end GlobalTheory.DRFil
