-- Prove2me | solution 1 for GlobalTheory.DRFil.twist_mem_FildR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:20.194788+00:00
-- url     : https://prove2.me/submissions/4a7de99f-fb9d-42c4-a60b-f98d8a9dc996

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_mulR_mulR
import Theorems.Thm_GlobalTheory_DRFil_mulR_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_twist_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_ext_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_ext_sm
import Theorems.Thm_GlobalTheory_DRFil_mem_DdRE
import Theorems.Thm_GlobalTheory_DRFil_sm_one_tmul


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
variable (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V') (w : F) (ψ : G → Qp)
  (hw : ∀ g, PD.actdR g w = ψ g • w) (hf : ∀ g x, ψ g • ρ' g (f x) = f (ρ g x))
include hw hf
namespace GlobalTheory.DRFil
theorem _root_.solution (τ : K →ₐ[Qp] LL) {n a : ℤ} (hn : w ∈ PD.Fil n) {x : V ⊗[Qp] F}
    (hx : x ∈ FildR PD ρ τ a) : mulR Qp F LL V' w (ext Qp F f x) ∈ FildR PD ρ' τ (n + a) := by
  refine ⟨(mem_DdRE PD _ _ _).2 ⟨twist_mem_DdR PD ρ ρ' f w ψ hw hf hx.1.1, fun c => ?_⟩,
    mulR_mem_FilV PD hn (ext_mem_FilV PD f hx.2)⟩
  rw [mulR_mulR, mul_comm, ← mulR_mulR, ← sm_one_tmul (algebraMap K F c), ← ext_sm, sm_one_tmul,
    ((mem_DdRE PD _ _ _).1 hx.1).2 c, map_smul, map_smul]
end GlobalTheory.DRFil
