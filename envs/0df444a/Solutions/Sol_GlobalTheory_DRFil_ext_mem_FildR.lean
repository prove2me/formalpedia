-- Prove2me | solution 1 for GlobalTheory.DRFil.ext_mem_FildR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:16:16.388797+00:00
-- url     : https://prove2.me/submissions/3ecd943d-fd18-496c-b7a5-a9865a21ba2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_ext_mulR
import Theorems.Thm_GlobalTheory_DRFil_act_ext
import Theorems.Thm_GlobalTheory_DRFil_ext_mem_FilV
import Theorems.Thm_GlobalTheory_DRFil_mem_DdR
import Theorems.Thm_GlobalTheory_DRFil_mem_DdRE


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
namespace GlobalTheory.DRFil
theorem _root_.solution (ρ : Representation LL G V) (ρ' : Representation LL G V') (f : V →ₗ[LL] V')
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (τ : K →ₐ[Qp] LL) {a : ℤ} {x : V ⊗[Qp] F}
    (hx : x ∈ FildR PD ρ τ a) : ext Qp F f x ∈ FildR PD ρ' τ a := by
  refine ⟨(mem_DdRE PD _ _ _).2 ⟨(mem_DdR PD _ _).2 fun g => ?_, fun c => ?_⟩, ext_mem_FilV PD f hx.2⟩
  · rw [act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx.1.1]
  · rw [← ext_mulR, ((mem_DdRE PD _ _ _).1 hx.1).2 c, map_smul]
end GlobalTheory.DRFil
