-- Prove2me | solution 1 for GlobalTheory.DRFil.mem_FildR_of_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:12:30.772332+00:00
-- url     : https://prove2.me/submissions/a41966db-9c87-4ba9-9007-6447e7130294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsComponentEquiv
import Theorems.Thm_GlobalTheory_DRFil_ext_mulR
import Theorems.Thm_GlobalTheory_DRFil_ext_ext_of_leftInverse
import Theorems.Thm_GlobalTheory_DRFil_ext_injective
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
    (hf : ∀ g v, f (ρ g v) = ρ' g (f v)) (hi : Function.Injective f) (τ : K →ₐ[Qp] LL) {a : ℤ}
    {x : V ⊗[Qp] F} (hx : ext Qp F f x ∈ FildR PD ρ' τ a) : x ∈ FildR PD ρ τ a := by
  obtain ⟨s, hs⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hi)
  refine ⟨(mem_DdRE PD _ _ _).2 ⟨(mem_DdR PD _ _).2 fun g => ext_injective f hi ?_,
    fun c => ext_injective f hi ?_⟩, ?_⟩
  · rw [← act_ext PD ρ ρ' f hf, (mem_DdR PD _ _).1 hx.1.1]
  · rw [ext_mulR, ((mem_DdRE PD _ _ _).1 hx.1).2 c, map_smul]
  · rw [← ext_ext_of_leftInverse f s (LinearMap.congr_fun hs) x]
    exact ext_mem_FilV PD s hx.2
end GlobalTheory.DRFil
