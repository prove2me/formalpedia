-- Prove2me | solution 1 for GlobalTheory.DRFil.bil_mem_DdR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:09:47.457242+00:00
-- url     : https://prove2.me/submissions/a5eb8815-cd2f-4eab-83d4-e8de66cd454b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfForallMemFilV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IdemNotMemFilVOne
import Theorems.Thm_GlobalTheory_DRFil_act_bil
import Theorems.Thm_GlobalTheory_DRFil_mem_DdR


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
theorem _root_.solution (ρ : Representation LL G V) (ρ' : Representation LL G V') (ρ'' : Representation LL G V'')
    (β : V →ₗ[LL] V' →ₗ[LL] V'') (hβ : ∀ g v w, β (ρ g v) (ρ' g w) = ρ'' g (β v w))
    {x : V ⊗[Qp] F} {y : V' ⊗[Qp] F} (hx : x ∈ DdR PD ρ) (hy : y ∈ DdR PD ρ') :
    bil Qp F β x y ∈ DdR PD ρ'' :=
  (mem_DdR PD _ _).2 fun g => by
    rw [act_bil PD ρ ρ' ρ'' β hβ, (mem_DdR PD _ _).1 hx, (mem_DdR PD _ _).1 hy]
end GlobalTheory.DRFil
