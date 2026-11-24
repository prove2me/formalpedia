-- Prove2me | solution 1 for GlobalTheory.Div.eigen_line_bilinear.bilin_zero_of_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:30:20.61603+00:00
-- url     : https://prove2.me/submissions/80434ceb-b56c-4ad5-a537-44b2f41f2961

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodProductIntegral
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open GlobalTheory GlobalTheory.Div GlobalTheory.Div.eigen_line_bilinear
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.Div.eigen_line_bilinear
theorem _root_.solution {ρ : orderC c →+* Module.End O H}
    (hdir : DirectSum.IsInternal (fun σ : E →+* K => eigK ρ σ)) (S : LinearMap.BilinForm K (K ⊗[O] H))
    (h : ∀ σ σ' : E →+* K, ∀ x ∈ eigK ρ σ, ∀ y ∈ eigK ρ σ', S x y = 0) (x y : K ⊗[O] H) : S x y = 0 := by
  have hmem : ∀ z : K ⊗[O] H, z ∈ ⨆ σ : E →+* K, eigK ρ σ := fun z => by
    rw [hdir.submodule_iSup_eq_top]; exact Submodule.mem_top
  refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun x => ∀ y, S x y = 0) (hmem x)
    ?_ (fun y => by simp) ?_ y
  · intro σ x hx y
    refine Submodule.iSup_induction (fun σ : E →+* K => eigK ρ σ) (motive := fun y => S x y = 0) (hmem y)
      (fun σ' y hy => h σ σ' x hx y hy) (by simp) ?_
    intro y y' h1 h2
    rw [map_add, h1, h2, add_zero]
  · intro x x' h1 h2 y
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]
end GlobalTheory.Div.eigen_line_bilinear
