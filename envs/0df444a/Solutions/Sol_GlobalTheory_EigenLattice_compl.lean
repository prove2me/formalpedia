-- Prove2me | solution 1 for GlobalTheory.EigenLattice.compl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:25:00.05881+00:00
-- url     : https://prove2.me/submissions/d24d642c-1e51-459b-be1f-cf39914fcec4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegralSecond
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
open GlobalTheory GlobalTheory.EigenLattice
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K] [IsFractionRing O K]
variable {H : Type} [AddCommGroup H] [Module O H] {c : Ideal (OF E)}
namespace GlobalTheory.EigenLattice
theorem _root_.solution [Module.Finite O H] (N : Submodule O H) (hN : IsSat N) : ∃ C : Submodule O H, IsCompl N C := by
  haveI : Module.IsTorsionFree O (H ⧸ N) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r m hrm
    by_cases hr : r = 0
    · exact Or.inl hr
    · right
      obtain ⟨h, rfl⟩ := N.mkQ_surjective m
      rw [← map_smul] at hrm
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hrm ⊢
      exact hN r h hr hrm
  haveI : Module.Free O (H ⧸ N) := Module.free_of_finite_type_torsion_free'
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hs' : ∀ q, N.mkQ (s q) = q := fun q => LinearMap.congr_fun hs q
  let f : H →ₗ[O] N := LinearMap.codRestrict N (LinearMap.id - s ∘ₗ N.mkQ) (by
    intro h
    rw [← Submodule.Quotient.mk_eq_zero]
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply]
    rw [Submodule.Quotient.mk_sub]
    have := hs' (N.mkQ h)
    simp only [Submodule.mkQ_apply] at this ⊢
    rw [this, sub_self])
  refine ⟨LinearMap.ker f, LinearMap.isCompl_of_proj (f := f) ?_⟩
  intro x
  ext
  simp [f, (Submodule.Quotient.mk_eq_zero N).2 x.2]
end GlobalTheory.EigenLattice
