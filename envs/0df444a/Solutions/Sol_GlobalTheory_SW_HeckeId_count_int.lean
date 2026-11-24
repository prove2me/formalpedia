-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.count_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:37:16.260885+00:00
-- url     : https://prove2.me/submissions/a920df5f-bf56-4298-9d89-efa47b9484ed

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_inf_mem_hyp
import Theorems.Thm_GlobalTheory_SW_Nbr_eq_nbOf
import Theorems.Thm_GlobalTheory_SW_Nbr_index_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_mem
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_spec
import Theorems.Thm_GlobalTheory_SW_Nbr_relIndex_eq
import Theorems.Thm_GlobalTheory_SW_Nbr_smul_le_iff
import Theorems.Thm_P2M_GlobalTheory_SW_Nbr_Int__symm_b5c59deb8a7e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical nonZeroDivisors
open scoped TensorProduct LinearAlgebra.Projectivization
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeckeId
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n N : ℕ}
open Nbr
variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X]
namespace GlobalTheory.SW.HeckeId
theorem _root_.solution {M q : ℕ} {P : Ideal (𝓞 E)} (hP : GoodPrime M q P) {Λ : Lt E n}
    (h : Λ ∈ Vset E n M) (u : X →ₗ[𝓞 E] (Fin n → E)) (hu : ∀ ξ, u ξ ∈ Λ) :
    {Λ' ∈ Nb M P Λ | ∀ ξ, u ξ ∈ Λ'}.ncard =
      {K ∈ Hyp P Λ | LinearMap.range (u.codRestrict Λ hu) ≤ K}.ncard := by
  refine Set.BijOn.ncard_eq (f := fun Λ' : Lt E n => Λ'.comap Λ.subtype)
    ⟨fun Λ' h' => ⟨inf_mem_hyp hP h'.1, ?_⟩, fun Λ' h' Λ'' h'' e => ?_, fun K hK => ?_⟩
  · rintro _ ⟨ξ, rfl⟩
    exact h'.2 ξ
  · have e' := congrArg (Submodule.map Λ.subtype) e
    simp only [Submodule.map_comap_subtype] at e'
    exact (eq_nbOf hP h h'.1).trans (e' ▸ (eq_nbOf hP h h''.1).symm)
  · obtain ⟨h3, h4⟩ := (index_iff hP.1 hP.2.2.1 K).2 hK.1
    have h5 : (K.map Λ.subtype).comap Λ.subtype = K :=
      Submodule.comap_map_eq_of_injective Λ.injective_subtype K
    have h6 : P • Λ ≤ K.map Λ.subtype :=
      smul_le_iff.2 fun c hc x hx => ⟨_, h3 c hc ⟨x, hx⟩, rfl⟩
    have h7 : (K.map Λ.subtype).toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
      rw [relIndex_eq, h5, h4]
    have h8 := (nbOf_spec hP h h6 (Λ.map_subtype_le K) h7).2
    refine ⟨_, ⟨nbOf_mem hP h h6 (Λ.map_subtype_le K) h7,
      fun ξ => (h8.ge ⟨_, hK.2 ⟨ξ, rfl⟩, rfl⟩).2⟩, Eq.trans ?_ h5⟩
    ext x
    exact ⟨fun hx => h8.le ⟨x.2, hx⟩, fun hx => (h8.ge hx).2⟩
end GlobalTheory.SW.HeckeId
