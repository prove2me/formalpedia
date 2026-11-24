-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.exists_nb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:40:10.917239+00:00
-- url     : https://prove2.me/submissions/420c67dc-ba27-462d-99a8-5551838018eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_smul_mem
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_gen
import Theorems.Thm_GlobalTheory_SW_HeckeId_perp_mem_hyp
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_index_iff
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
import Theorems.Thm_GlobalTheory_SW_Nbr_nbOf_mem
import Theorems.Thm_GlobalTheory_SW_Nbr_ne_bot_of_norm
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
    (h : Λ ∈ Vset E n M) {a b : 𝓞 E} (ha : a ∈ P) (hab : a + b = 1)
    (u : X →ₗ[𝓞 E] (Fin n → E)) (hH : Λ.comap u ∈ Hyp (conjI P) X) {η : X} (hη : u η ∉ Λ)
    (hI : ∀ ξ, Int' (u η) (u (b • ξ))) : ∃ Λ' ∈ Nb M P Λ, ∀ ξ, u ξ ∈ Λ' := by
  have := max_of_norm hP.1 hP.2.2.1
  have := max_of_norm (good_conj hP).1 (good_conj hP).2.2.1
  have hS : SD Λ := h.2.1
  have hQ : ∀ c ∈ conjI P, ∀ ξ, c • u ξ ∈ Λ := fun c hc ξ => by
    rw [← map_smul]; exact Hyp.smul_mem hH hc ξ
  obtain ⟨h3, h4⟩ := (index_iff hP.1 hP.2.2.1 _).2
    (perp_mem_hyp (ne_bot_of_norm hP.1 hP.2.2.1) hS hη fun c hc => hQ c hc η)
  have h5 : ((perp Λ (u η)).map Λ.subtype).comap Λ.subtype = perp Λ (u η) :=
    Submodule.comap_map_eq_of_injective Λ.injective_subtype _
  have h6 : P • Λ ≤ (perp Λ (u η)).map Λ.subtype :=
    smul_le_iff.2 fun c hc x hx => ⟨_, h3 c hc ⟨x, hx⟩, rfl⟩
  have h7 : ((perp Λ (u η)).map Λ.subtype).toAddSubgroup.relIndex Λ.toAddSubgroup = q := by
    rw [relIndex_eq, h5, h4]
  refine ⟨_, nbOf_mem hP h h6 (Λ.map_subtype_le _) h7, fun ξ => ⟨?_, fun c hc => ?_⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨r, hr⟩ := Hyp.gen hH (v := η) hη ξ
    have hr : u (ξ - r • η) ∈ Λ := hr
    have := Int'.add ((hS _).1 hr z z.2) ((Int'.symm hz).smul r)
    rwa [← map_smul, ← map_add, sub_add_cancel] at this
  · refine ⟨⟨_, hQ c hc ξ⟩, ?_, rfl⟩
    have h8 : Int' (a • c • u ξ) (u η) := h3 a ha ⟨_, hQ c hc ξ⟩
    have := h8.add (hI (c • ξ)).symm
    rwa [map_smul, map_smul, ← add_smul, hab, one_smul] at this
end GlobalTheory.SW.HeckeId
