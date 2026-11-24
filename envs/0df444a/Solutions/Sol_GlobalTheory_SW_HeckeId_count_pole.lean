-- Prove2me | solution 1 for GlobalTheory.SW.HeckeId.count_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:54:41.586114+00:00
-- url     : https://prove2.me/submissions/b8981de5-2129-43ea-a832-4dc16fbe1229

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_NeBotOfNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_TwistAdmissible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_CardKerMatrixFiniteField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HeckeRelationAdmissibleFamilyPointwise
import Theorems.Thm_GlobalTheory_SW_HeckeId_Hyp_eq_of_le
import Theorems.Thm_GlobalTheory_SW_HeckeId_nb_unique
import Theorems.Thm_GlobalTheory_SW_HeckeId_comap_mem_hyp
import Theorems.Thm_GlobalTheory_SW_HeckeId_exists_nb
import Theorems.Thm_GlobalTheory_SW_Nbr_SD_eq_of_le
import Theorems.Thm_GlobalTheory_SW_Nbr_good_conj
import Theorems.Thm_GlobalTheory_SW_Nbr_max_of_norm
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
    (u : X →ₗ[𝓞 E] (Fin n → E)) (hu : ¬ ∀ ξ, u ξ ∈ Λ) {A : ℕ} (B : Fin A → Submodule (𝓞 E) X)
    (hB : ∀ i, B i ∈ Hyp (conjI P) X) (hB1 : Function.Injective B)
    (hB2 : ∀ K ∈ Hyp (conjI P) X, ∃ i, B i = K) (η : Fin A → X) (hη : ∀ i, η i ∉ B i) :
    {i | (∀ ξ ∈ B i, u ξ ∈ Λ) ∧ ∀ ξ, Int' (u (η i)) (u (b • ξ))}.ncard =
      {Λ' ∈ Nb M P Λ | ∀ ξ, u ξ ∈ Λ'}.ncard := by
  have := max_of_norm (good_conj hP).1 (good_conj hP).2.2.1
  have k1 : ∀ i, (∀ ξ ∈ B i, u ξ ∈ Λ) → B i = Λ.comap u := fun i hi => Hyp.eq_of_le (hB i) hi hu
  by_cases hex : ∃ Λ' ∈ Nb M P Λ, ∀ ξ, u ξ ∈ Λ'
  · obtain ⟨Λ', h', hu'⟩ := hex
    obtain ⟨i, hi⟩ := hB2 _ (comap_mem_hyp hP h h' u hu hu')
    obtain ⟨y, hy⟩ := not_forall.1 hu
    rw [Set.ncard_eq_one.2 ⟨i, ?_⟩, Set.ncard_eq_one.2 ⟨Λ', ?_⟩]
    · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨h', hu'⟩, fun L hL =>
        nb_unique hP h hL.1 h' hy (hL.2 y) (hu' y)⟩
    · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨fun ξ hξ => by rwa [hi] at hξ,
        fun ξ => (h'.1.2.1 _).1 (hu' _) _ (hu' _)⟩, fun j hj => hB1 ((k1 j hj.1).trans hi.symm)⟩
  · rw [Set.eq_empty_of_forall_notMem (s := {Λ' ∈ Nb M P Λ | ∀ ξ, u ξ ∈ Λ'})
      fun L hL => hex ⟨L, hL⟩, Set.ncard_empty,
      Set.eq_empty_of_forall_notMem (s := {i | (∀ ξ ∈ B i, u ξ ∈ Λ) ∧ _}), Set.ncard_empty]
    rintro i ⟨hi, hI⟩
    exact hex (exists_nb hP h ha hab u (k1 i hi ▸ hB i) (fun H => hη i (k1 i hi ▸ H)) hI)
end GlobalTheory.SW.HeckeId
