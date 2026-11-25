-- Prove2me | solution 1 for GroundTheory.Automorphic.Parabolic.jacquetFixedMap_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:23:07.645828+00:00
-- url     : https://prove2.me/submissions/21a7d132-cff9-4a7a-bee1-cdc114f20eb2

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_Induction
import Definitions.Def_GroundTheory_AutomorphicForms_InductionJacquet
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolicLocal
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_commute
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_hasBasis_nhds_one
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_conj_mem_congruenceSubgroup
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_mem_blockUpper
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_rankTorus_pow
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_exists_fixedVectors_mk_eq
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply



set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal Topology Filter Set MeasureTheory Measure
open scoped NNReal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)
variable {F n β}
variable {V : Type*} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) F) V)
variable {π} {V' : Type*} [AddCommGroup V'] [Module ℂ V'] {π' : Representation ℂ (GL (Fin n) F) V'}
  {V'' : Type*} [AddCommGroup V''] [Module ℂ V''] {π'' : Representation ℂ (GL (Fin n) F) V''}
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
namespace GroundTheory.Automorphic.Parabolic
theorem _root_.solution (hπ : IsAdmissible π) {K : Subgroup (GL (Fin n) F)}
    (hKc : IsCompact (K : Set (GL (Fin n) F))) (hKo : IsOpen (K : Set (GL (Fin n) F)))
    (hfact : ∀ k ∈ K, ∃ z ∈ K ⊓ oppositeUnipotentRadical F n β, ∃ y ∈ K ⊓ levi F n β,
      ∃ x ∈ K ⊓ unipotentRadical F n β, k = z * y * x) :
    Function.Surjective (jacquetFixedMap F n β π K) := by
  rintro ⟨y, hy⟩
  obtain ⟨v, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  have hv : ∀ k ∈ K ⊓ levi F n β,
      Representation.Coinvariants.mk (π.comp (unipotentRadical F n β).subtype) (π k v) =
        Representation.Coinvariants.mk _ v := fun k hk =>
    hy ⟨k, (Subgroup.mem_inf.1 hk).2⟩ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 hk).1)

  obtain ⟨t₀, -, ht₀⟩ := (hasBasis_nhds_one F n).mem_iff.1 (hKo.mem_nhds K.one_mem)
  obtain ⟨m₀, hm₀⟩ := exists_conj_mem_congruenceSubgroup (β := β) hKc t₀
  set c := m₀ + 1 with hc
  set a := rankTorus F n β c with ha
  have haP : a ∈ blockUpper F n β := rankTorus_mem_blockUpper c
  have haN : ∀ u ∈ unipotentRadical F n β, a * u * a⁻¹ ∈ unipotentRadical F n β :=
    fun u hu => conj_mem_unipotentRadical haP hu
  have haN' : ∀ u ∈ unipotentRadical F n β, a⁻¹ * u * a ∈ unipotentRadical F n β := fun u hu => by
    simpa using conj_mem_unipotentRadical ((blockUpper F n β).inv_mem haP) hu
  have haM : ∀ y ∈ K ⊓ levi F n β, a * y = y * a :=
    fun y hy => rankTorus_commute c (Subgroup.mem_inf.1 hy).2
  have haK : ∀ z ∈ K ⊓ oppositeUnipotentRadical F n β, a⁻¹ * z * a ∈ K := fun z hz =>
    ht₀ (hm₀ c (by omega) z (Subgroup.mem_inf.1 hz).1 (Subgroup.mem_inf.1 hz).2
      (K.inv_mem (Subgroup.mem_inf.1 hz).1))
  have hlim : ∀ U ∈ 𝓝 (1 : GL (Fin n) F), ∃ m : ℕ,
      ∀ z ∈ K ⊓ oppositeUnipotentRadical F n β, (a ^ m)⁻¹ * z * a ^ m ∈ U := by
    intro U hU
    obtain ⟨t, -, ht⟩ := (hasBasis_nhds_one F n).mem_iff.1 hU
    obtain ⟨m₁, hm₁⟩ := exists_conj_mem_congruenceSubgroup (β := β) hKc t
    refine ⟨m₁, fun z hz => ?_⟩
    rw [ha, rankTorus_pow]
    exact ht (hm₁ (c * m₁) (by nlinarith) z (Subgroup.mem_inf.1 hz).1 (Subgroup.mem_inf.1 hz).2
      (K.inv_mem (Subgroup.mem_inf.1 hz).1))
  obtain ⟨x, hx, hxq⟩ := exists_fixedVectors_mk_eq hπ hKc hKo hfact a haN haN' haM haK hlim hv
  exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
end GroundTheory.Automorphic.Parabolic
