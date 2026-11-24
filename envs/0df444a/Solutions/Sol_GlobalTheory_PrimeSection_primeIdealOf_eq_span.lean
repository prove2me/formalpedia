-- Prove2me | solution 1 for GlobalTheory.PrimeSection.primeIdealOf_eq_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:47:45.513695+00:00
-- url     : https://prove2.me/submissions/df53b7f6-7770-4457-bc80-f657872c23ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_mem_primeIdealOf_iff
import Theorems.Thm_GlobalTheory_PrimeElement_isPrime_span


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
include hη hp
namespace GlobalTheory.PrimeSection
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) (h : η ∈ U) :
    (hU.primeIdealOf ⟨η, h⟩).asIdeal =
      Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t} := by
  have hπ := hp U hU h
  have hηt : η ∉ X.basicOpen t := (hη η).mpr (specializes_refl η)
  have hP : (Ideal.span {X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t}).IsPrime :=
    GlobalTheory.PrimeElement.isPrime_span hπ
  apply le_antisymm
  ·
    let P : PrimeSpectrum Γ(X, U) := ⟨_, hP⟩
    let y : U := hU.isoSpec.inv P
    have hy : hU.primeIdealOf y = P := by
      change hU.isoSpec.hom (hU.isoSpec.inv P) = P
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
      rfl
    have hyt : y.1 ∉ X.basicOpen t := by
      intro hyt
      have hmem : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t ∈ (hU.primeIdealOf y).asIdeal := by
        rw [hy]
        exact Ideal.subset_span rfl
      rw [mem_primeIdealOf_iff hU y, Scheme.basicOpen_res] at hmem
      exact hmem ⟨y.2, hyt⟩
    have hsp : (⟨η, h⟩ : U) ⤳ y :=
      (Topology.IsInducing.subtypeVal.specializes_iff).mp ((hη y.1).mp hyt)
    have hsp' := hsp.map hU.isoSpec.hom.continuous
    rw [← PrimeSpectrum.le_iff_specializes] at hsp'
    change (hU.primeIdealOf ⟨η, h⟩).asIdeal ≤ (hU.primeIdealOf y).asIdeal at hsp'
    rw [hy] at hsp'
    exact hsp'
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_primeIdealOf_iff hU ⟨η, h⟩,
      Scheme.basicOpen_res]
    exact fun hm => hηt hm.2
end GlobalTheory.PrimeSection
