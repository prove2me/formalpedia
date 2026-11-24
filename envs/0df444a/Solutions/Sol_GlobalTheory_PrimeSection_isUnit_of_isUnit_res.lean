-- Prove2me | solution 1 for GlobalTheory.PrimeSection.isUnit_of_isUnit_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:57.60872+00:00
-- url     : https://prove2.me/submissions/60bb7063-d710-46ce-880d-8ae0ba502803

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_res_res
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
import Theorems.Thm_GlobalTheory_PrimeSection_algebraMap_germ
import Theorems.Thm_GlobalTheory_PrimeSection_eq_of_germ_eq
import Theorems.Thm_GlobalTheory_PrimeSection_mem_of_notMem_basicOpen
import Theorems.Thm_GlobalTheory_PrimeSection_primeIdealOf_eq_span
import Theorems.Thm_GlobalTheory_PrimeElement_exists_algebraMap_eq
import Theorems.Thm_GlobalTheory_PrimeElement_exists_unit_algebraMap_eq
import Theorems.Thm_GlobalTheory_PrimeElement_isPrime_span

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.PrimeSection
section Integral
variable {X : Scheme.{u}} [IsIntegral X]
end Integral
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
variable [IsIntegral X]
private theorem exists_section_restrict_eq_of_germ_eq {V : X.Opens} (hV : IsAffineOpen V) (hηV : η ∈ V)
    (hπ : Prime (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (hq : (hV.primeIdealOf ⟨η, hηV⟩).asIdeal = Ideal.span {X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t})
    (hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (y : Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))) (z : X.presheaf.stalk η)
    (h : X.presheaf.germ _ (genericPoint X) hY y = algebraMap (X.presheaf.stalk η) X.functionField z) :
    ∃ r : Γ(X, V), X.presheaf.map (homOfLE (X.basicOpen_le _)).op r = y ∧
      (IsUnit y → IsUnit z → IsUnit r) := by
  have := GlobalTheory.PrimeElement.isPrime_span hπ
  have : Nonempty V := ⟨⟨η, hηV⟩⟩
  have : Nonempty (X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) := ⟨⟨_, hY⟩⟩
  let _ : Algebra Γ(X, V) Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))).op).hom.toAlgebra
  have : IsLocalization.Away (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)
      Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t)) :=
    hV.isLocalization_basicOpen _
  let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨η, hηV⟩ : V)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk η) (Ideal.span {X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t}) := by
    have h0 := hV.isLocalization_stalk ⟨η, hηV⟩
    unfold IsLocalization.AtPrime at h0 ⊢
    convert h0 using 3
    exact hq.symm
  have : IsScalarTower Γ(X, V) Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
      X.functionField := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    exact (germ_res (X.basicOpen_le _) hY a).symm
  have : FaithfulSMul Γ(X, V) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (X.germToFunctionField_injective V)
  have : IsScalarTower Γ(X, V) (X.presheaf.stalk η) X.functionField :=
    functionField_isScalarTower X V ⟨η, hηV⟩
  have hh : algebraMap _ X.functionField y = algebraMap (X.presheaf.stalk η) X.functionField z := h
  obtain ⟨r, hr⟩ := GlobalTheory.PrimeElement.exists_algebraMap_eq (K := X.functionField) hπ.ne_zero hh
  refine ⟨r, hr, fun hy hz => ?_⟩
  obtain ⟨r', hr'u, hr'⟩ :=
    GlobalTheory.PrimeElement.exists_unit_algebraMap_eq (K := X.functionField) hπ.ne_zero hy hz hh
  have hinj := IsLocalization.injective
    (M := Submonoid.powers (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    Γ(X, X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t))
    (powers_le_nonZeroDivisors_of_noZeroDivisors hπ.ne_zero)
  have hrr : r' = r := hinj (hr'.trans hr.symm)
  exact hrr ▸ hr'u
section Cocycle
variable {ι : Type v} {U : ι → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
variable [IsLocallyNoetherian X]
end Cocycle
end GlobalTheory.PrimeSection
end

set_option autoImplicit false
universe u v
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
variable {X : Scheme.{u}} {t : Γ(X, ⊤)} {η : X}
  (hη : ∀ x : X, x ∉ X.basicOpen t ↔ η ⤳ x)
  (hp : ∀ U : X.Opens, IsAffineOpen U → η ∈ U →
    Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
variable [IsIntegral X]
include hη hp
namespace GlobalTheory.PrimeSection
theorem _root_.solution {W : X.Opens} {s : Γ(X, W)}
    (hs : IsUnit (X.presheaf.map (homOfLE (inf_le_left : W ⊓ X.basicOpen t ≤ W)).op s))
    (hsη : η ∈ W → η ∈ X.basicOpen s) : IsUnit s := by
  refine X.toRingedSpace.isUnit_of_isUnit_germ W s fun x hx => ?_
  change IsUnit (X.presheaf.germ W x hx s)
  by_cases hxt : x ∈ X.basicOpen t
  · have hx' : x ∈ W ⊓ X.basicOpen t := ⟨hx, hxt⟩
    rw [← germ_res inf_le_left hx' s]
    exact hs.map _
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW0⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.isOpen
    have hVW : V ≤ W := hVW0
    have hηV : η ∈ V := mem_of_notMem_basicOpen hη hxV hxt
    have hηW : η ∈ W := hVW hηV
    rw [← germ_res hVW hxV s]
    refine IsUnit.map _ ?_
    have hπ := hp V hV hηV
    have hq := primeIdealOf_eq_span hη hp hV hηV
    have hYle : X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) ≤ W ⊓ X.basicOpen t := by
      rw [Scheme.basicOpen_res]
      exact fun y hy => ⟨hVW hy.1, hy.2⟩
    have hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op t) := by
      rw [Scheme.basicOpen_res]
      exact genericPoint_mem_inf hp hηV
    have hres : X.presheaf.map (homOfLE hYle).op (X.presheaf.map (homOfLE inf_le_left).op s) =
        X.presheaf.map (homOfLE (X.basicOpen_le _)).op (X.presheaf.map (homOfLE hVW).op s) := by
      rw [res_res, res_res]
    have hz : IsUnit (X.presheaf.germ V η hηV (X.presheaf.map (homOfLE hVW).op s)) := by
      rw [germ_res]
      exact (X.mem_basicOpen s η hηW).mp (hsη hηW)
    obtain ⟨r, hr, hru⟩ := exists_section_restrict_eq_of_germ_eq hV hηV hπ hq hY
      (X.presheaf.map (homOfLE (X.basicOpen_le _)).op (X.presheaf.map (homOfLE hVW).op s))
      (X.presheaf.germ V η hηV (X.presheaf.map (homOfLE hVW).op s))
      (by rw [algebraMap_germ, germ_res, germ_res])
    have hinj : r = X.presheaf.map (homOfLE hVW).op s := by
      have : Nonempty V := ⟨⟨η, hηV⟩⟩
      refine eq_of_germ_eq fun hgV => ?_
      rw [← germ_res (X.basicOpen_le _) hY r, hr, germ_res]
    rw [← hinj]
    refine hru ?_ hz
    rw [← hres]
    exact hs.map _
end GlobalTheory.PrimeSection
