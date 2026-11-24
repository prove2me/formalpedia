-- Prove2me | solution 1 for GlobalTheory.PrimeSection.exists_res_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:35:56.742489+00:00
-- url     : https://prove2.me/submissions/32975387-ba01-4687-a3e2-c38cd7c1c48f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUnitAlgebraMapEqOfValuationEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Theorems.Thm_GlobalTheory_PrimeSection_germ_res
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
include hη
namespace GlobalTheory.PrimeSection
theorem _root_.solution {W : X.Opens} (r : Γ(X, W ⊓ X.basicOpen t))
    (hr : ∀ h : η ∈ W, ∃ z : X.presheaf.stalk η, algebraMap _ X.functionField z =
      X.presheaf.germ _ (genericPoint X) (genericPoint_mem_inf hp h) r) :
    ∃ s : Γ(X, W), X.presheaf.map (homOfLE inf_le_left).op s = r := by
  classical

  have hloc : ∀ x : {x // x ∈ W ∧ x ∉ X.basicOpen t}, ∃ V : X.Opens, IsAffineOpen V ∧ x.1 ∈ V ∧ V ≤ W := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open x.2.1 W.isOpen
    exact ⟨V, hV, hxV, hVW⟩
  choose V hV hxV hVW using hloc
  have hηV : ∀ x, η ∈ V x := fun x => mem_of_notMem_basicOpen hη (hxV x) x.2.2

  have hsec : ∀ x, ∃ sx : Γ(X, V x), X.presheaf.germ (V x) (genericPoint X) (genericPoint_mem (hxV x)) sx =
      X.presheaf.germ _ (genericPoint X) (genericPoint_mem_inf hp (hVW x (hηV x))) r := by
    intro x
    have hπ := hp (V x) (hV x) (hηV x)
    have hq := primeIdealOf_eq_span hη hp (hV x) (hηV x)
    have hYle : X.basicOpen (X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op t) ≤ W ⊓ X.basicOpen t := by
      rw [Scheme.basicOpen_res]
      exact fun y hy => ⟨hVW x hy.1, hy.2⟩
    have hY : genericPoint X ∈ X.basicOpen (X.presheaf.map (homOfLE (le_top : V x ≤ ⊤)).op t) := by
      rw [Scheme.basicOpen_res]
      exact genericPoint_mem_inf hp (hηV x)
    obtain ⟨z, hz⟩ := hr (hVW x (hηV x))
    obtain ⟨sx, hsx, -⟩ := exists_section_restrict_eq_of_germ_eq (hV x) (hηV x) hπ hq hY
      (X.presheaf.map (homOfLE hYle).op r) z (by rw [germ_res]; exact hz.symm)
    refine ⟨sx, ?_⟩
    rw [← germ_res (X.basicOpen_le _) hY sx, hsx, germ_res]
  choose sx hsx using hsec

  let O : Option {x // x ∈ W ∧ x ∉ X.basicOpen t} → X.Opens := fun i => i.elim (W ⊓ X.basicOpen t) V
  let f : ∀ i, Γ(X, O i) := fun i => Option.rec (motive := fun i => Γ(X, O i)) r sx i
  have hOW : ∀ i, O i ≤ W := by
    intro i
    cases i with
    | none => exact inf_le_left
    | some x => exact hVW x
  have hcov : W ≤ iSup O := by
    intro y hy
    by_cases hyt : y ∈ X.basicOpen t
    · exact (le_iSup O none) ⟨hy, hyt⟩
    · exact (le_iSup O (some ⟨y, hy, hyt⟩)) (hxV ⟨y, hy, hyt⟩)
  have hgD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hgerm : ∀ i (hi : genericPoint X ∈ O i), X.presheaf.germ (O i) (genericPoint X) hi (f i) =
      X.presheaf.germ _ (genericPoint X) (⟨hOW i hi, hgD⟩ : genericPoint X ∈ W ⊓ X.basicOpen t) r := by
    intro i hi
    cases i with
    | none => rfl
    | some x => exact hsx x
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 O f := by
    intro i j
    refine eq_of_germ_eq fun hij => ?_
    change X.presheaf.germ _ _ hij (X.presheaf.map (Opens.infLELeft (O i) (O j)).op (f i)) =
      X.presheaf.germ _ _ hij (X.presheaf.map (Opens.infLERight (O i) (O j)).op (f j))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hgerm i, hgerm j]
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' O W (fun i => homOfLE (hOW i)) hcov f hcompat
  exact ⟨s, hs none⟩
end GlobalTheory.PrimeSection
