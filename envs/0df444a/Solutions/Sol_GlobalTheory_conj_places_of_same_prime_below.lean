-- Prove2me | solution 1 for GlobalTheory.conj_places_of_same_prime_below
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:22:16.637027+00:00
-- url     : https://prove2.me/submissions/77ffaddc-bb55-49f1-a625-7cc433ae2f1c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ConjPlacesOfSamePrimeBelow
import Theorems.Thm_ReciprocityTheory_Gal_continuousSMul_intCl
import Theorems.Thm_ReciprocityTheory_Gal_eq_of_valuation_lt_one_iff
import Theorems.Thm_ReciprocityTheory_Gal_isInvariant_intCl
import Theorems.Thm_ReciprocityTheory_Gal_primeBelow_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (K : IntermediateField E Ω) [FiniteDimensional E K] (A B : ValuationSubring Ω), (∀ x ∈ K, IsIntegral ℤ x → (A.valuation x < 1 ↔ B.valuation x < 1)) → ∃ ρ : G E Ω, (∀ x ∈ K, ρ x = x) ∧ ρ • A = B := by
  intro E Ω _ _ _ _ _ K _ A B h
  haveI : FiniteDimensional ℚ K := Module.Finite.trans E K
  haveI : NumberField K := ⟨⟩
  haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed E, Algebra.IsAlgebraic.tower_top (K := E) K⟩
  letI : TopologicalSpace (IntCl K Ω) := ⊥
  haveI : DiscreteTopology (IntCl K Ω) := ⟨rfl⟩
  haveI := continuousSMul_intCl K Ω
  haveI := isInvariant_intCl K Ω
  obtain ⟨g, hg⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite (A := 𝓞 K)
    (G := Ω ≃ₐ[K] Ω) (primeBelow (F := K) A) (primeBelow (F := K) B) (by
      ext x
      rw [Ideal.under, Ideal.under, Ideal.mem_comap, Ideal.mem_comap, mem_primeBelow, mem_primeBelow]
      have hK : ((algebraMap (𝓞 K) (IntCl K Ω) x : IntCl K Ω) : Ω) = ((x : K) : Ω) := rfl
      rw [hK]
      refine h _ (x : K).2 ?_
      exact (x.2.map (IsScalarTower.toAlgHom ℤ K Ω)))
  have hgA : g • A = B := by
    refine eq_of_valuation_lt_one_iff K fun b hb => ?_
    let b' : IntCl K Ω := ⟨b, hb.tower_top⟩
    change b' ∈ primeBelow (F := K) (g • A) ↔ b' ∈ primeBelow (F := K) B
    rw [primeBelow_smul, hg]
  refine ⟨g.restrictScalars E, fun x hx => ?_, ?_⟩
  · show g x = x
    exact g.commutes ⟨x, hx⟩
  · rw [← hgA]
    ext y
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    rfl
end GlobalTheory
