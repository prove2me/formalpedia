-- Prove2me | solution 1 for GlobalTheory.exists_splitting_vector
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:47:01.139152+00:00
-- url     : https://prove2.me/submissions/f853385e-8a38-4cc0-9b48-489af73cd048

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsSmulMemOfMemSpanFraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]
namespace GlobalTheory
theorem _root_.solution {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set V) = ⊤) (l : V →ₗ[K] K) (hl : l ≠ 0) :
    ∃ (c : FractionalIdeal R⁰ K) (e : V), c ≠ 0 ∧ l e = 1 ∧ (∀ v ∈ Λ, l v ∈ c) ∧
      ∀ x ∈ c, x • e ∈ Λ := by
  have hfg' : (Λ.map (l.restrictScalars R)).FG := hfg.map _
  let c : FractionalIdeal R⁰ K := ⟨Λ.map (l.restrictScalars R), FractionalIdeal.isFractional_of_fg hfg'⟩
  have hc : ∀ x, x ∈ c ↔ ∃ v ∈ Λ, l v = x := fun x => Iff.rfl
  have hc0 : c ≠ 0 := by
    intro h
    apply hl
    refine LinearMap.ext_on hsp ?_
    intro v hv
    have : l v ∈ c := (hc _).2 ⟨v, hv, rfl⟩
    rw [h] at this
    simpa using this
  have h1 : (1 : K) ∈ c * c⁻¹ := by
    rw [mul_inv_cancel₀ hc0]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ y ∈ c * c⁻¹, ∃ e : V, l e = y ∧ ∀ x ∈ c, x • e ∈ Λ := by
    intro y hy
    refine FractionalIdeal.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨v, hv, rfl⟩ := (hc _).1 ha
      refine ⟨b • v, by simp [mul_comm], ?_⟩
      intro x hx
      have : x * b ∈ c * c⁻¹ := FractionalIdeal.mul_mem_mul hx hb
      rw [mul_inv_cancel₀ hc0, FractionalIdeal.mem_one_iff] at this
      obtain ⟨t, ht⟩ := this
      rw [smul_smul, ← ht, algebraMap_smul]
      exact Λ.smul_mem _ hv
    · rintro a b ⟨e, he, he'⟩ ⟨f, hf, hf'⟩
      refine ⟨e + f, by simp [he, hf], ?_⟩
      intro x hx
      rw [smul_add]
      exact Λ.add_mem (he' x hx) (hf' x hx)
  obtain ⟨e, he, he'⟩ := key 1 h1
  exact ⟨c, e, hc0, he, fun v hv => (hc _).2 ⟨v, hv, rfl⟩, he'⟩
end GlobalTheory
