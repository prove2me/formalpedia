-- Prove2me | solution 1 for GlobalTheory.OnePoint.exists_section_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:43:43.335212+00:00
-- url     : https://prove2.me/submissions/9cb19140-e74e-4500-9369-bacb0b4ba7f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsIntegrallyClosedInFractionFieldPowerSeries
import Theorems.Thm_GlobalTheory_OnePoint_exists_algHom_ker_eq_nilradical

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped LaurentSeries PowerSeries
open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.OnePoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K : Type u} [Field K]
namespace GlobalTheory.OnePoint
theorem _root_.solution [PerfectField K] {F : Scheme.{u}} (f : F ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (Ω : Type u) [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (h : ∀ a b : Spec (.of Ω) ⟶ F, a ≫ f = specAlg(K, Ω) → b ≫ f = specAlg(K, Ω) → a = b)
    (p : F) : ∃ s : Spec (.of K) ⟶ F, s ≫ f = 𝟙 _ ∧ p ∈ Set.range s := by
  obtain ⟨A, i, _, q, rfl⟩ := Scheme.exists_Spec_apply_eq p
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (i ≫ f)
  have hft : φ.hom.FiniteType := by
    have : LocallyOfFiniteType (Spec.map φ) := hφ ▸ inferInstance
    exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp this
  let : Algebra K A := φ.hom.toAlgebra
  have : Algebra.FiniteType K A := hft
  have : Nontrivial A := PrimeSpectrum.nonempty_iff_nontrivial.mp ⟨q⟩
  have hcomp : ∀ (L : Type u) [Field L] [Algebra K L] (a : A →ₐ[K] L),
      (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ i) ≫ f = specAlg(K, L) := fun L _ _ a ↦ by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]
    congr 1
    ext c
    exact a.commutes c
  obtain ⟨ψ, hψ⟩ := exists_algHom_ker_eq_nilradical (K := K) (A := A) Ω fun a b ↦ by
    have := Spec.map_injective ((cancel_mono i).mp (h _ _ (hcomp Ω a) (hcomp Ω b)))
    exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom this)
  refine ⟨Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ i, ?_, ⟨⊥, Ideal.isPrime_bot⟩, ?_⟩
  · rw [hcomp K ψ]
    simp
  · refine (Scheme.Hom.comp_apply _ _ _).trans (congrArg i ?_)
    apply PrimeSpectrum.ext
    have hmax : (RingHom.ker ψ).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective ψ fun c ↦ ⟨algebraMap K A c, ψ.commutes c⟩
    have := q.isPrime
    exact hmax.eq_of_le q.isPrime.ne_top (hψ ▸ nilradical_le_prime q.asIdeal)
end GlobalTheory.OnePoint
