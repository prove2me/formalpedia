-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Glob.InertiaLift.mem_inertia_of_integers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:35:53.955988+00:00
-- url     : https://prove2.me/submissions/68526fa3-7175-492c-a317-d77a24a03c65

import Mathlib
import Definitions.Def_ReciprocityTheory_Hypotheses_GalCoh
import Definitions.Def_GroundTheory_ProfiniteCohomology_RestrictedRamification_IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GaloisUnramifiedOutsideCohomology
import Theorems.Thm_GroundTheory_ProfCoh_IsUnramifiedOutside_map
import Theorems.Thm_ReciprocityTheory_Gal_exists_den


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual
open scoped Pointwise IntermediateField
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Glob GlobalTheory.CompanionTheory.Glob.InertiaLift
variable {F K Ω : Type*} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
  [Field Ω] [Algebra F Ω] [Algebra K Ω] [IsScalarTower F K Ω]
omit [NumberField K] [Field K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]
namespace GlobalTheory.CompanionTheory.Glob.InertiaLift
theorem _root_.solution [IsAlgClosure F Ω] {A : ValuationSubring Ω} {σ : Ω ≃ₐ[F] Ω}
    (hd : σ • A = A) (hb : ∀ b : Ω, IsIntegral ℤ b → A.valuation (σ b - b) < 1) :
    σ ∈ Inertia (F := F) A := by
  refine ⟨hd, fun x hx => ?_⟩
  have hD : σ ∈ Dec (F := F) A := hd
  obtain ⟨s, t, hs, ht, hs1, e⟩ := exists_den F A hx
  have hvt : A.valuation t ≤ 1 := (A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A ht)
  have hσs : A.valuation (σ s) = 1 := by
    refine le_antisymm ((A.valuation_le_one_iff _).mpr (mem_of_isIntegral_int A
      (hs.map ((σ : Ω ≃ₐ[F] Ω).toAlgHom.restrictScalars ℤ)))) ?_
    refine not_lt.mp fun h => ?_
    have := (valuation_apply_lt_one_iff hD s).1 h
    rw [hs1] at this
    exact lt_irrefl _ this
  have he' : σ s * σ x = σ t := by rw [← map_mul, e]
  have key : s * σ s * (σ x - x) = s * (σ t - t) + t * (s - σ s) := by
    rw [← he', ← e]; ring
  have hv : A.valuation (s * σ s * (σ x - x)) < 1 := by
    rw [key]
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul, hs1, one_mul]
      exact hb t ht
    · rw [Valuation.map_mul, Valuation.map_sub_swap]
      calc A.valuation t * A.valuation (σ s - s) ≤ 1 * A.valuation (σ s - s) :=
            mul_le_mul_left hvt _
        _ < 1 := by rw [one_mul]; exact hb s hs
  rwa [Valuation.map_mul, Valuation.map_mul, hs1, hσs, one_mul, one_mul] at hv
end GlobalTheory.CompanionTheory.Glob.InertiaLift
