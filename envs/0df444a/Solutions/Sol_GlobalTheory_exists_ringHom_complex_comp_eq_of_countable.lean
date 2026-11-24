-- Prove2me | solution 1 for GlobalTheory.exists_ringHom_complex_comp_eq_of_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:10:02.822678+00:00
-- url     : https://prove2.me/submissions/a66299c1-cf3d-4c2e-bf17-c6dc6aa2bbc7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRingHomComplexCompEqOfCountable
import Theorems.Thm_GlobalTheory_nonempty_algHom_complex_of_countable
import Theorems.Thm_GlobalTheory_injective_of_finiteType_int_of_charZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (o : Type) [CommRing o] (em : o →+* ℂ) (K₀ : Type) [Field K₀] [CharZero K₀] [Countable K₀] (β : o →+* K₀), IsDedekindDomain o → Algebra.FiniteType ℤ o → Function.Injective em → Countable o ∧ ∃ j : K₀ →+* ℂ, j.comp β = em := by
  intro o _ em K₀ _ _ _ β hD hF hem
  haveI := hD
  haveI := hF
  have hβ : Function.Injective β := injective_of_finiteType_int_of_charZero β
  have hcount : Countable o := by
    obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 hF
    have hc : Countable (MvPolynomial (Fin n) ℤ) := by
      rw [← Cardinal.mk_le_aleph0_iff]
      exact MvPolynomial.cardinalMk_le_max.trans
        (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)
    exact hf.countable
  refine ⟨hcount, ?_⟩
  haveI := hcount
  letI : Algebra o K₀ := β.toAlgebra
  letI : Algebra o ℂ := em.toAlgebra
  haveI : FaithfulSMul o K₀ := (faithfulSMul_iff_algebraMap_injective o K₀).2 hβ
  haveI : FaithfulSMul o ℂ := (faithfulSMul_iff_algebraMap_injective o ℂ).2 hem
  obtain ⟨g⟩ := nonempty_algHom_complex_of_countable o K₀
  exact ⟨g.toRingHom, RingHom.ext fun x => g.commutes x⟩
end GlobalTheory
