-- Prove2me | solution 1 for MvPolynomial.CrossingQuotient.Resolution.locallyOfFiniteType_and_quasiCompact_toCrossing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/8b1d099e-3ea0-5db9-94b5-40e030a77925

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient

open CategoryTheory AlgebraicGeometry MvPolynomial MvPolynomial.CrossingQuotient in
theorem solution
    {W : Type u} [CommRing W] (t : W) (e : ℕ) :
    LocallyOfFiniteType (Resolution.toCrossing t e) ∧ QuasiCompact (Resolution.toCrossing t e) := by
  constructor
  · rw [IsZariskiLocalAtSource.iff_of_openCover (P := @LocallyOfFiniteType) (Resolution.openCover t e)]
    intro i
    have hι := Resolution.ι_toCrossing t e (i : Fin e)
    change LocallyOfFiniteType (Resolution.ι t e (i : Fin e) ≫ Resolution.toCrossing t e)
    rw [hι, HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    change RingHom.FiniteType (resolutionChart t e i).toRingHom
    refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap W (CrossingQuotient W (t ^ e))) ?_
    have hc : (resolutionChart t e i).toRingHom.comp (algebraMap W (CrossingQuotient W (t ^ e))) =
        algebraMap W (CrossingQuotient W t) := RingHom.ext fun w => (resolutionChart t e i).commutes w
    rw [hc, RingHom.finiteType_algebraMap]
    exact Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ W _) (Ideal.Quotient.mkₐ_surjective W _)
  · haveI hc : CompactSpace (chartScheme t) := by
      have h := (isAffineOpen_top (chartScheme t)).isCompact
      exact isCompact_univ_iff.mp (by simpa using h)
    haveI : CompactSpace (Resolution t e) := by
      constructor
      have h : (Set.univ : Set (Resolution t e)) = ⋃ i : Fin e, Set.range (Resolution.ι t e i).base := by
        ext x
        simp only [Set.mem_univ, Set.mem_iUnion, true_iff]
        obtain ⟨i, y, rfl⟩ := Resolution.exists_ι_apply_eq t e x
        exact ⟨i, y, rfl⟩
      rw [h]
      exact isCompact_iUnion fun i => isCompact_range (Resolution.ι t e i).continuous
    exact (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)).mpr ‹CompactSpace (Resolution t e)›

end S_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing
end P2MW
export P2MW.S_MvPolynomial_CrossingQuotient_Resolution_locallyOfFiniteType_and_quasiCompact_toCrossing (solution)
