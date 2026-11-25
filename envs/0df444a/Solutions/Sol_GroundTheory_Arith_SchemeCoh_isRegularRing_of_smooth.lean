-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.isRegularRing_of_smooth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:06:38.404965+00:00
-- url     : https://prove2.me/submissions/d9390a9d-59cd-433e-86c5-da8c589f3a05

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularLocalDomain
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_RegularSmooth
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_isRegularLocalRing_localization_of_etale

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open IsLocalRing
universe u
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (k A : Type*) [CommRing k] [IsRegularRing k] [CommRing A]
    [Algebra k A] [Algebra.Smooth k A] : IsRegularRing A := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  rw [isRegularRing_iff]
  intro q hq
  obtain ⟨s, hs, hstd⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth (R := k) (S := A)
  obtain ⟨f, hfs, hfq⟩ : ∃ f ∈ s, f ∉ q := by
    by_contra! hc
    exact hq.ne_top (top_le_iff.mp (hs ▸ Ideal.span_le.mpr hc))
  obtain ⟨q', hq', hcomap⟩ : ∃ q' : Ideal (Localization.Away f), q'.IsPrime ∧
      q'.comap (algebraMap A (Localization.Away f)) = q := by
    have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime (I := q) f).mpr hfq
    exact ⟨q.map (algebraMap A (Localization.Away f)),
      IsLocalization.isPrime_of_isPrime_disjoint (.powers f) _ q hq hdisj,
      IsLocalization.under_map_of_isPrime_disjoint (.powers f) _ hq hdisj⟩
  subst hcomap
  suffices IsRegularLocalRing (Localization.AtPrime q') from
    IsRegularLocalRing.of_ringEquiv
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q').toRingEquiv.symm
  have hf := hstd f hfs
  obtain ⟨n, g, -, hg⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap k (Localization.Away f))
    (RingHom.isStandardSmooth_algebraMap.mpr hf)
  algebraize [g]
  exact isRegularLocalRing_localization_of_etale (P := MvPolynomial (Fin n) k) q'
end GroundTheory.Arith.SchemeCoh
