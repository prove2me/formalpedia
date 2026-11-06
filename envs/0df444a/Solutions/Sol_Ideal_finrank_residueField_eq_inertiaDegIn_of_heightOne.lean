-- Prove2me | solution 1 for Ideal.finrank_residueField_eq_inertiaDegIn_of_heightOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:40:19.903196+00:00
-- url     : https://prove2.me/submissions/d26c5c27-6a96-439b-94a5-f2a00b200175

import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_HeightOneQuotientResidue
import Mathlib.NumberTheory.RamificationInertia.Galois
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Places_ResidueFinrankInertia
import Theorems.Thm_Ideal_finrank_eq_inertiaDegIn_of_quotient_equivs

set_option autoImplicit false
open Ideal
noncomputable section
namespace Ideal
theorem _root_.solution
    {k O C K G : Type*} [Field k] [Finite k]
    [CommRing O] [IsDedekindDomain O] [CommRing C] [IsDedekindDomain C]
    [Algebra O C] [Module.Finite O C]
    [Field K] [Algebra C K] [IsFractionRing C K]
    [Group G] [Finite G] [MulSemiringAction G C] [IsGaloisGroup G O C]
    (p : Ideal O) [p.IsMaximal]
    (H : IsDedekindDomain.HeightOneSpectrum C)
    (hH : H.asIdeal.LiesOver p)
    (v : Valuation K (WithZero (Multiplicative ℤ)))
    [Algebra k (IsLocalRing.ResidueField v.valuationSubring)]
    [FiniteDimensional k (IsLocalRing.ResidueField v.valuationSubring)]
    (baseEquiv : k ≃+* (O ⧸ p)) (hv : H.valuation K = v) :
    Module.finrank k (IsLocalRing.ResidueField v.valuationSubring) =
      p.inertiaDegIn C := by
  let P : p.primesOver C := ⟨H.asIdeal, H.isPrime, hH⟩
  letI : P.1.IsMaximal := by
    change H.asIdeal.IsMaximal
    infer_instance
  let upperEquiv : (C ⧸ P.1) ≃+*
      IsLocalRing.ResidueField v.valuationSubring := by
    change (C ⧸ H.asIdeal) ≃+*
      IsLocalRing.ResidueField v.valuationSubring
    exact (H.quotientResidueEquivValuation (K := K)).trans
      (Valuation.residueFieldEquivOfEq (H.valuation K) v hv)
  exact finrank_eq_inertiaDegIn_of_quotient_equivs
    (G := G) p P baseEquiv upperEquiv
end Ideal
