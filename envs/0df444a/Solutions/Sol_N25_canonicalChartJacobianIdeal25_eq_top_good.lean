-- Prove2me | solution 1 for N25.canonicalChartJacobianIdeal25_eq_top_good
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:30:54.337235+00:00
-- url     : https://prove2.me/submissions/0765c9aa-575c-48e2-8a44-3ac998d56853

import Definitions.Def_N25_CanonicalThreeNormalization
import Definitions.Def_N25_CanonicalNormalizedPoints
import Definitions.Def_N25_NormalizedPointPivot
import Theorems.Thm_N25_canonicalJacobianMinor25_eval
import Theorems.Thm_N25_canonicalChartPoint25_exists_minor_good

/-! Structural Jacobian certificates for the canonical curve in both good characteristics. -/

namespace MazurProof.RationalPointsN25QuotientSmoothF2

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

end MazurProof.RationalPointsN25QuotientSmoothF2

namespace MazurProof.RationalPointsN25QuotientSmoothF3

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThree

open MazurProof.RationalPointsN25QuotientWeilThreeLinear

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

open MazurProof.RationalPointsN25QuotientSmallThreeSemantic

end MazurProof.RationalPointsN25QuotientSmoothF3

namespace N25

open scoped BigOperators

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientWeil

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

open scoped BigOperators

open MazurProof.RationalPointsN25QuotientF2

open MazurProof.RationalPointsN25QuotientKummerThreeProjective

end N25

namespace N25

private theorem canonicalQuadricGradient25_hom {K L : Type*} [CommRing K] [CommRing L]
    (f : MvPolynomial (Fin 4) K →+* L) (j : Fin 4) :
    f (MvPolynomial.pderiv j (canonicalQuadric
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3))) =
      canonicalQuadricGradient25 (fun a => f (MvPolynomial.X a)) j := by
  fin_cases j <;> simp [canonicalQuadric, canonicalQuadricGradient25, map_ofNat] <;> ring

private theorem canonicalCubicGradient25_hom {K L : Type*} [CommRing K] [CommRing L]
    (f : MvPolynomial (Fin 4) K →+* L) (j : Fin 4) :
    f (MvPolynomial.pderiv j (canonicalCubic
      (MvPolynomial.X 0) (MvPolynomial.X 1) (MvPolynomial.X 2) (MvPolynomial.X 3))) =
      canonicalCubicGradient25 (fun a => f (MvPolynomial.X a)) j := by
  fin_cases j <;> simp [canonicalCubic, canonicalCubicGradient25, map_ofNat] <;> ring

private theorem canonicalJacobianMinor25_hom {K L : Type*} [CommRing K] [CommRing L]
    (f : MvPolynomial (Fin 4) K →+* L) (j k : Fin 4) :
    f (canonicalJacobianMinor25 K j k) =
      canonicalQuadricGradient25 (fun a => f (MvPolynomial.X a)) j *
        canonicalCubicGradient25 (fun a => f (MvPolynomial.X a)) k -
      canonicalCubicGradient25 (fun a => f (MvPolynomial.X a)) j *
        canonicalQuadricGradient25 (fun a => f (MvPolynomial.X a)) k := by
  simp only [canonicalJacobianMinor25, map_sub, map_mul,
    canonicalQuadricGradient25_hom, canonicalCubicGradient25_hom]

/-- The non-pivot Jacobian minors generate the unit ideal in every literal
canonical chart over a field of characteristic two or three. -/
theorem _root_.solution
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] (i : Fin 4) :
    canonicalChartJacobianIdeal25 K i = ⊤ := by
  classical
  by_contra hproper
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (canonicalChartJacobianIdeal25 K i) hproper
  letI : m.IsMaximal := hm
  let L := CanonicalChartRing25 K i ⧸ m
  letI : Field L := Ideal.Quotient.field m
  letI : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let η := Ideal.Quotient.mk (canonicalChartIdeal25 K i)
  let φ : CanonicalChartRing25 K i →+* L := Ideal.Quotient.mk m
  let f : MvPolynomial (Fin 4) K →+* L := φ.comp η
  let v : Fin 4 → L := fun j => f (MvPolynomial.X j)
  have hQmem : canonicalQuadric (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3) ∈ canonicalChartIdeal25 K i :=
    Ideal.subset_span (by simp)
  have hCmem : canonicalCubic (MvPolynomial.X 0) (MvPolynomial.X 1)
      (MvPolynomial.X 2) (MvPolynomial.X 3) ∈ canonicalChartIdeal25 K i :=
    Ideal.subset_span (by simp)
  have himem : MvPolynomial.X i - 1 ∈ canonicalChartIdeal25 K i :=
    Ideal.subset_span (by simp)
  have hQ : canonicalQuadric (v 0) (v 1) (v 2) (v 3) = 0 := by
    have hz := congrArg φ (Ideal.Quotient.eq_zero_iff_mem.mpr hQmem)
    simpa [canonicalQuadric, f, v] using hz
  have hC : canonicalCubic (v 0) (v 1) (v 2) (v 3) = 0 := by
    have hz := congrArg φ (Ideal.Quotient.eq_zero_iff_mem.mpr hCmem)
    simpa [canonicalCubic, f, v] using hz
  have hi : v i = 1 := by
    have hz := congrArg φ (Ideal.Quotient.eq_zero_iff_mem.mpr himem)
    have heq : v i - 1 = 0 := by simpa [v, f] using hz
    exact sub_eq_zero.mp heq
  let P : CanonicalChartPoint25 L i := ⟨v, hQ, hC, hi⟩
  obtain ⟨j, k, hj, hk, hjk, hnonzero⟩ :=
    canonicalChartPoint25_exists_minor_good p hp L i P
  have hgen : η (canonicalJacobianMinor25 K j k) ∈ canonicalChartJacobianIdeal25 K i :=
    Ideal.subset_span ⟨j, k, hj, hk, hjk, rfl⟩
  have hz : f (canonicalJacobianMinor25 K j k) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (hle hgen)
  apply hnonzero
  change MvPolynomial.eval v (canonicalJacobianMinor25 L j k) = 0
  rw [canonicalJacobianMinor25_eval]
  change canonicalQuadricGradient25 (fun a => f (MvPolynomial.X a)) j *
      canonicalCubicGradient25 (fun a => f (MvPolynomial.X a)) k -
    canonicalCubicGradient25 (fun a => f (MvPolynomial.X a)) j *
      canonicalQuadricGradient25 (fun a => f (MvPolynomial.X a)) k = 0
  rw [← canonicalJacobianMinor25_hom]
  exact hz

end N25
