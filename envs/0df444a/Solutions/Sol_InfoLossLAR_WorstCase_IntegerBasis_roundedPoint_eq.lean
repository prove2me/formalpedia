-- Prove2me | solution 1 for InfoLossLAR.WorstCase.IntegerBasis.roundedPoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T02:17:34.639616+00:00
-- url     : https://prove2.me/submissions/3ee4f6ed-5c33-4d12-b5f1-ec14469dcf48

import Definitions.Def_InfoLossLAR_BDD_Coordinates

set_option autoImplicit false

/-! # Executable Gaussian weights at arbitrary rational centers

The denominator of the rational center is cleared exactly. The resulting
program calls the proved rational pi/exponential routine; it does not
invoke a real floor, square root, or Gaussian oracle.
-/

namespace AFT.RationalNumerics

/-- This integer translation is computed from rational numerator and
denominator. Later scalar draws use bounded offsets from this anchor. -/
def centeredGaussianAnchor (center : ℚ) : ℤ := ⌊center⌋

noncomputable section

set_option backward.isDefEq.respectTransparency false

end

end AFT.RationalNumerics



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native

open AFT GaussianSource RationalNumerics BinaryArithmetic

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open Integration9_9 TM2NativeFiniteSeries TM2NativeGaussian

open scoped BigOperators

theorem anchor_eq (center : ℚ) : anchor center=(centeredGaussianAnchor center : ℚ) := by
  unfold anchor
  split <;> rename_i hc
  · have hn := Int.natCast_ceil_eq_ceil (neg_nonneg.mpr hc.le)
    rw [←Int.cast_natCast,hn,Int.ceil_neg,Int.cast_neg,neg_neg]
    rfl
  · rw [←Int.cast_natCast,Int.natCast_floor_eq_floor (le_of_not_gt hc)]
    rfl

end InfoLossLAR.WorstCase.GaussianRandomizedRounding.Native



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open scoped BigOperators

open GaussianProjection

noncomputable section

variable {dimension : ℕ}

theorem integerBasis_apply (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0) (index : Fin dimension) :
    (integerBasis basis hdet index : Space (dimension:=dimension))=WithLp.toLp 2 (fun row => (basis row index : ℝ)) := by
  exact (Module.Basis.restrictScalars_apply ℤ (realBasis basis hdet) index).trans (realBasis_apply basis hdet index)

theorem projection_spec (basis : Matrix (Fin dimension) (Fin dimension) ℤ)
    (query : Fin dimension → ℚ) (value : Fin dimension → ℤ) :
    (projection basis query value : ℝ)=inner ℝ (rationalPoint query) (latVec basis value) := by
  unfold projection rationalPoint latVec
  rw [PiLp.inner_apply]
  push_cast
  simp only [Real.inner_apply]

end

end InfoLossLAR.WorstCase.IntegerBasis



set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace InfoLossLAR.WorstCase.IntegerBasis

open RegevLWE.GaussConv GaussianProjection GaussianProjection.CosetGeometry

open AFT GaussianSource GaussianRandomizedRounding

open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic

open scoped BigOperators

noncomputable section

variable {dimension : ℕ}

theorem queryCoordinate_spec (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (query : Fin dimension → ℚ) (index : Fin dimension) :
    (queryCoordinate basis query index : ℝ)=
      inner ℝ (rationalPoint query) (integerBasis basis hdet index : Space (dimension:=dimension)) := by
  rw [queryCoordinate,projection_spec,integerBasis_apply]
  congr 1
  unfold latVec
  rw [Matrix.mulVec_single]
  simp only [MulOpposite.op_one,one_smul]
  rfl

theorem nearestInteger_eq (center : ℚ) : nearestInteger center=⌊center+1/2⌋ := by
  simp only [nearestInteger,GaussianRandomizedRounding.Native.anchor_eq,RationalNumerics.centeredGaussianAnchor,Rat.num_intCast]

/-- A rigorous stopping test uses the full Euclidean error and each
original input-column norm. No coefficient accuracy is silently assumed. -/
theorem roundedCoordinates_eq (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (query : Fin dimension → ℚ) (nearest : dual (inputLattice basis hdet))
    (hsmall : ∀ index : Fin dimension,
      ‖rationalPoint query-(nearest : Space (dimension:=dimension))‖*
        ‖(integerBasis basis hdet index : Space (dimension:=dimension))‖ < 1/2) :
    roundedCoordinates basis query=fun index => pairing (inputLattice basis hdet) nearest (integerBasis basis hdet index) := by
  funext index
  have hclose : |(queryCoordinate basis query index : ℝ)-
      (pairing (inputLattice basis hdet) nearest (integerBasis basis hdet index) : ℝ)|<1/2 := by
    rw [queryCoordinate_spec basis hdet,pairing_spec,←inner_sub_left]
    exact (abs_real_inner_le_norm _ _).trans_lt (hsmall index)
  change nearestInteger (queryCoordinate basis query index)=_
  rw [nearestInteger_eq]
  apply Int.floor_eq_iff.mpr
  constructor
  · have h := (abs_lt.mp hclose).1
    have he : (pairing (inputLattice basis hdet) nearest (integerBasis basis hdet index) : ℝ) ≤
        (queryCoordinate basis query index : ℝ)+1/2 := by linarith
    apply (Rat.cast_le (K:=ℝ)).mp
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_intCast] using he
  · have h := (abs_lt.mp hclose).2
    have he : (queryCoordinate basis query index : ℝ)+1/2 <
        (pairing (inputLattice basis hdet) nearest (integerBasis basis hdet index) : ℝ)+1 := by linarith
    apply (Rat.cast_lt (K:=ℝ)).mp
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_intCast] using he

end

end InfoLossLAR.WorstCase.IntegerBasis



open InfoLossLAR.WorstCase InfoLossLAR.WorstCase.IntegerBasis
open RegevLWE.GaussConv InfoLossLAR.WorstCase.GaussianProjection InfoLossLAR.WorstCase.GaussianProjection.CosetGeometry

theorem solution {dimension : ℕ} (basis : Matrix (Fin dimension) (Fin dimension) ℤ) (hdet : basis.det≠0)
    (query : Fin dimension → ℚ) (nearest : dual (inputLattice basis hdet))
    (hsmall : ∀ index : Fin dimension,
      ‖rationalPoint query-(nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖*
        ‖(integerBasis basis hdet index : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))‖ < 1/2) :
    roundedPoint basis hdet query=nearest := by
  apply Subtype.ext
  change dualCoordinates basis hdet (roundedCoordinates basis query)=(nearest : InfoLossLAR.WorstCase.IntegerBasis.Space (dimension:=dimension))
  rw [roundedCoordinates_eq basis hdet query nearest hsmall,dualCoordinates_pairing]
