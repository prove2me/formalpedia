-- Prove2me | solution 1 for MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.parameter_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:55:26.401809+00:00
-- url     : https://prove2.me/submissions/2a7f4b88-a7a4-4a27-bf4e-9843499aeffb

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the literal inverse parameter section cuts out exactly the ordinary parameter-localization image on the actual curve.
Named downstream consumers: the inverse overlap basic-open field and unchanged integral FiniteMapData. The original inverse basic-open proof is retained for the public section constructor. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartSections
import Theorems.Thm_MazurTransfer_ActualAffineSectionRingBasicOpenTransport_basicOpen_transport
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InverseParameterFiniteAlgebra
theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    (curveScheme R).basicOpen (MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104) =
      (ordinaryParameterCurveMap R).opensRange := by
  let := finiteModelToCurve_isOpenImmersion R h104
  let := ordinaryParameterToFiniteAffineScheme_isOpenImmersion R
  have hr : (ordinaryParameterToFiniteAffineScheme R).opensRange = PrimeSpectrum.basicOpen (sElement R) := by
    apply SetLike.ext'
    exact ordinaryParameterToFiniteAffineScheme_range R
  refine (MazurTransfer.ActualAffineSectionRingBasicOpenTransport.basicOpen_transport
    (inverseChartOpen R) (finiteModelInverseChartIso R h104) (sElement R)).trans ?_
  apply SetLike.ext'
  change Set.image ((finiteModelInverseChartIso R h104).hom ≫ (inverseChartOpen R).ι)
    (PrimeSpectrum.basicOpen (sElement R) : Set (PrimeSpectrum (candidateAlgebra R))) = Set.range (ordinaryParameterCurveMap R)
  have hD := congrArg (fun W : (inverseFiniteAffineScheme R).Opens => (W : Set (inverseFiniteAffineScheme R))) hr
  rw [finiteModelInverseChartIso_hom_ι]
  refine (congrArg (Set.image (finiteModelToCurve R h104)) hD.symm).trans ?_
  change Set.image (finiteModelToCurve R h104)
    (Set.range (ordinaryParameterToFiniteAffineScheme R)) = _
  rw [← Set.range_comp]
  change Set.range (ordinaryParameterToFiniteAffineScheme R ≫ finiteModelToCurve R h104) = _
  rw [ordinaryParameterToFiniteAffineScheme_finiteModelToCurve]
#print axioms solution
