-- Prove2me | solution 1 for MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.parameter_basicOpen
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-17T06:54:40.21626+00:00
-- url     : https://prove2.me/submissions/17945709-c4c3-4646-8b69-ba70aa5f533f

/- Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: the chosen actual first-chart parameter cuts out the ordinary parameter-localization image on the actual curve.
Named downstream consumers: first overlap basic-open field and unchanged integral FiniteMapData. Uses the existing Proved public ordinary-localization equivalence with its literal inclusion compatibility. -/
import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartSections
import Definitions.Def_MazurTransfer_Order13InverseChartOpen
import Theorems.Thm_MazurTransfer_order13_actual_single_section_ordinary_localization_charts
import Theorems.Thm_MazurTransfer_ActualAffineSectionRingBasicOpenTransport_basicOpen_transport
noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Polynomial
open MazurTorsion.XOneThirteenAffineCurve MazurTorsion.XOneThirteenProjectiveCurve
open scoped MazurTransfer.Order13SingleSectionFiniteAlgebra
open scoped MazurTransfer.Order13FirstFiniteChartFromPublicTheorem
open MazurTransfer.Order13FirstFiniteChartFromPublicTheorem

theorem solution (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    (curveScheme R).basicOpen (parameterSection R h104) =
      (MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryParameterCurveMap R).opensRange := by
  obtain ⟨tB, pB, qB, ht, hp, hq, κ, κ₂, hκ, hκ₂, hcover⟩ :=
    MazurTransfer.order13_actual_single_section_ordinary_localization_charts R
  have ht' : tB = parameterElement R := by
    apply Subtype.ext
    exact ht.trans (parameterElement_value R).symm
  subst tB
  let B := MazurTransfer.Order13SingleSectionFiniteAlgebra.candidateAlgebra R
  let L := Localization.Away (parameterElement R)
  let Ω := MazurTransfer.Order13SingleSectionFiniteAlgebra.ordinaryParameterLocalization R
  let κr : L ≃+* Ω := @AlgEquiv.toRingEquiv R _ _ _ _ _ _ _ κ
  let k : Spec (.of Ω) ≅ Spec (.of L) :=
    Scheme.Spec.mapIso κr.toCommRingCatIso.op
  let locB : Spec (.of L) ⟶ Spec (.of B) :=
    Spec.map (CommRingCat.ofHom (algebraMap B L))
  letI : IsOpenImmersion locB := IsOpenImmersion.of_isLocalization (parameterElement R)
  have hr : (k.hom ≫ locB).opensRange = PrimeSpectrum.basicOpen (parameterElement R) := by
    rw [Scheme.Hom.opensRange_comp_of_isIso]
    apply SetLike.ext'
    exact PrimeSpectrum.localization_away_comap_range L (parameterElement R)
  let φ : B →+* Ω := (algebraMap (CoordinateRing R) Ω).comp
    (MazurTransfer.Order13SingleSectionFiniteAlgebra.candidateAlgebra R).val.toRingHom
  have hk : k.hom ≫ locB = Spec.map (CommRingCat.ofHom φ) := by
    change Spec.map (CommRingCat.ofHom κr.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B L)) = _
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro b
    exact hκ b
  have hc : (k.hom ≫ locB) ≫ (specIso R h104).hom ≫ (chartOpen R).ι =
      MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryParameterCurveMap R := by
    rw [hk]
    have hφ : Spec.map (CommRingCat.ofHom φ) =
        Spec.map (CommRingCat.ofHom (algebraMap (CoordinateRing R) Ω)) ≫
          Spec.map (CommRingCat.ofHom
            (MazurTransfer.Order13SingleSectionFiniteAlgebra.candidateAlgebra R).val.toRingHom) := by
      rw [← Spec.map_comp]
      rfl
    rw [hφ, Category.assoc, specIso_ordinary]
    rfl
  refine (MazurTransfer.ActualAffineSectionRingBasicOpenTransport.basicOpen_transport
    (chartOpen R) (specIso R h104) (parameterElement R)).trans ?_
  apply SetLike.ext'
  change Set.image ((specIso R h104).hom ≫ (chartOpen R).ι)
    (PrimeSpectrum.basicOpen (parameterElement R) : Set (PrimeSpectrum B)) =
      Set.range (MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryParameterCurveMap R)
  have hD := congrArg (fun W : (Spec (.of B)).Opens => (W : Set (Spec (.of B)))) hr
  refine (congrArg (Set.image ((specIso R h104).hom ≫ (chartOpen R).ι)) hD.symm).trans ?_
  change Set.image ((specIso R h104).hom ≫ (chartOpen R).ι)
    (Set.range (k.hom ≫ locB)) = _
  rw [← Set.range_comp]
  change Set.range ((k.hom ≫ locB) ≫ (specIso R h104).hom ≫ (chartOpen R).ι) = _
  rw [hc]
#print axioms solution
