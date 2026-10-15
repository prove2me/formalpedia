-- Prove2me | solution 1 for OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:21:15.512207+00:00
-- url     : https://prove2.me/submissions/cb80a89e-3910-4995-8b18-d8bc217ea310

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/GlobalSpecialization.lean:L231-L276
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_LogKodairaFiberNegative
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Basic
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Adjunction
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_BaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_RelativeCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_Specialization
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LocalCanonical
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_FiberCharts
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_LatticeBaseChange
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_GlobalSpecialization
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_NumeratorChart_exists_near_fiber_point
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_local_specialization_regular
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_specialization_refinement
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_ReducedSNCBoundary_isLogPluriform_local_iff
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_fiber_boundary_equation_ne_zero

-- ---- from OAI.AlgebraicGeometry.LogKodaira.BoundaryPullback ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.IdealPullback

 
theorem ideal_comap_affine {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (I : Y.IdealSheafData) (f : X ⟶ Y) :
    (I.comap f).ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom := by
  have hmap (J : X.IdealSheafData) :
      (J.map f).ideal ⟨⊤, isAffineOpen_top Y⟩ =
        (J.ideal ⟨⊤, isAffineOpen_top X⟩).comap f.appTop.hom := by
    exact J.ideal_map_of_isAffineHom f ⟨⊤, isAffineOpen_top Y⟩
  let eX := Scheme.IdealSheafData.equivOfIsAffine (X := X)
  let J := eX.symm ((I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom)
  have hJ : J.ideal ⟨⊤, isAffineOpen_top X⟩ =
      (I.ideal ⟨⊤, isAffineOpen_top Y⟩).map f.appTop.hom :=
    eX.apply_symm_apply _
  apply le_antisymm
  · have hIJ : I ≤ J.map f := by
      apply Scheme.IdealSheafData.le_of_isAffine
      rw [hmap, hJ]
      exact Ideal.le_comap_map
    have h := (Scheme.IdealSheafData.le_map_iff_comap_le.mp hIJ)
      ⟨⊤, isAffineOpen_top X⟩
    rw [hJ] at h
    exact h
  · rw [Ideal.map_le_iff_le_comap, ← hmap]
    exact (I.le_map_comap f) ⟨⊤, isAffineOpen_top Y⟩

end ReverseLogKodaira.IdealPullback

namespace ReverseLogKodaira.IdealPullback

lemma ideal_restriction_map {X : Scheme} (I : X.IdealSheafData) (U : X.affineOpens) :
    ((I.comap U.1.ι).ideal ⟨⊤, @isAffineOpen_top U.1 U.2⟩).map U.1.topIso.hom.hom = I.ideal U := by
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion]
  simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
  exact I.map_ideal (U := U)
    (V := ⟨U.1.ι ''ᵁ ⊤, (isAffineOpen_top U.1).image_of_isOpenImmersion U.1.ι⟩)
    U.1.ι_image_top.ge

 

theorem ideal_comap_appLE {X Y : Scheme}
    (I : Y.IdealSheafData) (f : X ⟶ Y)
    (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1) :
    (I.comap f).ideal V = (I.ideal U).map (f.appLE U.1 V.1 e).hom := by
  let : IsAffine U.1 := U.2
  let : IsAffine V.1 := V.2
  have hc : (I.comap f).comap V.1.ι = (I.comap U.1.ι).comap (f.resLE U.1 V.1 e) := by
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
      Scheme.Hom.resLE_comp_ι]
  rw [← ideal_restriction_map (I.comap f) V, hc, ideal_comap_affine]
  rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.hom_comp, Ideal.map_map, ← RingHom.comp_assoc]
  rw [← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id,
    RingHom.id_comp, ← Ideal.map_map, ideal_restriction_map]

end ReverseLogKodaira.IdealPullback

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI

-- ---- from OAI.AlgebraicGeometry.LogKodaira.GlobalSpecialization ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange

 
end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

 

namespace NumeratorChart
variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange LogarithmicSpecialization

namespace NumeratorChart

end NumeratorChart
end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization.NumeratorChart
open SmoothProjectiveVariety DifferentialBaseChange

variable {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
  {f : BoundaryFibration X Y E D} {y : Y.ComplexPoint} {F : FiberModel f y}
  {U : Y.scheme.affineOpens} {hdim : X.dimension = Y.dimension + F.variety.dimension}
  {m : ℕ} {s : X.RationalPluriform m}

lemma value_eq_of_refinement (P Q : NumeratorChart f y F U hdim m s)
    (hV : Q.V.1 ≤ P.V.1) (hy : y.point ∈ U.1)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) : P.value hy b = Q.value hy b := by
  let := P.nonempty
  let := Q.nonempty
  let := P.fiberNonempty
  let := Q.fiberNonempty
  exact specialization_refinement f y F U hy P.V Q.V P.overOpen hV
    P.formallySmooth Q.formallySmooth Y.dimension F.variety.dimension m b
    P.relativeBasis Q.relativeBasis P.equation Q.equation
    (fiber_boundary_equation_ne_zero f y F P.V P.equation P.ideal_eq)
    (fiber_boundary_equation_ne_zero f y F Q.V Q.equation Q.ideal_eq)
    P.numerator Q.numerator (P.source_eq.trans Q.source_eq.symm)

end ReverseLogKodaira.FiberChartSpecialization.NumeratorChart

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

lemma NumeratorChart.value_eq
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1)))
    (P Q : NumeratorChart f.toBoundaryFibration y F U hdim m s) :
    P.value hy b = Q.value hy b := by
  let z := genericPoint F.variety.scheme
  have hzP : F.inclusion z ∈ P.V.1 :=
    ((genericPoint_spec F.variety.scheme).mem_open_set_iff (F.inclusion ⁻¹ᵁ P.V.1).2).mpr
      (by simpa using P.fiberNonempty)
  have hzQ : F.inclusion z ∈ Q.V.1 :=
    ((genericPoint_spec F.variety.scheme).mem_open_set_iff (F.inclusion ⁻¹ᵁ Q.V.1).2).mpr
      (by simpa using Q.fiberNonempty)
  obtain ⟨R, _, hR⟩ := NumeratorChart.exists_near_fiber_point f U hU y hy F hdim m s hs
    (P.V.1 ⊓ Q.V.1) z ⟨hzP, hzQ⟩
  exact (P.value_eq_of_refinement R (fun x hx => (hR hx).1) hy b).trans
    (Q.value_eq_of_refinement R (fun x hx => (hR hx).2) hy b).symm

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

theorem exists_global_specialization
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) :
    ∃ σ : F.variety.RationalPluriform m, σ ∈ F.boundary.sections m ∧
      ∀ P : NumeratorChart f.toBoundaryFibration y F U hdim m s, P.value hy b = σ := by
  classical
  obtain ⟨P, _, _⟩ := NumeratorChart.exists_near_fiber_point f U hU y hy F hdim m s hs
    ⊤ (genericPoint F.variety.scheme) (by trivial)
  refine ⟨P.value hy b, ?_, fun Q => NumeratorChart.value_eq f U hU y hy F hdim m s hs b Q P⟩
  change F.boundary.IsLogPluriform m (P.value hy b)
  apply (F.boundary.isLogPluriform_local_iff m (P.value hy b)).mpr
  intro z
  obtain ⟨Q, hzQ, _⟩ := NumeratorChart.exists_near_fiber_point f U hU y hy F hdim m s hs
    ⊤ z (by trivial)
  let := Q.fiberNonempty
  let W : F.variety.scheme.affineOpens := ⟨F.inclusion ⁻¹ᵁ Q.V.1,
    (fiber_affine_chart_pushout f.toBoundaryFibration y F U hy Q.V Q.overOpen).1⟩
  let tW : Γ(F.variety.scheme, W.1) := F.inclusion.app Q.V.1 Q.equation
  have htK := fiber_boundary_equation_ne_zero f.toBoundaryFibration y F Q.V
    Q.equation Q.ideal_eq
  have htW : tW ≠ 0 := by
    intro ht
    apply htK
    change algebraMap Γ(F.variety.scheme, W.1) F.variety.scheme.functionField tW = 0
    rw [ht, map_zero]
  have hIW : F.boundary.ideal.ideal W = Ideal.span {tW} := by
    rw [F.boundary_pullback,
      IdealPullback.ideal_comap_appLE E.ideal F.inclusion Q.V W le_rfl,
      Q.ideal_eq, Ideal.map_span]
    simp only [Set.image_singleton]
    change Ideal.span {(F.inclusion.appLE Q.V.1 (F.inclusion ⁻¹ᵁ Q.V.1) le_rfl).hom
      Q.equation} = _
    rw [Scheme.Hom.appLE_eq_app]
  refine ⟨W, Q.fiberNonempty, hzQ, tW, htW, hIW, ?_⟩
  have hreg := local_specialization_regular f.toBoundaryFibration y F U hy Q.V Q.overOpen
    Q.formallySmooth Y.dimension m b Q.relativeBasis Q.equation htK Q.numerator
  change (algebraMap Γ(F.variety.scheme, W.1) F.variety.scheme.functionField tW)^m •
    Q.value hy b ∈ F.variety.regularPluriformLattice W m at hreg
  rw [NumeratorChart.value_eq f U hU y hy F hdim m s hs b Q P] at hreg
  exact hreg

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.FiberChartSpecialization
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open SmoothProjectiveVariety DifferentialBaseChange

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.affineOpens) (hU : U.1 ≤ D.complement)
    (y : Y.ComplexPoint) (hy : y.point ∈ U.1) (F : FiberModel f.toBoundaryFibration y)
    (hdim : X.dimension = Y.dimension + F.variety.dimension)
    (m : ℕ) (s : X.RationalPluriform m) (hs : s ∈ E.sections m)
    (b : Module.Basis (Fin Y.dimension) Γ(Y.scheme, U.1)
      (KaehlerDifferential ℂ Γ(Y.scheme, U.1))) :
    ∃ σ : F.variety.RationalPluriform m, σ ∈ F.boundary.sections m ∧
      ∀ P : NumeratorChart f.toBoundaryFibration y F U hdim m s, P.value hy b = σ := by
  first
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization f U hU y hy F hdim m s hs b
    | exact OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization
    | (apply OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.FiberChartSpecialization.exists_global_specialization <;> assumption)
