-- Prove2me | solution 1 for OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T03:25:33.162163+00:00
-- url     : https://prove2.me/submissions/43f95ddb-d7b9-4336-91fb-f6286b9319c5

-- Generated from openai/math@1581d4c lean/OAI/AlgebraicGeometry/LogKodaira/NonzeroFiber.lean:L449-L522
-- (upload_full_project.md Phase 4): solution for node OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform. The node keeps its source
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
import Definitions.Def_OAI_AlgebraicGeometry_LogKodaira_NonzeroFiber
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_exists_global_specialization
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_fiber_dimension_eq
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_local_logarithmic_numerator
import Theorems.Thm_OAI_ReverseLogKodaira_FiberChartSpecialization_logarithmicNumerator_ne_zero_of_coefficient
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothDimension_smooth_relative_dimension_subtraction
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_exists_relative_log_chart
import Theorems.Thm_OAI_ReverseLogKodaira_SmoothProjectiveVariety_fiber_boundary_equation_ne_zero

-- ---- from OAI.AlgebraicGeometry.LogKodaira.GlobalSpecialization ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.DifferentialBaseChange

 
lemma logarithmicPullback_degreeTransport
    (R B K : Type*) [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra B K] [Algebra R K] [IsScalarTower R B K]
    {n n' : ℕ} (h : n = n') (m : ℕ) (t : B) (q : Pluricanonical R B n m) :
    LogarithmicSpecialization.logarithmicPullback R B K n' m t
      (degreeTransport R B h m q) = degreeTransport R K h m
        (LogarithmicSpecialization.logarithmicPullback R B K n m t q) := by
  subst n'
  rfl

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

end ReverseLogKodaira.FiberChartSpecialization.NumeratorChart

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange

 

end ReverseLogKodaira.FiberChartSpecialization

end

end OAI

-- ---- from OAI.AlgebraicGeometry.LogKodaira.NonzeroFiber ----
namespace OAI

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization
open CanonicalAdjunction DifferentialBaseChange BasedRelativeCanonical

 

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.CanonicalSpecialization

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.FiberChartSpecialization
open SmoothProjectiveVariety DifferentialBaseChange CanonicalSpecialization

 

end ReverseLogKodaira.FiberChartSpecialization

namespace ReverseLogKodaira.RelativeCharts

 

theorem exists_standard_chart_fixed_base
    {X Y : Scheme} (f : X ⟶ Y) (n : ℕ) [SmoothOfRelativeDimension n f]
    (U : Y.affineOpens) (V : X.Opens) (x : X) (hx : x ∈ V)
    (hfx : f x ∈ U.1) :
    ∃ (W : X.affineOpens), x ∈ W.1 ∧ W.1 ≤ V ∧
      ∃ (e : W.1 ≤ f ⁻¹ᵁ U.1),
        RingHom.IsStandardSmoothOfRelativeDimension n (f.appLE U.1 W.1 e).hom := by
  classical
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hx₀, hV₀le⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (V ⊓ f ⁻¹ᵁ U.1 : X.Opens) from ⟨hx, hfx⟩)
      (V ⊓ f ⁻¹ᵁ U.1).isOpen
  have e₀ : V₀ ≤ f ⁻¹ᵁ U.1 := fun z hz => (hV₀le hz).2
  have hlocal := HasRingHomProperty.appLE (@SmoothOfRelativeDimension n) f
    (inferInstance : SmoothOfRelativeDimension n f) U ⟨V₀, hV₀⟩ e₀
  obtain ⟨s, hs, hsm⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).mp hlocal
  let hprime := (hV₀.primeIdealOf ⟨x, hx₀⟩)
  obtain ⟨t, ht, htx⟩ : ∃ t ∈ s, t ∉ hprime.asIdeal := by
    by_contra! hh
    have hle : Ideal.span (s : Set Γ(X, V₀)) ≤ hprime.asIdeal :=
      Ideal.span_le.mpr hh
    rw [hs] at hle
    exact hprime.isPrime.ne_top (top_unique hle)
  have hxB : x ∈ X.basicOpen t := by
    have hm : hV₀.fromSpec (hV₀.primeIdealOf ⟨x, hx₀⟩) ∈ X.basicOpen t := by
      change hV₀.primeIdealOf ⟨x, hx₀⟩ ∈ hV₀.fromSpec ⁻¹ᵁ X.basicOpen t
      rw [hV₀.fromSpec_preimage_basicOpen]
      exact htx
    have he : hV₀.fromSpec (hV₀.primeIdealOf ⟨x, hx₀⟩) = x :=
      hV₀.fromSpec_primeIdealOf ⟨x, hx₀⟩
    exact he ▸ hm
  let e : X.basicOpen t ≤ f ⁻¹ᵁ U.1 := (X.basicOpen_le t).trans e₀
  refine ⟨⟨X.basicOpen t, hV₀.basicOpen t⟩, hxB,
    (X.basicOpen_le t).trans (fun z hz => (hV₀le hz).1), e, ?_⟩
  let := hV₀.isLocalization_basicOpen t
  have h := hsm t ht Γ(X, X.basicOpen t)
  convert h using 1
  exact congrArg CommRingCat.Hom.hom (f.appLE_map e₀ (homOfLE (X.basicOpen_le t)).op).symm

end ReverseLogKodaira.RelativeCharts

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem exists_cotangent_chart (X : SmoothProjectiveVariety)
    (O : X.scheme.Opens) (x : X.scheme) (hx : x ∈ O) :
    ∃ U : X.scheme.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧
      Nonempty (Module.Basis (Fin X.dimension) Γ(X.scheme, U.1)
        (KaehlerDifferential ℂ Γ(X.scheme, U.1))) := by
  classical
  let U₀ : complexBase.affineOpens := ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨U, hxU, hUO, e, hsm⟩ :=
    RelativeCharts.exists_standard_chart_fixed_base X.structural X.dimension U₀ O x hx (by trivial)
  let : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have hsm' : RingHom.IsStandardSmoothOfRelativeDimension X.dimension (X.constants U.1) := by
    have he : RingHom.IsStandardSmoothOfRelativeDimension 0
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom : ℂ →+* Γ(complexBase, ⊤)) := by
      let : Algebra ℂ Γ(complexBase, ⊤) :=
        ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom : ℂ →+* Γ(complexBase, ⊤)).toAlgebra
      exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv)
    have hh := hsm.comp he
    rw [Nat.add_zero] at hh
    convert hh using 1
    ext a
    simp only [constants, globalConstants, RingHom.comp_apply, Scheme.Hom.appTop]
    rfl
  let := hsm'.toAlgebra
  let : Algebra.IsStandardSmooth ℂ Γ(X.scheme, U.1) :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth X.dimension
  have hr : Module.finrank Γ(X.scheme, U.1) (KaehlerDifferential ℂ Γ(X.scheme, U.1)) =
      X.dimension := by
    simp only [Module.finrank,
      Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential X.dimension,
      Cardinal.toNat_natCast]
  exact ⟨U, hxU, hUO, ⟨Module.finBasisOfFinrankEq _ _ hr⟩⟩
end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma ReducedSNCBoundary.generic_mem_complement {X : SmoothProjectiveVariety}
    (E : X.ReducedSNCBoundary) : genericPoint X.scheme ∈ E.complement := by
  change genericPoint X.scheme ∉ E.ideal.support
  intro hg
  have hbot : E.ideal = ⊥ := by
    apply Scheme.IdealSheafData.support_eq_top_iff.mp
    apply eq_top_iff.mpr
    intro z hz
    have hs := closure_minimal (Set.singleton_subset_iff.mpr hg) E.ideal.support.isClosed
    rw [genericPoint_closure] at hs
    exact hs (Set.mem_univ z)
  obtain ⟨V, _, t, ht, hI⟩ := E.union_cartier (genericPoint X.scheme)
  change E.ideal.ideal V = Ideal.span {t} at hI
  rw [hbot] at hI
  change (⊥ : Ideal Γ(X.scheme, V.1)) = Ideal.span {t} at hI
  apply ht
  have hm : t ∈ (⊥ : Ideal Γ(X.scheme, V.1)) := by
    rw [hI]
    exact Ideal.subset_span (Set.mem_singleton t)
  exact hm

lemma generic_mem_basicOpen {X : SmoothProjectiveVariety}
    (V : X.scheme.Opens) [Nonempty V] (a : Γ(X.scheme, V)) (ha : a ≠ 0) :
    genericPoint X.scheme ∈ X.scheme.basicOpen a := by
  have hg : genericPoint X.scheme ∈ V :=
    ((genericPoint_spec X.scheme).mem_open_set_iff V.2).mpr (by simpa using (inferInstance : Nonempty V))
  rw [Scheme.mem_basicOpen _ _ _ hg]
  apply isUnit_iff_ne_zero.mpr
  change X.scheme.germToFunctionField V a ≠ 0
  simpa only [map_zero] using (X.scheme.germToFunctionField_injective V).ne ha

lemma chartToFunctionField_ne_zero_of_mem_basicOpen
    {X F : SmoothProjectiveVariety} (i : F.scheme ⟶ X.scheme)
    (V : X.scheme.Opens) [Nonempty (i ⁻¹ᵁ V)]
    (a : Γ(X.scheme, V)) (z : F.scheme) (hz : i z ∈ X.scheme.basicOpen a) :
    chartToFunctionField i V a ≠ 0 := by
  intro hn
  have hzero : i.app V a = 0 := by
    apply F.scheme.germToFunctionField_injective (i ⁻¹ᵁ V)
    rw [map_zero]
    change chartToFunctionField i V a = 0
    exact hn
  have hz' : z ∈ i ⁻¹ᵁ X.scheme.basicOpen a := hz
  rw [Scheme.Hom.preimage_basicOpen, hzero, Scheme.basicOpen_zero] at hz'
  exact hz'

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety

 

theorem exists_open_meeting_coefficient
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D)
    (U : Y.scheme.Opens) (hU : U ≤ D.complement)
    (V : X.scheme.affineOpens) [Nonempty V.1] (e : V.1 ≤ f.hom ⁻¹ᵁ U)
    (a : Γ(X.scheme, V.1)) (ha : a ≠ 0) :
    ∃ W : Y.scheme.Opens, W ≠ ⊥ ∧ W ≤ U ∧
      ∀ (y : Y.ComplexPoint), y.point ∈ W →
        ∀ F : FiberModel f.toBoundaryFibration y,
          ∃ z : F.variety.scheme, F.inclusion z ∈ X.scheme.basicOpen a := by
  let eD : V.1 ≤ f.hom ⁻¹ᵁ D.complement := fun z hz => hU (e hz)
  let : Smooth (f.hom ∣_ D.complement) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using f.smooth
  let : Smooth (f.hom.resLE D.complement V.1 eD) := by
    unfold Scheme.Hom.resLE
    infer_instance
  let g : V.1.toScheme ⟶ Y.scheme := f.hom.resLE D.complement V.1 eD ≫ D.complement.ι
  let T : V.1.toScheme.Opens := V.1.ι ⁻¹ᵁ X.scheme.basicOpen a
  have hg : g = V.1.ι ≫ f.hom := Scheme.Hom.resLE_comp_ι f.hom eD
  have hW : IsOpen (g '' (T : Set V.1.toScheme)) := g.isOpenMap _ T.2
  let W : Y.scheme.Opens := ⟨g '' (T : Set V.1.toScheme), hW⟩
  have hsrc : genericPoint X.scheme ∈ V.1 := X.scheme.basicOpen_le a (generic_mem_basicOpen V.1 a ha)
  let x : V.1.toScheme := ⟨genericPoint X.scheme, hsrc⟩
  have hxT : x ∈ T := generic_mem_basicOpen V.1 a ha
  refine ⟨W, ?_, ?_, ?_⟩
  · intro hbot
    have hxW : g x ∈ W := ⟨x, hxT, rfl⟩
    rw [hbot] at hxW
    exact hxW
  · rintro w ⟨x, hx, rfl⟩
    rw [hg, Scheme.Hom.comp_apply]
    exact e x.2
  · intro y hy F
    obtain ⟨x, hx, hxy⟩ := hy
    have hxy' : f.hom (V.1.ι x) = y.hom complexBasePoint := by
      change g x = y.hom complexBasePoint at hxy
      rw [hg, Scheme.Hom.comp_apply] at hxy
      exact hxy
    obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback F.square (V.1.ι x)
      complexBasePoint hxy'
    refine ⟨z, ?_⟩
    rw [hz]
    exact hx

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.DifferentialBaseChange

lemma degreeTransport_trans (R B : Type*) [CommRing R] [CommRing B] [Algebra R B]
    {n n' n'' : ℕ} (h : n = n') (h' : n' = n'') (m : ℕ)
    (q : Pluricanonical R B n m) :
    degreeTransport R B h' m (degreeTransport R B h m q) =
      degreeTransport R B (h.trans h') m q := by
  subst n'; subst n''; rfl

end ReverseLogKodaira.DifferentialBaseChange

namespace ReverseLogKodaira.CanonicalSpecialization
open DifferentialBaseChange

lemma pluricanonicalCoordinate_degreeTransport
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FormallySmooth A B] (n r r' m : ℕ) (h : r = r')
    (b : Module.Basis (Fin n) A (KaehlerDifferential R A))
    (c : Module.Basis (Fin r) B (KaehlerDifferential A B))
    (q : Pluricanonical R B (n + r) m) :
    pluricanonicalCoordinate R A B n r' m b (basisDegreeTransport h c)
      (degreeTransport R B (congrArg (n + ·) h) m q) =
        pluricanonicalCoordinate R A B n r m b c q := by
  subst r'; rfl

end ReverseLogKodaira.CanonicalSpecialization

namespace ReverseLogKodaira.SmoothProjectiveVariety

lemma base_dimension_le_of_smooth_point
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (x : X.scheme)
    (hx : f.hom x ∈ D.complement) : Y.dimension ≤ X.dimension := by
  let Q := D.complement
  let P := f.hom ⁻¹ᵁ Q
  let : Nonempty P := ⟨⟨x, hx⟩⟩
  let sP : P.toScheme ⟶ complexBase := P.ι ≫ X.structural
  let sQ : Q.toScheme ⟶ complexBase := Q.ι ≫ Y.structural
  let : SmoothOfRelativeDimension X.dimension sP := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + X.dimension) (P.ι ≫ X.structural))
  let : SmoothOfRelativeDimension Y.dimension sQ := by
    simpa only [Nat.zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + Y.dimension) (Q.ι ≫ Y.structural))
  let : Smooth (f.hom ∣_ Q) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using f.smooth
  have hw : (f.hom ∣_ Q) ≫ sQ = sP := by
    dsimp only [sP, sQ, P, Q]
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc, f.over_base]
  exact (SmoothDimension.smooth_relative_dimension_subtraction
    sP sQ X.dimension Y.dimension (f.hom ∣_ Q) hw).1

end ReverseLogKodaira.SmoothProjectiveVariety

namespace ReverseLogKodaira.SmoothProjectiveVariety
open DifferentialBaseChange CanonicalSpecialization FiberChartSpecialization

 

theorem exists_open_nonzero_fiber_pluriform
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (m : ℕ) (hm : 0 < m)
    (s : X.RationalPluriform m) (hs : s ∈ E.sections m) (hn : s ≠ 0) :
    ∃ U : Y.scheme.Opens, U ≠ ⊥ ∧ U ≤ D.complement ∧
      ∀ (y : Y.ComplexPoint), y.point ∈ U →
        ∀ F : FiberModel f.toBoundaryFibration y,
          ∃ σ : F.variety.RationalPluriform m, σ ∈ F.boundary.sections m ∧ σ ≠ 0 := by
  classical
  by_cases hm0 : m = 0
  · exact (Nat.ne_of_gt hm hm0).elim
  · have hgen := D.generic_mem_complement
    obtain ⟨U, hgenU, hU, ⟨b⟩⟩ := Y.exists_cotangent_chart D.complement
      (genericPoint Y.scheme) hgen
    let := f.surjective
    obtain ⟨x, hx⟩ := f.hom.surjective (genericPoint Y.scheme)
    have hfx : f.hom x ∈ U.1 := hx ▸ hgenU
    obtain ⟨V, hxV, _, e, hsm, t, ht, hI⟩ :=
      exists_relative_log_chart f U hU ⊤ x (by trivial) hfx
    let : Nonempty V.1 := ⟨⟨x, hxV⟩⟩
    let A := Γ(Y.scheme, U.1)
    let B := Γ(X.scheme, V.1)
    let r := X.dimension - Y.dimension
    let : Algebra A B := (f.hom.appLE U.1 V.1 e).hom.toAlgebra
    let : IsScalarTower ℂ A B := IsScalarTower.of_algebraMap_eq fun a =>
      (appLE_constants f.hom f.over_base U.1 V.1 e a).symm
    let : Algebra.IsStandardSmoothOfRelativeDimension r A B := hsm.toAlgebra
    let : Algebra.IsStandardSmooth A B :=
      Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth r
    have hle := base_dimension_le_of_smooth_point f x (hU hfx)
    have hdim : X.dimension = Y.dimension + r := by omega
    have hrank : Module.finrank B (KaehlerDifferential A B) = r := by
      simp only [Module.finrank,
        Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential r,
        Cardinal.toNat_natCast]
    let c := Module.finBasisOfFinrankEq B (KaehlerDifferential A B) hrank
    obtain ⟨q₀, hq₀⟩ := local_logarithmic_numerator E m s hs V t ht hI
    have hq₀n : q₀ ≠ 0 := by
      intro hq
      apply hn
      rw [← hq₀, hq, map_zero]
    let q := degreeTransport ℂ B hdim m q₀
    let a := pluricanonicalCoordinate ℂ A B Y.dimension r m b c q
    have han : a ≠ 0 := by
      have hqn : q ≠ 0 := by
        simpa only [map_zero] using (degreeTransport ℂ B hdim m).injective.ne hq₀n
      simpa only [map_zero] using
        (pluricanonicalCoordinate ℂ A B Y.dimension r m b c).injective.ne hqn
    obtain ⟨W, hW, hWU, hmeet⟩ := exists_open_meeting_coefficient f U.1 hU V e a han
    refine ⟨W, hW, hWU.trans hU, ?_⟩
    intro y hy F
    have hyU := hWU hy
    have hdimF := fiber_dimension_eq f y (hU hyU) F
    have hr : r = F.variety.dimension := by omega
    obtain ⟨z, hz⟩ := hmeet y hy F
    have hzV : F.inclusion z ∈ V.1 := X.scheme.basicOpen_le a hz
    let : Nonempty (F.inclusion ⁻¹ᵁ V.1) := ⟨⟨z, hzV⟩⟩
    let cF := basisDegreeTransport hr c
    let qF := degreeTransport ℂ B (congrArg (Y.dimension + ·) hr) m q
    let P : NumeratorChart f.toBoundaryFibration y F U hdimF m s :=
      ⟨V, e, inferInstance, inferInstance, inferInstance, cF, t, ht, hI, qF, by
        dsimp only [qF, q]
        rw [degreeTransport_trans, logarithmicPullback_degreeTransport, hq₀]⟩
    obtain ⟨σ, hσ, heq⟩ := exists_global_specialization f U hU y hyU F hdimF m s hs b
    refine ⟨σ, hσ, ?_⟩
    rw [← heq P]
    change logarithmicNumerator f.toBoundaryFibration y F U hyU V e
      (inferInstance : Algebra.FormallySmooth A B) Y.dimension F.variety.dimension m b cF t qF ≠ 0
    apply logarithmicNumerator_ne_zero_of_coefficient f.toBoundaryFibration y F U hyU V e
      (inferInstance : Algebra.FormallySmooth A B) Y.dimension m b cF t
      (fiber_boundary_equation_ne_zero f.toBoundaryFibration y F V t hI) qF
    dsimp only [cF, qF]
    rw [pluricanonicalCoordinate_degreeTransport]
    exact chartToFunctionField_ne_zero_of_mem_basicOpen F.inclusion V.1 a z hz

end ReverseLogKodaira.SmoothProjectiveVariety

end

end OAI

-- ---- platform node ----
open OAI OAI.ReverseLogKodaira OAI.ReverseLogKodaira.SmoothProjectiveVariety
open CategoryTheory AlgebraicGeometry
open scoped TensorProduct
open DifferentialBaseChange CanonicalSpecialization FiberChartSpecialization

theorem solution
    {X Y : SmoothProjectiveVariety} {E : X.ReducedSNCBoundary} {D : Y.ReducedSNCBoundary}
    (f : StratumSmoothFibration X Y E D) (m : ℕ) (hm : 0 < m)
    (s : X.RationalPluriform m) (hs : s ∈ E.sections m) (hn : s ≠ 0) :
    ∃ U : Y.scheme.Opens, U ≠ ⊥ ∧ U ≤ D.complement ∧
      ∀ (y : Y.ComplexPoint), y.point ∈ U →
        ∀ F : FiberModel f.toBoundaryFibration y,
          ∃ σ : F.variety.RationalPluriform m, σ ∈ F.boundary.sections m ∧ σ ≠ 0 := by
  first
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform f m hm s hs hn
    | exact OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform
    | (apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform <;> assumption)
    | (intros; apply OAI.ReverseLogKodaira.SmoothProjectiveVariety.exists_open_nonzero_fiber_pluriform <;> assumption)
