-- Prove2me | solution 1 for OAI.Erdos970.WeightedTorusJets.Geometry.torus_prime_residue_logarithmicForm_ne_zero_jb247
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:01:52.307093+00:00
-- url     : https://prove2.me/submissions/901a7552-9b66-4c09-a933-bfc0387c3de8

import Mathlib
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Integrability.LogMeromorphic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.PosLog
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Finite.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.MetricSpace.Basic
import Definitions.Def_OAIQ247J004
import Definitions.Def_OAIQ247J005

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_DominantFunctionFieldHom
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay

noncomputable section

open Module

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

attribute [local instance] OAI.Erdos970.WeightedTorusJets.scheme_top_nonempty
theorem existsUnique_globalSection_scalar (K : Type u) [Field K] [IsAlgClosed K]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (CommRingCat.of K))
    [UniversallyClosed f] (s : Γ(X, ⊤)) :
    ∃! c : K, ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom c = s := by
  have hIntegral : ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ f.appTop).hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  exact (IsAlgClosed.ringHom_bijective_of_isIntegral _ hIntegral).existsUnique s

end WeightedTorusJets

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

theorem finite_integralClosure_of_normal_subring
    (R K A L : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Field K] [CommRing A] [Field L]
    [Algebra R K] [IsFractionRing R K] [Algebra R A] [Algebra A L]
    [Algebra R L] [IsScalarTower R A L] [Algebra K L] [IsScalarTower R K L]
    [Algebra.IsIntegral R A] [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite A (integralClosure A L) := by
  have : IsIntegralClosure (integralClosure A L) R L := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := by
      intro x
      constructor
      · intro hx
        exact ⟨⟨x, hx.tower_top⟩, rfl⟩
      · rintro ⟨x, rfl⟩
        exact isIntegral_trans (R := R) (A := A) _ x.property }
  have : Module.Finite R (integralClosure A L) :=
    IsIntegralClosure.finite R K L (integralClosure A L)
  exact Module.Finite.of_restrictScalars_finite R A (integralClosure A L)

theorem finite_integralClosure_of_finiteType_charZero (k A : Type*)
    [Field k] [CharZero k] [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] : Module.Finite A (integralClosure A (FractionRing A)) := by
  obtain ⟨n, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let : Algebra P A := g.toRingHom.toAlgebra
  have : Module.Finite P A := hfin
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  let := FractionRing.liftAlgebra P (FractionRing A)
  have : Module.Finite (FractionRing P) (FractionRing A) := by
    apply Module.rank_lt_aleph0_iff.mp
    rw [Algebra.IsAlgebraic.rank_fractionRing]
    exact Module.rank_lt_aleph0 P A
  exact finite_integralClosure_of_normal_subring P (FractionRing P) A (FractionRing A)

theorem isFractionRing_genericPoint_preimage_sections
    (Y : Scheme.{u}) [IsIntegral Y] (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U] :
    let n := Y.fromSpecStalk (genericPoint Y)
    let := (n.app U).hom.toAlgebra
    IsFractionRing Γ(Y, U) Γ(Spec Y.functionField, n ⁻¹ᵁ U) := by
  let n := Y.fromSpecStalk (genericPoint Y)
  let := (n.app U).hom.toAlgebra
  have hm : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr
      (by simpa using (inferInstance : Nonempty U))
  have hpre : n ⁻¹ᵁ U = ⊤ := by
    apply top_unique
    intro x _
    change n x ∈ U
    have hx : x = IsLocalRing.closedPoint Y.functionField :=
      Subsingleton.elim (α := PrimeSpectrum Y.functionField) _ _
    rw [hx, Scheme.fromSpecStalk_closedPoint]
    exact hm
  let e : Y.functionField ≅ Γ(Spec Y.functionField, n ⁻¹ᵁ U) :=
    (Scheme.ΓSpecIso Y.functionField).symm ≪≫
      (Spec Y.functionField).presheaf.mapIso (eqToIso hpre).op
  let eA : Y.functionField ≃ₐ[Γ(Y, U)] Γ(Spec Y.functionField, n ⁻¹ᵁ U) :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := fun a ↦ by
        change e.hom (Y.germToFunctionField U a) = n.app U a
        rw [Scheme.fromSpecStalk_app hm]
        rfl }
  have := functionField_isFractionRing_of_isAffineOpen Y U hU
  exact IsFractionRing.of_algEquiv eA

theorem isFinite_genericNormalization (k : Type u) [Field k] [CharZero k]
    (Y : Scheme.{u}) [IsIntegral Y]
    (g : Y ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType g] :
    IsFinite (Y.fromSpecStalk (genericPoint Y)).fromNormalization := by
  let n := Y.fromSpecStalk (genericPoint Y)
  constructor
  intro U hU
  let A := Γ(Y, U)
  let L := Γ(Spec Y.functionField, n ⁻¹ᵁ U)
  let : Algebra A L := (n.app U).hom.toAlgebra
  let F := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appLE ⊤ U le_top
  let : Algebra k A := F.hom.toAlgebra
  have : Algebra.FiniteType k A := by
    change F.hom.FiniteType
    apply RingHom.finiteType_respectsIso.2
      (e := (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv)
    exact g.finiteType_appLE (isAffineOpen_top _) hU le_top
  have hfin : Module.Finite A (integralClosure A L) := by
    by_cases hne : Nonempty U
    · have : IsFractionRing A L := isFractionRing_genericPoint_preimage_sections Y U hU
      have := finite_integralClosure_of_finiteType_charZero k A
      exact Module.Finite.equiv (FractionRing.algEquiv A L).mapIntegralClosure.toLinearEquiv
    · have hUbot : U = ⊥ := by
        apply bot_unique
        intro x hx
        exact False.elim (hne ⟨⟨x, hx⟩⟩)
      have hprebot : n ⁻¹ᵁ U = ⊥ := by rw [hUbot]; rfl
      have : Subsingleton L := by dsimp only [L]; rw [hprebot]; infer_instance
      infer_instance
  rw [n.fromNormalization_app hU, CommRingCat.hom_comp]
  exact (RingHom.Finite.of_surjective _
    (n.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.surjective).comp
      (RingHom.finite_algebraMap.mpr hfin)

end WeightedTorusJets

open IsLocalRing

theorem isDiscreteValuationRing_of_fraction_pole
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K]
    (y : K) (hy : y ∉ Set.range (algebraMap R K))
    (hmul : ∀ r ∈ maximalIdeal R, y * algebraMap R K r ∈ Set.range (algebraMap R K)) :
    IsDiscreteValuationRing R := by
  classical
  have hnf : ¬ IsField R := fun h ↦ hy ((IsFractionRing.surjective_iff_isField.mpr h) y)
  have hmne : maximalIdeal R ≠ ⊥ := isField_iff_maximalIdeal_eq.not.mp hnf
  let M : Submodule R K := Submodule.map (Algebra.linearMap R K) (maximalIdeal R)
  have hM : M ≠ ⊥ := by
    obtain ⟨a, ha, hane⟩ := (Submodule.ne_bot_iff _).mp hmne
    rw [Submodule.ne_bot_iff]
    exact ⟨algebraMap R K a, ⟨a, ha, rfl⟩,
      (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr hane⟩
  have hstable : ¬ ∀ z ∈ M, y * z ∈ M := by
    intro h
    have hint : IsIntegral R y := isIntegral_of_smul_mem_submodule M hM
      (Submodule.FG.map _ (IsNoetherian.noetherian _)) y h
    exact hy (IsIntegrallyClosed.algebraMap_eq_of_integral hint)
  push Not at hstable
  obtain ⟨z, hz, hyz⟩ := hstable
  obtain ⟨r, hr, rfl⟩ := hz
  obtain ⟨t, ht⟩ := hmul r hr
  have htunit : IsUnit t := by
    by_contra htunit
    apply hyz
    exact ⟨t, htunit, ht⟩
  obtain ⟨v, hv⟩ := htunit.exists_right_inv
  let u : R := r * v
  have hu : u ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hr
  have hyu : y * algebraMap R K u = 1 := by
    rw [show u = r * v from rfl, map_mul, ← mul_assoc, ← ht, ← map_mul, hv, map_one]
  have hp : (maximalIdeal R).IsPrincipal := by
    refine ⟨⟨u, le_antisymm ?_ ?_⟩⟩
    · intro a ha
      obtain ⟨b, hb⟩ := hmul a ha
      apply Ideal.mem_span_singleton'.mpr
      refine ⟨b, ?_⟩
      apply IsFractionRing.injective R K
      rw [map_mul, hb, mul_right_comm, hyu, one_mul]
    · exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hu)
  exact ((IsDiscreteValuationRing.TFAE R hnf).out (5-1) (1-1)).mp hp

theorem height_eq_one_of_prime_denominator
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (p : Ideal R) [p.IsPrime] (y : K)
    (hp : ∀ r : R, r ∈ p ↔ y * algebraMap R K r ∈ Set.range (algebraMap R K)) :
    p.height = 1 := by
  classical
  let S := Localization.subalgebra.ofField K p.primeCompl p.primeCompl_le_nonZeroDivisors
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S p
  have : IsNoetherianRing S :=
    IsLocalization.isNoetherianRing p.primeCompl S inferInstance
  have : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S p.primeCompl p.primeCompl_le_nonZeroDivisors
  have hmap (a : R) (s : p.primeCompl) :
      algebraMap S K (IsLocalization.mk' S a s) =
        algebraMap R K a / algebraMap R K s := by
    have hs : algebraMap R K s ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr
      (fun hzero ↦ s.2 (hzero ▸ p.zero_mem))
    apply (eq_div_iff hs).mpr
    have h := congrArg (algebraMap S K) (IsLocalization.mk'_spec S a s)
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply R S K] using h
  have hnot : y ∉ Set.range (algebraMap S K) := by
    rintro ⟨z, hz⟩
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    apply s.2
    apply (hp s).mpr
    refine ⟨a, ?_⟩
    rw [← hz, hmap]
    have hs : algebraMap R K s ≠ 0 := (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr
      (fun hzero ↦ s.2 (hzero ▸ p.zero_mem))
    exact (div_mul_cancel₀ _ hs).symm
  have hmul : ∀ r ∈ maximalIdeal S,
      y * algebraMap S K r ∈ Set.range (algebraMap S K) := by
    intro z hz
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    have ha : a ∈ p := (IsLocalization.AtPrime.mk'_mem_maximal_iff S p a s).mp hz
    obtain ⟨b, hb⟩ := (hp a).mp ha
    refine ⟨IsLocalization.mk' S b s, ?_⟩
    rw [hmap, hmap, hb, mul_div_assoc]
  have : IsDiscreteValuationRing S := isDiscreteValuationRing_of_fraction_pole y hnot hmul
  have hdim := IsDiscreteValuationRing.ringKrullDim_eq_one S
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p S] at hdim
  exact_mod_cast hdim

theorem mem_algebraMap_of_mem_height_one_localizations
    {R K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K] {x : K}
    (hlocal : ∀ p : PrimeSpectrum R, p.asIdeal.height = 1 →
      x ∈ Localization.subalgebra.ofField K p.asIdeal.primeCompl
        p.asIdeal.primeCompl_le_nonZeroDivisors) :
    x ∈ Set.range (algebraMap R K) := by
  classical
  by_contra hx
  let B : Submodule R K := (Algebra.linearMap R K).range
  let D : K → Ideal R := fun y ↦ B.colon {y}
  have hD (y : K) (r : R) :
      r ∈ D y ↔ y * algebraMap R K r ∈ Set.range (algebraMap R K) := by
    simp only [D, Submodule.mem_colon_singleton, B, LinearMap.mem_range,
      Algebra.linearMap_apply, Algebra.smul_def, mul_comm, Set.mem_range]
  have hDx : D x ≠ ⊤ := by
    intro heq
    have hmem : (1 : R) ∈ D x := heq ▸ (show (1 : R) ∈ (⊤ : Ideal R) by simp)
    exact hx (by simpa using (hD x 1).mp hmem)
  obtain ⟨p, ⟨hle, hpne, y, rfl⟩, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherianRing R)
      {p : Ideal R | D x ≤ p ∧ p ≠ ⊤ ∧ ∃ y : K, p = D y}
      ⟨D x, le_rfl, hDx, x, rfl⟩
  have hprime : (D y).IsPrime := by
    refine ⟨hpne, ?_⟩
    intro a b hab
    by_cases ha : a ∈ D y
    · exact Or.inl ha
    apply Or.inr
    have H : D y ≤ D (algebraMap R K a * y) := by
      intro c hc
      obtain ⟨d, hd⟩ := (hD y c).mp hc
      apply (hD _ c).mpr
      refine ⟨a * d, ?_⟩
      rw [map_mul, hd, mul_assoc]
    have Hne : D (algebraMap R K a * y) ≠ ⊤ := by
      intro heq
      apply ha
      have hmem : (1 : R) ∈ D (algebraMap R K a * y) :=
        heq ▸ (show (1 : R) ∈ (⊤ : Ideal R) by simp)
      simpa [hD, mul_comm] using hmem
    have Heq : D y = D (algebraMap R K a * y) :=
      H.eq_of_not_lt (hmax _ ⟨hle.trans H, Hne, _, rfl⟩)
    rw [Heq, hD]
    simpa [map_mul, mul_left_comm, mul_assoc] using (hD y (a * b)).mp hab
  have : (D y).IsPrime := hprime
  have hheight : (D y).height = 1 := height_eq_one_of_prime_denominator (D y) y (hD y)
  obtain ⟨a, s, hs, hxs⟩ := hlocal ⟨D y, hprime⟩ hheight
  apply hs
  apply hle
  apply (hD x s).mpr
  refine ⟨a, ?_⟩
  rw [hxs, mul_assoc, inv_mul_cancel₀, mul_one]
  exact (IsFractionRing.to_map_eq_zero_iff (K := K)).not.mpr
    (fun hzero ↦ hs (hzero ▸ (D y).zero_mem))

open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory

namespace AlgebraicGeometry.Scheme

variable {X : Scheme} [IsIntegral X] [IsLocallyNoetherian X]

theorem isDiscreteValuationRing_stalk_of_isIntegrallyClosed {x : X}
    [IsIntegrallyClosed (X.presheaf.stalk x)] (hx : Order.coheight x = 1) :
    IsDiscreteValuationRing (X.presheaf.stalk x) := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
  have hnf : ¬ IsField (X.presheaf.stalk x) := by
    intro h
    have hzero := ringKrullDim_eq_zero_of_isField h
    rw [ringKrullDim_stalk_eq_coheight, hx] at hzero
    exact one_ne_zero hzero
  apply ((IsDiscreteValuationRing.TFAE (X.presheaf.stalk x) hnf).out (4-1) (1-1)).mp
  refine ⟨inferInstance, IsLocalRing.maximalIdeal (X.presheaf.stalk x), ?_, ?_⟩
  · exact ⟨IsLocalRing.isField_iff_maximalIdeal_eq.not.mp hnf, inferInstance⟩
  · intro p hp
    exact IsLocalRing.eq_maximalIdeal (hp.2.isMaximal_of_ne_bot hp.1)

theorem exists_stalk_unit_of_ord_eq_zero {x : X}
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (hx : Order.coheight x = 1) {f : X.functionField} (hf : f ≠ 0)
    (hord : X.ord f x = 0) :
    ∃ u : X.presheaf.stalk x, IsUnit u ∧
      algebraMap (X.presheaf.stalk x) X.functionField u = f := by
  have h : Ring.ordFrac (X.presheaf.stalk x) f = 1 := by
    simpa [_root_.AlgebraicGeometry.Scheme.ordHom] using (X.ord_eq_iff hx hf).mp hord
  change f ∈ (IsUnit.submonoid (X.presheaf.stalk x)).map
    (algebraMap (X.presheaf.stalk x) X.functionField)
  rw [← Ring.mker_ordFrac_eq_isUnitSubmonoid]
  exact h

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

variable {X : Scheme} [IsIntegral X]

theorem IsAffineOpen.isIntegrallyClosed_of_stalks {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] : IsIntegrallyClosed Γ(X, U) := by
  let (p : PrimeSpectrum Γ(X, U)) : Algebra Γ(X, U) (X.presheaf.stalk (hU.fromSpec p)) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec p, (hU.isoSpec.inv p).2⟩
  have (p : Ideal Γ(X, U)) [hp : p.IsPrime] :
      IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec ⟨p, hp⟩)) p :=
    hU.isLocalization_stalk' ⟨p, hp⟩ (hU.isoSpec.inv _).2
  exact IsIntegrallyClosed.of_isLocalization_maximal
    (fun p hp ↦ X.presheaf.stalk (hU.fromSpec ⟨p, hp.isPrime⟩)) (fun _ _ ↦ inferInstance)

theorem IsAffineOpen.exists_section_of_codim_one_regular {U : X.Opens}
    (hU : IsAffineOpen U) [Nonempty U] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)] (f : X.functionField)
    (hregular : ∀ x : X, Order.coheight x = 1 →
      ∃ u : X.presheaf.stalk x, algebraMap (X.presheaf.stalk x) X.functionField u = f) :
    ∃ s : Γ(X, U), X.germToFunctionField U s = f := by
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsIntegrallyClosed Γ(X, U) := IsAffineOpen.isIntegrallyClosed_of_stalks hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  have hmem : f ∈ Set.range (algebraMap Γ(X, U) X.functionField) := by
    apply mem_algebraMap_of_mem_height_one_localizations
    intro p hp
    let x : X := hU.fromSpec p
    have hxU : x ∈ U := (hU.isoSpec.inv p).2
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxU⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
      hU.isLocalization_stalk' p hxU
    have hx : Order.coheight x = 1 := by
      have hdim := IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)
      rw [ringKrullDim_stalk_eq_coheight, hp] at hdim
      exact_mod_cast hdim
    have : IsScalarTower Γ(X, U) (X.presheaf.stalk x) X.functionField :=
      functionField_isScalarTower X U ⟨x, hxU⟩
    obtain ⟨u, hu⟩ := hregular x hx
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq p.asIdeal.primeCompl u
    refine ⟨a, s, s.2, ?_⟩
    rw [← hu, ← div_eq_mul_inv]
    have hs : algebraMap Γ(X, U) X.functionField s ≠ 0 :=
      (IsFractionRing.to_map_eq_zero_iff (K := X.functionField)).not.mpr
        (fun hzero ↦ s.2 (hzero ▸ p.asIdeal.zero_mem))
    apply (eq_div_iff hs).mpr
    have h := congrArg (algebraMap (X.presheaf.stalk x) X.functionField)
      (IsLocalization.mk'_spec (X.presheaf.stalk x) a s)
    simpa only [map_mul, ← IsScalarTower.algebraMap_apply Γ(X, U)
      (X.presheaf.stalk x) X.functionField] using h
  exact hmem

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

variable {X : Scheme} [IsIntegral X]

theorem exists_global_unit_of_stalk_units {f : X.functionField}
    (h : ∀ x : X, ∃ u : X.presheaf.stalk x, IsUnit u ∧
      algebraMap (X.presheaf.stalk x) X.functionField u = f) :
    ∃ s : Γ(X, ⊤), IsUnit s ∧
      X.presheaf.germ ⊤ (genericPoint X) (by simp) s = f := by
  classical
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, by simp⟩⟩
  change ∃ s : Γ(X, ⊤), IsUnit s ∧ X.germToFunctionField ⊤ s = f
  have hlocal (x : X) : ∃ (U : X.Opens) (hx : x ∈ U) (s : Γ(X, U)), IsUnit s ∧
      algebraMap (X.presheaf.stalk x) X.functionField (X.presheaf.germ U x hx s) = f := by
    obtain ⟨u, hu, huf⟩ := h x
    obtain ⟨U, hxU, s, hs⟩ := X.presheaf.exists_germ_eq u
    obtain ⟨V, i, hxV, hv⟩ := X.toRingedSpace.isUnit_res_of_isUnit_germ U s x hxU
      (hs.symm ▸ hu)
    refine ⟨V, hxV, X.presheaf.map i.op s, hv, ?_⟩
    rw [X.presheaf.germ_res_apply i x hxV s, hs, huf]
  choose U hx s hs hf using hlocal
  have (x : X) : Nonempty (U x) := ⟨⟨x, hx x⟩⟩
  have hfield (x : X) : X.germToFunctionField (U x) (s x) = f := by
    rw [← X.algebraMap_germ_eq_germToFunctionField (hx x)]
    exact hf x
  have hcover : (⊤ : X.Opens) ≤ iSup U := by
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  have hc : TopCat.Presheaf.IsCompatible X.presheaf U s := by
    intro x y
    apply TopCat.Presheaf.section_ext X.sheaf
    intro z hz
    change X.presheaf.germ (U x ⊓ U y) z hz
        (X.presheaf.map (Opens.infLELeft (U x) (U y)).op (s x)) =
      X.presheaf.germ (U x ⊓ U y) z hz
        (X.presheaf.map (Opens.infLERight (U x) (U y)).op (s y))
    apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
    rw [X.presheaf.germ_res_apply, X.presheaf.germ_res_apply,
      X.algebraMap_germ_eq_germToFunctionField hz.1,
      X.algebraMap_germ_eq_germToFunctionField hz.2]
    exact (hfield x).trans (hfield y).symm
  obtain ⟨g, hg, _⟩ : ∃ g : Γ(X, ⊤),
      (∀ i, X.presheaf.map (homOfLE (show U i ≤ ⊤ from le_top)).op g = s i) ∧ _ :=
    X.sheaf.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top) hcover s hc
  refine ⟨g, ?_, ?_⟩
  · apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro x hxTop
    have heq : X.presheaf.germ ⊤ x hxTop g =
        X.presheaf.germ (U x) x (hx x) (s x) := by
      rw [← hg x, X.presheaf.germ_res_apply]
    rw [heq]
    exact (hs x).map (X.presheaf.germ (U x) x (hx x)).hom
  · let x : X := Classical.arbitrary X
    rw [← hfield x, ← hg x, ← X.algebraMap_germ_eq_germToFunctionField (hx x),
      X.presheaf.germ_res_apply, X.algebraMap_germ_eq_germToFunctionField]

variable [IsLocallyNoetherian X]
  [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]

theorem exists_global_unit_of_ord_eq_zero (f : X.functionField) (hf : f ≠ 0)
    (hord : ∀ x : X, X.ord f x = 0) :
    ∃ s : Γ(X, ⊤), IsUnit s ∧
      X.presheaf.germ ⊤ (genericPoint X) (by simp) s = f := by
  have hunit (x : X) (hx : Order.coheight x = 1) :
      ∃ u : X.presheaf.stalk x, IsUnit u ∧
        algebraMap (X.presheaf.stalk x) X.functionField u = f := by
    have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
      isDiscreteValuationRing_stalk_of_isIntegrallyClosed hx
    exact exists_stalk_unit_of_ord_eq_zero hx hf (hord x)
  apply exists_global_unit_of_stalk_units
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ (⊤ : X.Opens) by simp)
      (⊤ : X.Opens).isOpen
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  obtain ⟨s, hs⟩ := IsAffineOpen.exists_section_of_codim_one_regular hU f fun y hy ↦ by
    obtain ⟨u, _, hu⟩ := hunit y hy
    exact ⟨u, hu⟩
  obtain ⟨t, ht⟩ := IsAffineOpen.exists_section_of_codim_one_regular hU f⁻¹ fun y hy ↦ by
    obtain ⟨u, hu, huf⟩ := hunit y hy
    refine ⟨↑hu.unit⁻¹, ?_⟩
    rw [map_units_inv, hu.unit_spec, huf]
  have hst : s * t = 1 := by
    apply X.germToFunctionField_injective U
    rw [map_mul, map_one, hs, ht, mul_inv_cancel₀ hf]
  have hsu : IsUnit s := IsUnit.of_mul_eq_one t hst
  refine ⟨X.presheaf.germ U x hxU s, hsu.map (X.presheaf.germ U x hxU).hom, ?_⟩
  rw [X.algebraMap_germ_eq_germToFunctionField hxU, hs]

end AlgebraicGeometry.Scheme

open AlgebraicGeometry TopologicalSpace CategoryTheory

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LocalFractionAlgebra
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section

section

namespace WeightedTorusJets.Geometry

variable {K : Type*} [Field K]

theorem maximal_polynomial_height (n : ℕ)
    (p : Ideal (MvPolynomial (Fin n) K)) [p.IsMaximal] : p.height = n := by
  induction n with
  | zero =>
    have h := p.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
    have h0 : p.height ≤ 0 := WithBot.coe_le_coe.mp (by simpa using h)
    exact le_antisymm h0 bot_le
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) := p.map e
    have : P.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
    have : P.LiesOver q := ⟨rfl⟩
    have hq : q.height = n := ih q
    calc
      p.height = P.height := (e.height_map p).symm
      _ = q.height + 1 := Polynomial.height_eq_height_add_one q P
      _ = (n + 1 : ℕ) := by rw [hq]; simp

end WeightedTorusJets.Geometry

end

end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LinearShearHom
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section

namespace WeightedTorusJets.Geometry

theorem ringKrullDim_eq_of_integral_faithful_goingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [FaithfulSMul R S] [Algebra.HasGoingDown R S] :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · apply Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
    intro p q hpq
    exact Ideal.IsIntegral.comap_lt_comap (R := R) (A := S) (I := p.asIdeal) (J := q.asIdeal) hpq
  · change Order.krullDim (PrimeSpectrum R) ≤ Order.krullDim (PrimeSpectrum S)
    apply iSup_le
    intro l
    obtain ⟨P⟩ := Ideal.nonempty_primesOver (S := S) l.last.asIdeal
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P.1
    simpa only [hlen] using Order.LTSeries.length_le_krullDim L

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_FinrankDerivationCardTranscendenceBasis
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section
open Module
open scoped RatFunc

namespace WeightedTorusJets

theorem finiteType_dimension_trdeg {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] :
    ∃ n : ℕ, ringKrullDim A = (n : WithBot ℕ∞) ∧ Algebra.trdeg K A = n := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  refine ⟨n, ?_, ?_⟩
  · rw [Geometry.ringKrullDim_eq_of_integral_faithful_goingDown
      (R := MvPolynomial (Fin n) K)]
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field]
  · have hz : Algebra.trdeg (MvPolynomial (Fin n) K) A = 0 :=
      trdeg_eq_zero_iff.mpr inferInstance
    have h := lift_trdeg_add_eq K (MvPolynomial (Fin n) K) A
    simpa [hz, MvPolynomial.trdeg_of_isDomain] using h.symm

end WeightedTorusJets

noncomputable section
open scoped BigOperators
open MvPolynomial

namespace WeightedTorusJets

theorem trdeg_eq_of_integral_polynomial_base {K A : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] (n : ℕ)
    (g : MvPolynomial (Fin n) K →ₐ[K] A)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    Algebra.trdeg K A = n := by
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have hz : Algebra.trdeg (MvPolynomial (Fin n) K) A = 0 :=
    trdeg_eq_zero
  have h := lift_trdeg_add_eq K (MvPolynomial (Fin n) K) A
  simpa [hz, MvPolynomial.trdeg_of_isDomain] using h.symm

theorem fractionField_trdeg_eq_nat {K A F : Type*} [Field K]
    [CommRing A] [IsDomain A] [Algebra K A] [Field F]
    [Algebra K F] [Algebra A F] [IsScalarTower K A F] [IsFractionRing A F]
    (n : ℕ) (h : Algebra.trdeg K A = n) : Algebra.trdeg K F = n := by
  let : Algebra.IsAlgebraic A F := IsLocalization.isAlgebraic F (nonZeroDivisors A)
  have hz : Algebra.trdeg A F = 0 := trdeg_eq_zero
  have htower := lift_trdeg_add_eq K A F
  simpa [h, hz] using htower.symm

end WeightedTorusJets

end
end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_GenericNormalization
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay
noncomputable section
open Module
open CategoryTheory _root_.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
namespace AlgebraicGeometry.Scheme.Hom

theorem isIntegrallyClosed_stalk_normalization_of_field
    {K : Type*} [Field K] {Y : Scheme}
    (f : Spec (.of K) ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (x : f.normalization) :
    IsIntegrallyClosed (f.normalization.presheaf.stalk x) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open
      (show f.fromNormalization x ∈ (⊤ : Y.Opens) by simp) (⊤ : Y.Opens).isOpen
  have hpre : f ⁻¹ᵁ U = ⊤ := by
    obtain ⟨a, ha⟩ := f.toNormalization.denseRange.exists_mem_open
      (f.fromNormalization ⁻¹ᵁ U).isOpen ⟨x, hxU⟩
    change f.fromNormalization (f.toNormalization a) ∈ U at ha
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization] at ha
    apply top_unique
    intro b _
    change f b ∈ U
    have hba : b = a := Subsingleton.elim b a
    subst b
    exact ha
  have hfield : IsField Γ(Spec (.of K), f ⁻¹ᵁ U) := by
    rw [hpre]
    exact (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField K)
  let : Field Γ(Spec (.of K), f ⁻¹ᵁ U) := hfield.toField
  let : Algebra Γ(Y, U) Γ(Spec (.of K), f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  have : IsIntegrallyClosed (integralClosure Γ(Y, U) Γ(Spec (.of K), f ⁻¹ᵁ U)) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn _ Γ(Spec (.of K), f ⁻¹ᵁ U)
  have : IsIntegrallyClosed Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) :=
    IsIntegrallyClosed.of_equiv (f.normalizationObjIso hU).symm.commRingCatIsoToRingEquiv
  have : Nonempty (f.fromNormalization ⁻¹ᵁ U) := ⟨⟨x, hxU⟩⟩
  let : Algebra Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)
      (f.normalization.presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk f.normalization.presheaf ⟨x, hxU⟩
  have hV := hU.preimage f.fromNormalization
  have := hV.isLocalization_stalk ⟨x, hxU⟩
  exact isIntegrallyClosed_of_isLocalization (f.normalization.presheaf.stalk x)
    (hV.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl
    (hV.primeIdealOf ⟨x, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors

end AlgebraicGeometry.Scheme.Hom

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

theorem isReduced_schemeImage [AlgebraicGeometry.IsReduced X] :
    AlgebraicGeometry.IsReduced f.image := by
  constructor
  intro U
  constructor
  intro s hs
  apply f.image.IsSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨_, ⟨V, hV, rfl⟩, rfl⟩, hxV, hVU⟩ :=
    (Y.isBasis_affineOpens.of_isInducing f.imageι.isEmbedding.isInducing).exists_subset_of_mem_open hx U.isOpen
  refine ⟨f.imageι ⁻¹ᵁ V, hVU, hxV, ?_⟩
  apply f.toImage_app_injective ⟨V, hV⟩
  simp only [map_zero]
  exact ((hs.map (f.image.presheaf.map (homOfLE hVU).op).hom).map
    (f.toImage.app (f.imageι ⁻¹ᵁ V)).hom).eq_zero

theorem isIntegral_schemeImage [IsIntegral X] : IsIntegral f.image := by
  have : AlgebraicGeometry.IsReduced f.image := isReduced_schemeImage f
  have : IrreducibleSpace f.image := by
    rw [irreducibleSpace_def]
    convert!
      ((IrreducibleSpace.isIrreducible_univ X).image _
          f.toImage.continuous.continuousOn).closure
    simpa using f.toImage.denseRange.closure_range.symm
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end WeightedTorusJets

open MvPolynomial HomogeneousLocalization

namespace WeightedTorusJets.Geometry

attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
theorem affineProjChartMap_mk
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (n : ℕ) (p : MvPolynomial (Option ι) k)
    (hp : p ∈ homogeneousSubmodule (Option ι) k (n • 1)) :
    affineProjChartMap (k := k) x (Away.mk (homogeneousSubmodule (Option ι) k)
      (isHomogeneous_X k (none : Option ι)) n p hp) = affineProjEval (k := k) x p := by
  change (IsLocalization.Away.lift (X (none : Option ι))
    (S := Localization.Away (X (none : Option ι) : MvPolynomial (Option ι) k))
    (g := (affineProjEval (k := k) x).toRingHom) (by simp [affineProjEval]))
    (Localization.mk p ⟨(X (none : Option ι)) ^ n, ⟨n, rfl⟩⟩) = _
  rw [Localization.mk_eq_mk', IsLocalization.Away.lift, IsLocalization.lift_mk']
  rw [Units.mul_inv_eq_iff_eq_mul]
  simp [IsUnit.coe_liftRight, affineProjEval]

theorem affineProjEval_mem_chartMap_range
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (p : MvPolynomial ι k) : aeval x p ∈ (affineProjChartMap (k := k) x).range := by
  have hc (c : k) : algebraMap k A c ∈ (affineProjChartMap (k := k) x).range := by
    refine ⟨Away.mk (homogeneousSubmodule (Option ι) k)
      (isHomogeneous_X k (none : Option ι)) 0 (C c) (by simp), ?_⟩
    rw [affineProjChartMap_mk]
    simp [affineProjEval]
  have hx (i : ι) : x i ∈ (affineProjChartMap (k := k) x).range := by
    refine ⟨Away.mk (homogeneousSubmodule (Option ι) k)
      (isHomogeneous_X k (none : Option ι)) 1 (X (some i)) (by simpa using isHomogeneous_X k (some i)), ?_⟩
    rw [affineProjChartMap_mk]
    simp [affineProjEval]
  induction p using MvPolynomial.induction_on with
  | C c => simpa using hc c
  | add p q hp hq => simpa using (affineProjChartMap (k := k) x).range.add_mem hp hq
  | mul_X p i hp => simpa using (affineProjChartMap (k := k) x).range.mul_mem hp (hx i)

theorem affineProjChartMap_surjective
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (hx : Function.Surjective (aeval (R := k) x)) :
    Function.Surjective (affineProjChartMap (k := k) x) := by
  intro a
  obtain ⟨p, rfl⟩ := hx a
  exact affineProjEval_mem_chartMap_range x p

theorem affineProjChartMap_fromZero
    {k A ι : Type*} [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (c : homogeneousSubmodule (Option ι) k 0) :
    affineProjChartMap (k := k) x
      (fromZeroRingHom (homogeneousSubmodule (Option ι) k)
        (Submonoid.powers (X (none : Option ι))) c) = affineProjEval (k := k) x c := by
  change (IsLocalization.Away.lift (X (none : Option ι))
    (S := Localization.Away (X (none : Option ι) : MvPolynomial (Option ι) k))
    (g := (affineProjEval (k := k) x).toRingHom) (by simp [affineProjEval]))
    (algebraMap (MvPolynomial (Option ι) k)
      (Localization.Away (X (none : Option ι))) c) = _
  exact IsLocalization.Away.lift_eq _ _ _

end WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

namespace WeightedTorusJets

universe u

variable (k ι : Type u) [CommRing k]

theorem polynomial_finiteType_degreeZero [Finite ι] :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) := by
  have : IsScalarTower k (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) :=
    IsScalarTower.of_algebraMap_eq (R := k)
      (S := MvPolynomial.homogeneousSubmodule ι k 0)
      (A := MvPolynomial ι k) fun _ ↦ rfl
  exact Algebra.FiniteType.of_restrictScalars_finiteType k
    (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k)

theorem polynomialProjToSpec_isProper [Finite ι] : IsProper (polynomialProjToSpec k ι) := by
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) :=
    polynomial_finiteType_degreeZero k ι
  have : IsIso (CommRingCat.ofHom
      (algebraMap k (MvPolynomial.homogeneousSubmodule ι k 0))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (polynomialDegreeZeroEquiv k ι).bijective
  dsimp only [polynomialProjToSpec]
  infer_instance

end WeightedTorusJets
namespace WeightedTorusJets.Geometry

open CategoryTheory _root_.AlgebraicGeometry

universe u

attribute [local instance] WeightedTorusJets.Geometry.polynomialGradedAlgebra
theorem affineIntoProj_isImmersion {k A ι : Type u}
    [CommRing k] [CommRing A] [Algebra k A]
    (x : ι → A) (hx : Function.Surjective (aeval (R := k) x)) :
    IsImmersion (affineIntoProj (k := k) x) := by
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (affineProjChartMap (k := k) x))) :=
    IsClosedImmersion.spec_of_surjective _ (affineProjChartMap_surjective x hx)
  unfold affineIntoProj
  infer_instance

theorem affineIntoProj_toSpec {k A ι : Type u}
    [CommRing k] [CommRing A] [Algebra k A] (x : ι → A) :
    affineIntoProj (k := k) x ≫ polynomialProjToSpec k (Option ι) =
      Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  simp only [affineIntoProj, polynomialProjToSpec, Category.assoc,
    Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  change affineProjChartMap (k := k) x
    (fromZeroRingHom (homogeneousSubmodule (Option ι) k) _
      (algebraMap k (homogeneousSubmodule (Option ι) k 0) c)) = algebraMap k A c
  rw [affineProjChartMap_fromZero]
  change affineProjEval (k := k) x (C c) = _
  simp [affineProjEval]

theorem exists_proper_immersion_of_finiteType
    (k A : Type u) [CommRing k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (Y : Scheme.{u}) (f : Spec (CommRingCat.of A) ⟶ Y)
      (g : Y ⟶ Spec (CommRingCat.of k)),
      IsImmersion f ∧ QuasiCompact f ∧ Scheme.IsSeparated Y ∧ IsProper g ∧
      f ≫ g = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
  obtain ⟨ι, hι, φ, hφ⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial'.mp
    (inferInstance : Algebra.FiniteType k A)
  let : Fintype ι := hι
  let x : ι → A := fun i => φ (X i)
  have hx : Function.Surjective (aeval (R := k) x) := by
    exact MvPolynomial.aeval_unique φ ▸ hφ
  exact ⟨Proj (homogeneousSubmodule (Option ι) k), affineIntoProj x,
    polynomialProjToSpec k (Option ι), affineIntoProj_isImmersion x hx,
    inferInstance, inferInstance, polynomialProjToSpec_isProper k (Option ι), affineIntoProj_toSpec x⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets

universe u

instance schemeImage_isIntegral {X Y : Scheme.{u}} [IsIntegral X] (f : X ⟶ Y)
    [QuasiCompact f] : IsIntegral f.image := isIntegral_schemeImage f

theorem exists_normal_proper_model_of_finiteType_domain
    (k A : Type u) [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ (N : Scheme.{u}) (hN : IsIntegral N),
      let : IsIntegral N := hN
      ∃ (p : N ⟶ Spec (CommRingCat.of k)),
        IsLocallyNoetherian N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
        LocallyOfFiniteType p ∧ UniversallyClosed p ∧
        (let : Algebra k N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
         Nonempty (FractionRing A →ₐ[k] N.functionField)) := by
  obtain ⟨Y, f, g, hf, hqc, hsep, hproper, hfg⟩ :=
    Geometry.exists_proper_immersion_of_finiteType k A
  let C := f.image
  let gC := f.imageι ≫ g
  let N := genericNormalization C
  let p := genericNormalizationMap C ≫ gC
  have : IsFinite (genericNormalizationMap C) := isFinite_genericNormalization k C gC
  have : IsLocallyNoetherian N := LocallyOfFiniteType.isLocallyNoetherian p
  have hnormal (x : N) : IsIntegrallyClosed (N.presheaf.stalk x) :=
    _root_.OAI.Erdos970.AlgebraicGeometry.Scheme.Hom.isIntegrallyClosed_stalk_normalization_of_field
      (C.fromSpecStalk (genericPoint C)) x
  have hcomp : f.toImage ≫ gC = Spec.map (CommRingCat.ofHom (algebraMap k A)) := by
    simpa only [gC, ← Category.assoc, Scheme.Hom.toImage_imageι] using hfg
  let : Algebra k (Spec (CommRingCat.of A)).functionField :=
    schemeBaseStalkAlgebra (f.toImage ≫ gC) (genericPoint (Spec (CommRingCat.of A)))
  let : Algebra k N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  let e : FractionRing A ≃ₐ[k] (Spec (CommRingCat.of A)).functionField := by
    change @AlgEquiv k (FractionRing A) ((Spec (CommRingCat.of A)).functionField)
      _ _ _ _ (schemeBaseStalkAlgebra (f.toImage ≫ gC)
        (genericPoint (Spec (CommRingCat.of A))))
    rw [hcomp]
    exact affineFractionFieldAlgEquiv k A
  let φ : (Spec (CommRingCat.of A)).functionField →ₐ[k] N.functionField :=
    normalizationFunctionFieldAlgHom f.toImage gC
  exact ⟨N, inferInstance, p, inferInstance, hnormal, inferInstance, inferInstance,
    ⟨φ.comp e.toAlgHom⟩⟩

end WeightedTorusJets

open _root_.Polynomial IsLocalRing TensorProduct

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_ParameterIdeal
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section OriginalSourceGeometryOverlay
noncomputable section
open Module
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.Erdos970.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open _root_.Polynomial IsLocalRing TensorProduct
namespace WeightedTorusJets

theorem transcendental_of_nonzero_nonunit
    {k A : Type*} [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    {t : A} (ht0 : t ≠ 0) (htu : ¬ IsUnit t) : Transcendental k t := by
  intro h
  exact htu (h.isIntegral.isUnit ht0)

theorem residue_aeval_eq_eval_zero
    {k A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    {t : A} (ht : t ∈ maximalIdeal A) (p : k[X]) :
    residue A (Polynomial.aeval t p) = algebraMap k (ResidueField A) (p.eval 0) := by
  have ht0 : residue A t = 0 := (residue_eq_zero_iff t).mpr ht
  change (IsScalarTower.toAlgHom k A (ResidueField A)) (Polynomial.aeval t p) = _
  rw [← Polynomial.aeval_algHom_apply]
  change Polynomial.aeval (residue A t) p = _
  rw [ht0, ← Polynomial.coeff_zero_eq_aeval_zero', Polynomial.coeff_zero_eq_eval_zero]

theorem isUnit_aeval_of_eval_zero_ne_zero
    {k A : Type*} [Field k] [CommRing A] [IsLocalRing A] [Algebra k A]
    {t : A} (ht : t ∈ maximalIdeal A) {p : k[X]} (hp : p.eval 0 ≠ 0) :
    IsUnit (Polynomial.aeval t p) := by
  rw [← residue_ne_zero_iff_isUnit, residue_aeval_eq_eval_zero ht]
  exact (_root_.map_ne_zero (algebraMap k (ResidueField A))).mpr hp

theorem exists_parameter_local_algebra
    {k A : Type*} [Field k] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra k A] (t : A) (ht : Irreducible t) :
    ∃ φ : parameterRing k →ₐ[k] A,
      Function.Injective φ ∧ IsLocalHom φ.toRingHom ∧
      (maximalIdeal (parameterRing k)).map φ.toRingHom = maximalIdeal A := by
  let p := parameterIdeal k
  let R := Localization.AtPrime p
  have htmem : t ∈ maximalIdeal A := ht.not_isUnit
  let φ : R →ₐ[k] A := IsLocalization.liftAlgHom (M := p.primeCompl)
    (f := Polynomial.aeval t) fun s ↦ isUnit_aeval_of_eval_zero_ne_zero htmem s.property
  have hφ : φ.toRingHom.comp (algebraMap k[X] R) = (Polynomial.aeval t).toRingHom := by
    apply RingHom.ext
    intro r
    exact IsLocalization.lift_eq _ r
  have hinj : Function.Injective φ := by
    rw [show Function.Injective φ = Function.Injective φ.toRingHom from rfl,
      IsLocalization.injective_iff_map_algebraMap_eq p.primeCompl]
    intro x y
    simp only [← RingHom.comp_apply, hφ]
    change _ ↔ Polynomial.aeval t x = Polynomial.aeval t y
    exact (FaithfulSMul.algebraMap_injective k[X] R).eq_iff.trans
        ((transcendental_iff_injective.mp
          (transcendental_of_nonzero_nonunit ht.ne_zero ht.not_isUnit)).eq_iff).symm
  have hmap : (maximalIdeal R).map φ.toRingHom = maximalIdeal A := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hφ]
    have hp : p = Ideal.span {(Polynomial.X : k[X])} := by
      simpa [p, parameterIdeal] using Polynomial.ker_evalRingHom (0 : k)
    rw [hp, Ideal.map_span, Set.image_singleton]
    change Ideal.span {Polynomial.aeval t Polynomial.X} = maximalIdeal A
    rw [Polynomial.aeval_X, ht.maximalIdeal_eq]
  exact ⟨φ, hinj, ((local_hom_TFAE φ.toRingHom).out (3-1) (1-1)).mp hmap.le, hmap⟩

end WeightedTorusJets

open TensorProduct IsLocalRing

namespace WeightedTorusJets

theorem formallySmooth_of_flat_of_essFiniteType_of_map_maximalIdeal
    {R S : Type*} [CommRing R] [CommRing S] [IsNoetherianRing R]
    [IsLocalRing R] [IsLocalRing S] [Algebra R S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [Algebra.EssFiniteType R S] [PerfectField (ResidueField R)]
    (hmap : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    Algebra.FormallySmooth R S := by
  let e : (ResidueField R ⊗[R] S) ≃+* ResidueField S :=
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor S (maximalIdeal R)).symm.toRingEquiv.trans
      (Ideal.quotEquivOfEq hmap)
  let : Field (ResidueField R ⊗[R] S) :=
    (e.toMulEquiv.isField (Field.toIsField (ResidueField S))).toField
  let P := Algebra.EssFiniteType.subalgebra R S
  let M := Algebra.EssFiniteType.submonoid R S
  have : Algebra.FinitePresentation R P :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact Algebra.FormallySmooth.of_formallySmooth_residueField_tensor M



theorem formallySmooth_of_essFiniteType_of_discreteValuationRing
    {k A : Type*} [Field k] [CharZero k] [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] [Algebra k A] [Algebra.EssFiniteType k A] :
    Algebra.FormallySmooth k A := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨φ, hinj, hlocal, hmap⟩ := exists_parameter_local_algebra (k := k) t ht
  let R := parameterRing k
  algebraize [φ.toRingHom]
  have : IsLocalHom (algebraMap R A) := hlocal
  have : Module.IsTorsionFree R A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  have : Algebra.EssFiniteType R A := Algebra.EssFiniteType.of_comp k R A
  have : CharZero (ResidueField R) := Algebra.charZero_of_charZero k (ResidueField R)
  have : Algebra.FormallySmooth R A :=
    formallySmooth_of_flat_of_essFiniteType_of_map_maximalIdeal hmap
  have : Algebra.FormallyEtale k[X] R :=
    Algebra.FormallyEtale.of_isLocalization (parameterIdeal k).primeCompl
  have : Algebra.FormallySmooth k R := Algebra.FormallySmooth.comp k k[X] R
  exact Algebra.FormallySmooth.comp k R A

end WeightedTorusJets

open scoped TensorProduct

namespace WeightedTorusJets.Geometry

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

theorem exists_derivation_residue_eq_one (I : Ideal A) [I.IsMaximal]
    [Algebra.FormallySmooth K A] [Algebra.FormallySmooth K (A ⧸ I)]
    (x : I) (hx : I.toCotangent x ≠ 0) :
    ∃ D : Derivation K A A, Ideal.Quotient.mk I (D x) = 1 := by
  let := Ideal.Quotient.field I
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (A ⧸ I) hx
  obtain ⟨ψ, hψ⟩ := LinearMap.dualMap_surjective_of_injective
    (conormalDifferential_injective (K := K) I) φ
  let l : Ω[A⁄K] →ₗ[A] A ⧸ I := ψ.restrictScalars A ∘ₗ
    TensorProduct.mk A (A ⧸ I) Ω[A⁄K] 1
  obtain ⟨f, hf⟩ := Module.projective_lifting_property (Algebra.linearMap A (A ⧸ I)) l
    Ideal.Quotient.mk_surjective
  refine ⟨KaehlerDifferential.linearMapEquivDerivation K A f, ?_⟩
  change Ideal.Quotient.mk I (f (KaehlerDifferential.D K A x)) = 1
  have he := LinearMap.congr_fun hf (KaehlerDifferential.D K A x)
  change Ideal.Quotient.mk I (f (KaehlerDifferential.D K A x)) =
    ψ (1 ⊗ₜ[A] KaehlerDifferential.D K A x) at he
  rw [he, ← conormalDifferential_toCotangent]
  exact (LinearMap.congr_fun hψ (I.toCotangent x)).trans hφ

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem uniformizer_cotangent_ne_zero {A : Type*} [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] (t : A) (ht : Irreducible t)
    (hm : t ∈ IsLocalRing.maximalIdeal A) :
    (IsLocalRing.maximalIdeal A).toCotangent ⟨t, hm⟩ ≠ 0 := by
  intro h
  have hd := ((IsLocalRing.maximalIdeal A).toCotangent_eq_zero ⟨t, hm⟩).mp h
  change t ∈ IsLocalRing.maximalIdeal A ^ 2 at hd
  rw [ht.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hd
  have hle : 2 ≤ 1 := (pow_dvd_pow_iff ht.ne_zero ht.not_isUnit).mp (by simpa using hd)
  omega

theorem exists_transverse_derivation_uniformizer {K A : Type*} [Field K] [PerfectField K]
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra K A]
    [Algebra.EssFiniteType K A] [Algebra.FormallySmooth K A]
    (t : A) (ht : Irreducible t) :
    ∃ D : Derivation K A A, IsLocalRing.residue A (D t) = 1 := by
  have hm : t ∈ IsLocalRing.maximalIdeal A := by
    rw [ht.maximalIdeal_eq]
    exact Ideal.subset_span (Set.mem_singleton t)
  let := Ideal.Quotient.field (IsLocalRing.maximalIdeal A)
  have : Algebra.FormallySmooth K (A ⧸ IsLocalRing.maximalIdeal A) := inferInstance
  exact exists_derivation_residue_eq_one (K := K) (IsLocalRing.maximalIdeal A)
    ⟨t, hm⟩ (uniformizer_cotangent_ne_zero t ht hm)



variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

theorem localizeDerivation_algebraMap (M : Submonoid S) [IsLocalization M T]
    (D : Derivation R S S) (s : S) :
    localizeDerivation M D (algebraMap S T s) = algebraMap S T (D s) := by
  let := Algebra.FormallyEtale.of_isLocalization (Rₘ := T) M
  change ((Algebra.ofId S T).toLinearMap.compDer D).liftKaehlerDifferential.liftBaseChange T
    ((KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R S T).symm
      (KaehlerDifferential.D R T (algebraMap S T s))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp

end WeightedTorusJets.Geometry

open scoped BigOperators

namespace WeightedTorusJets

theorem int_coefficients_eq_zero_of_sum_eq_zero
    {ι K : Type*} [Fintype ι] [Field K] [CharZero K]
    {c : ι → K} (hc : LinearIndependent ℚ c)
    {n : ι → ℤ} (h : ∑ i, c i * (n i : K) = 0) : ∀ i, n i = 0 := by
  apply Fintype.linearIndependent_iff.mp (hc.restrict_scalars' ℤ) n
  simpa [zsmul_eq_mul, mul_comm] using h

theorem exists_unit_mul_zpow_order
    {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {t : X.presheaf.stalk x} (ht : Irreducible t)
    {f : X.functionField} (hf : f ≠ 0) :
    ∃ u : (X.presheaf.stalk x)ˣ,
      f = algebraMap (X.presheaf.stalk x) X.functionField (u : X.presheaf.stalk x) *
        algebraMap (X.presheaf.stalk x) X.functionField t ^ X.ord f x := by
  have hf_order : Ring.ordFrac (X.presheaf.stalk x) f = WithZero.exp (X.ord f x) := by
    exact (AlgebraicGeometry.Scheme.ord_eq_iff hx hf).mp rfl
  have hpow : Ring.ordFrac (X.presheaf.stalk x)
      (algebraMap (X.presheaf.stalk x) X.functionField t ^ X.ord f x) =
      Ring.ordFrac (X.presheaf.stalk x) f := by
    rw [map_zpow₀, Ring.ordFrac_irreducible ht, hf_order, ← WithZero.exp_zsmul]
    simp
  obtain ⟨u, hu⟩ := Ring.associated_of_ordFrac_eq (R := X.presheaf.stalk x)
    (algebraMap (X.presheaf.stalk x) X.functionField t ^ X.ord f x) f hpow
  exact ⟨u, by simpa [Units.smul_def, Algebra.smul_def] using hu.symm⟩



theorem log_deriv_mul_zpow
    {R K : Type*} [CommRing R] [Field K] [Algebra R K]
    (D : Derivation R K K) {u t : K} (hu : u ≠ 0) (ht : t ≠ 0) (n : ℤ) :
    D (u * t ^ n) / (u * t ^ n) = D u / u + (n : K) * (D t / t) := by
  rw [D.leibniz, D.leibniz_zpow]
  simp only [smul_eq_mul, zsmul_eq_mul, zpow_sub₀ ht, zpow_one]
  field_simp
  ring

theorem exists_rescaled_log_deriv_lift
    {R A K L : Type*} [CommRing R] [CommRing A] [Field K] [Field L]
    [Algebra R A] [Algebra R K]
    (φ : A →+* K) (ψ : A →+* L)
    (d : Derivation R A A) (D : Derivation R K K)
    (hD : ∀ a, D (φ a) = φ (d a))
    (u : Aˣ) (t : A) (n : ℤ) (ht : φ t ≠ 0)
    (hres_t : ψ t = 0) :
    ∃ a : A,
      φ a = φ t * (D (φ (u : A) * φ t ^ n) / (φ (u : A) * φ t ^ n)) ∧
      ψ a = (n : L) * ψ (d t) := by
  refine ⟨t * (↑(u⁻¹) : A) * d (u : A) + (n : A) * d t, ?_, ?_⟩
  · have hu : φ (u : A) ≠ 0 := (u.isUnit.map φ).ne_zero
    rw [log_deriv_mul_zpow D hu ht n, hD, hD]
    simp only [map_add, map_mul, map_intCast, map_units_inv]
    field_simp
  · simp [hres_t]

theorem sum_orders_eq_zero_of_kaehler_relation
    {ι k A F E : Type*} [Fintype ι] [Field k] [CommRing A] [Field F] [Field E]
    [Algebra k A] [Algebra k F] [Algebra k E]
    (φ : A →ₐ[k] F) (ψ : A →ₐ[k] E) (hφ : Function.Injective φ)
    (d : Derivation k A A) (D : Derivation k F F)
    (hD : ∀ a, D (φ a) = φ (d a))
    (u : ι → Aˣ) (t : A) (n : ι → ℤ) (c : ι → k) (ht : φ t ≠ 0)
    (hres_t : ψ t = 0) (hres_dt : ψ (d t) ≠ 0)
    (hω : ∑ i, (algebraMap k F (c i) / (φ (u i : A) * φ t ^ n i)) •
      KaehlerDifferential.D k F (φ (u i : A) * φ t ^ n i) = 0) :
    ∑ i, algebraMap k E (c i) * (n i : E) = 0 := by
  have hlog : ∑ i, algebraMap k F (c i) *
      (D (φ (u i : A) * φ t ^ n i) / (φ (u i : A) * φ t ^ n i)) = 0 := by
    simpa only [map_sum, map_smul, map_zero, Derivation.liftKaehlerDifferential_comp_D,
      smul_eq_mul, div_mul_eq_mul_div, mul_div_assoc] using
      congrArg D.liftKaehlerDifferential hω
  choose a ha hres using fun i =>
    exists_rescaled_log_deriv_lift φ.toRingHom ψ.toRingHom d D hD
      (u i) t (n i) ht hres_t
  simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at ha hres
  have hA : ∑ i, algebraMap k A (c i) * a i = 0 := by
    apply hφ
    simp only [map_sum, map_mul, AlgHom.commutes, map_zero]
    simp_rw [ha, mul_left_comm (algebraMap k F _) (φ t)]
    rw [← Finset.mul_sum, hlog, mul_zero]
  have hE : ∑ i, algebraMap k E (c i) * ((n i : E) * ψ (d t)) = 0 := by
    simpa only [map_sum, map_mul, AlgHom.commutes, map_zero, hres] using congrArg ψ hA
  simp_rw [← mul_assoc] at hE
  rw [← Finset.sum_mul] at hE
  exact (mul_eq_zero.mp hE).resolve_right hres_dt



theorem scheme_residue_equation_of_log_form
    {ι k : Type*} [Fintype ι] [Field k] [CharZero k]
    {X : AlgebraicGeometry.Scheme} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsLocallyNoetherian X]
    {x : X} (hx : Order.coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)]
    [Algebra k (X.presheaf.stalk x)] [Algebra k X.functionField]
    [IsScalarTower k (X.presheaf.stalk x) X.functionField]
    [Algebra.EssFiniteType k (X.presheaf.stalk x)]
    (c : ι → k)
    {f : ι → X.functionField} (hf : ∀ i, f i ≠ 0)
    (hω : ∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) :
    ∑ i, c i * (X.ord (f i) x : k) = 0 := by
  let A := X.presheaf.stalk x
  have : Algebra.FormallySmooth k A :=
    formallySmooth_of_essFiniteType_of_discreteValuationRing
  let φ : A →ₐ[k] X.functionField := IsScalarTower.toAlgHom k A X.functionField
  let ψ : A →ₐ[k] IsLocalRing.ResidueField A :=
    IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨d, hd⟩ := Geometry.exists_transverse_derivation_uniformizer (K := k) t ht
  let D : Derivation k X.functionField X.functionField :=
    Geometry.localizeDerivation (nonZeroDivisors A) d
  have hD : ∀ a, D (φ a) = φ (d a) :=
    fun a => Geometry.localizeDerivation_algebraMap (nonZeroDivisors A) d a
  choose u hu using fun i => exists_unit_mul_zpow_order hx ht (hf i)
  have htφ : φ t ≠ 0 := by
    simpa only [φ, IsScalarTower.toAlgHom_apply, map_zero] using
      (IsFractionRing.injective A X.functionField).ne ht.ne_zero
  have hres_t : ψ t = 0 := by
    apply (IsLocalRing.residue_eq_zero_iff t).mpr
    rw [IsLocalRing.mem_maximalIdeal]
    exact ht.not_isUnit
  have hres_dt : ψ (d t) ≠ 0 := by
    change IsLocalRing.residue A (d t) ≠ 0
    rw [hd]
    exact one_ne_zero
  have hω' : ∑ i, (algebraMap k X.functionField (c i) /
      (φ (u i : A) * φ t ^ X.ord (f i) x)) •
      KaehlerDifferential.D k X.functionField
        (φ (u i : A) * φ t ^ X.ord (f i) x) = 0 := by
    have hu' (i) : φ (u i : A) * φ t ^ X.ord (f i) x = f i := (hu i).symm
    simpa only [hu'] using hω
  apply (algebraMap k (IsLocalRing.ResidueField A)).injective
  simpa only [map_sum, map_mul, map_intCast, map_zero] using
    (sum_orders_eq_zero_of_kaehler_relation φ ψ (IsFractionRing.injective A X.functionField)
      d D hD u t (fun i => X.ord (f i) x) c htφ hres_t hres_dt hω')



universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem schemeBaseStalkAlgebra_essFiniteType {R : Type u} [CommRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] (x : X) :
    let := schemeBaseStalkAlgebra f x
    Algebra.EssFiniteType R (X.presheaf.stalk x) := by
  change (schemeBaseToStalk f x).EssFiniteType
  have hbase : (StructureSheaf.toStalk R (f x)).hom.EssFiniteType := by
    let : Algebra R ((Spec.structureSheaf R).presheaf.stalk (f x)) :=
      StructureSheaf.stalkAlgebra R (f x)
    change Algebra.EssFiniteType R ((Spec.structureSheaf R).presheaf.stalk (f x))
    let q : PrimeSpectrum R := f x
    exact Algebra.EssFiniteType.of_isLocalization _ q.asIdeal.primeCompl
  exact hbase.comp (LocallyOfFiniteType.stalkMap f x)

theorem schemeBaseStalkAlgebra_isScalarTower {R : Type u} [CommRing R]
    {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (CommRingCat.of R)) (x : X) :
    let := schemeBaseStalkAlgebra f x
    let : Algebra R X.functionField := schemeBaseStalkAlgebra f (genericPoint X)
    IsScalarTower R (X.presheaf.stalk x) X.functionField := by
  let := schemeBaseStalkAlgebra f x
  let : Algebra R X.functionField := schemeBaseStalkAlgebra f (genericPoint X)
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, by simp⟩⟩
  apply IsScalarTower.of_algebraMap_eq'
  ext a
  change schemeBaseToStalk f (genericPoint X) a =
    algebraMap (X.presheaf.stalk x) X.functionField (schemeBaseToStalk f x a)
  simp only [schemeBaseToStalk_eq_global_germ, RingHom.comp_apply]
  exact (X.algebraMap_germ_eq_germToFunctionField (show x ∈ (⊤ : X.Opens) by simp) _).symm

end WeightedTorusJets

namespace WeightedTorusJets

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem scheme_residue_equation_of_locallyOfFiniteType
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    {x : X} (hx : Order.coheight x = 1)
    [IsIntegrallyClosed (X.presheaf.stalk x)]
    (c : ι → k) (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∑ i, c i * (X.ord (f i) x : k) = 0 := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω
  let := schemeBaseStalkAlgebra p x
  have : Algebra.EssFiniteType k (X.presheaf.stalk x) :=
    schemeBaseStalkAlgebra_essFiniteType p x
  have : IsScalarTower k (X.presheaf.stalk x) X.functionField :=
    schemeBaseStalkAlgebra_isScalarTower p x
  have : IsDiscreteValuationRing (X.presheaf.stalk x) :=
    Scheme.isDiscreteValuationRing_stalk_of_isIntegrallyClosed hx
  exact scheme_residue_equation_of_log_form hx c hf hω

theorem scheme_orders_zero_of_locallyOfFiniteType_log_form
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∀ i, X.ord (f i) = 0 := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω i
  funext x
  change X.ord (f i) x = 0
  by_cases hx : Order.coheight x = 1
  · exact int_coefficients_eq_zero_of_sum_eq_zero hc
      (scheme_residue_equation_of_locallyOfFiniteType p hx c f hf hω) i
  · exact Scheme.ord_eq_zero_of_coheight_neq_one hx (f i)

theorem scheme_global_units_of_locallyOfFiniteType_log_form
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∀ i, ∃ s : Γ(X, ⊤), IsUnit s ∧
        X.presheaf.germ ⊤ (genericPoint X) (by simp) s = f i := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω i
  apply Scheme.exists_global_unit_of_ord_eq_zero (f i) (hf i)
  intro x
  exact congrFun (scheme_orders_zero_of_locallyOfFiniteType_log_form p c hc f hf hω i) x

end WeightedTorusJets

end
end OriginalSourceGeometryOverlay
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_LogarithmicForm
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

noncomputable section
open Module
open CategoryTheory _root_.AlgebraicGeometry _root_.OAI.Erdos970.AlgebraicGeometry
open CategoryTheory _root_.AlgebraicGeometry
open IsLocalRing
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open _root_.AlgebraicGeometry TopologicalSpace CategoryTheory
open CategoryTheory _root_.AlgebraicGeometry
open MvPolynomial HomogeneousLocalization
open CategoryTheory _root_.AlgebraicGeometry
open _root_.Polynomial IsLocalRing TensorProduct
open TensorProduct IsLocalRing
open scoped TensorProduct
open scoped BigOperators
namespace WeightedTorusJets

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem scheme_coordinates_constant_of_log_form
    {ι : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [UniversallyClosed p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → X.functionField) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    (∑ i, (algebraMap k X.functionField (c i) / f i) •
      KaehlerDifferential.D k X.functionField (f i) = 0) →
      ∀ i, ∃ a : k, algebraMap k X.functionField a = f i := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro hω i
  obtain ⟨s, _, hs⟩ := scheme_global_units_of_locallyOfFiniteType_log_form p c hc f hf hω i
  obtain ⟨a, ha, _⟩ := existsUnique_globalSection_scalar k p s
  refine ⟨a, ?_⟩
  change schemeBaseToStalk p (genericPoint X) a = f i
  rw [schemeBaseToStalk_eq_global_germ, RingHom.comp_apply, ha]
  exact hs

end WeightedTorusJets

namespace WeightedTorusJets

theorem logarithmic_relation_map_algHom
    {ι k F L : Type*} [Fintype ι] [Field k] [Field F] [Field L]
    [Algebra k F] [Algebra k L]
    (φ : F →ₐ[k] L) (c : ι → k) (f : ι → F)
    (h : ∑ i, (algebraMap k F (c i) / f i) • KaehlerDifferential.D k F (f i) = 0) :
    ∑ i, (algebraMap k L (c i) / φ (f i)) •
      KaehlerDifferential.D k L (φ (f i)) = 0 := by
  algebraize [φ.toRingHom]
  have hm := congrArg (KaehlerDifferential.map k k F L) h
  rw [map_zero] at hm
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  simp only [map_sum, map_smul, KaehlerDifferential.map_D]
  apply Finset.sum_congr rfl
  intro i _
  symm
  rw [← IsScalarTower.algebraMap_smul L, map_div₀,
    IsScalarTower.algebraMap_apply k F L]
  rfl



universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem coordinates_constant_of_log_form_via_normal_model
    {ι F : Type*} [Fintype ι] {k : Type u} [Field k] [CharZero k] [IsAlgClosed k]
    [Field F] [Algebra k F]
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    [∀ x : X, IsIntegrallyClosed (X.presheaf.stalk x)]
    (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p] [UniversallyClosed p]
    (c : ι → k) (hc : LinearIndependent ℚ c)
    (f : ι → F) (hf : ∀ i, f i ≠ 0) :
    let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
    ∀ _φ : F →ₐ[k] X.functionField,
      (∑ i, (algebraMap k F (c i) / f i) • KaehlerDifferential.D k F (f i) = 0) →
      ∀ i, ∃ a : k, algebraMap k F a = f i := by
  let : Algebra k X.functionField := schemeBaseStalkAlgebra p (genericPoint X)
  dsimp only
  intro φ hω i
  have hf' (i) : φ (f i) ≠ 0 := by
    intro hz
    apply hf i
    apply φ.injective
    change φ (f i) = φ 0
    simpa only [map_zero] using hz
  obtain ⟨a, ha⟩ := scheme_coordinates_constant_of_log_form p c hc
    (fun i => φ (f i)) hf' (logarithmic_relation_map_algHom φ c f hω) i
  refine ⟨a, ?_⟩
  apply φ.injective
  change φ (algebraMap k F a) = φ (f i)
  exact (φ.commutes a).trans ha

end WeightedTorusJets

namespace WeightedTorusJets

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

theorem laurent_range_mem_intermediateField
    (q : AddMonoidAlgebra K (ι →₀ ℤ) →ₐ[K] L) (S : IntermediateField K L)
    (h : ∀ i, q (AddMonoidAlgebra.single (Finsupp.single i 1) 1) ∈ S)
    (p : AddMonoidAlgebra K (ι →₀ ℤ)) : q p ∈ S := by
  have hm (m : ι →₀ ℤ) : q (AddMonoidAlgebra.single m 1) ∈ S := by
    induction m using Finsupp.induction_linear with
    | zero => change q 1 ∈ S; simp
    | add m n hm hn =>
        rw [show AddMonoidAlgebra.single (m + n) (1 : K) =
          AddMonoidAlgebra.single m 1 * AddMonoidAlgebra.single n 1 by simp, map_mul]
        exact S.mul_mem hm hn
    | single i z =>
        let f := q.toMonoidHom.comp (AddMonoidAlgebra.of K (ι →₀ ℤ))
        have hz : q (AddMonoidAlgebra.single (Finsupp.single i z) 1) =
            q (AddMonoidAlgebra.single (Finsupp.single i 1) 1) ^ z := by
          simpa [f, ← ofAdd_zsmul, Finsupp.smul_single, zsmul_eq_mul] using
            map_zpow f (Multiplicative.ofAdd (Finsupp.single i 1)) z
        rw [hz]
        exact S.toSubfield.zpow_mem (h i) z
  induction p using AddMonoidAlgebra.induction_on with
  | of m => exact hm m
  | add p r hp hr => rw [map_add]; exact S.add_mem hp hr
  | smul c p hp => rw [map_smul, Algebra.smul_def]; exact S.mul_mem (S.algebraMap_mem c) hp

theorem laurent_quotient_exists_nonconstant_coordinate
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime]
    (hdim : 0 < ringKrullDim (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P)) :
    ∃ i, ¬ ∃ c : K,
      algebraMap _ (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
          (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1)) =
        algebraMap K (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P)) c := by
  by_contra! h
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  let j : B →ₐ[K] FractionRing B := IsScalarTower.toAlgHom K B (FractionRing B)
  have hsurj : Function.Surjective (algebraMap K B) := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K P b
    have hp := laurent_range_mem_intermediateField
      (j.comp (Ideal.Quotient.mkₐ K P)) (⊥ : IntermediateField K (FractionRing B))
      (fun i ↦ IntermediateField.mem_bot.mpr (by
        obtain ⟨c, hc⟩ := h i
        exact ⟨c, hc.symm⟩)) p
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp hp
    refine ⟨c, IsFractionRing.injective B (FractionRing B) ?_⟩
    exact (j.commutes c).trans hc
  have hle := ringKrullDim_le_of_surjective (algebraMap K B) hsurj
  have hzero : ringKrullDim K = 0 := Order.krullDim_eq_zero_of_unique
  rw [hzero] at hle
  exact (not_lt_of_ge hle) hdim

theorem laurent_finiteType [Finite ι] :
    Algebra.FiniteType K (AddMonoidAlgebra K (ι →₀ ℤ)) := by
  apply AddMonoidAlgebra.finiteType_iff_group_fg.mpr
  exact AddGroup.fg_of_surjective
    (f := (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).symm.toAddMonoidHom)
    (Finsupp.linearEquivFunOnFinite ℤ ℤ ι).symm.surjective

end WeightedTorusJets

open scoped BigOperators


namespace WeightedTorusJets.Geometry

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem logarithmicForm_ne_zero_on_torus_subvariety_of_normal_model
    {K : Type u} {ι : Type} [Field K] [CharZero K] [IsAlgClosed K] [Fintype ι]
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime]
    (hdim : 0 < ringKrullDim (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
    (c : ι → K) (hc : LinearIndependent ℚ c)
    {N : Scheme.{u}} [IsIntegral N] [IsLocallyNoetherian N]
    [∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)]
    (p : N ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [UniversallyClosed p] :
    let : Algebra K N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
    ∀ _φ : FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P) →ₐ[K] N.functionField,
      logarithmicForm c (fun i ↦ algebraMap _
        (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
          (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) ≠ 0 := by
  let : Algebra K N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  dsimp only
  intro φ hform
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  let q : AddMonoidAlgebra K (ι →₀ ℤ) →ₐ[K] FractionRing B :=
    (IsScalarTower.toAlgHom K B (FractionRing B)).comp (Ideal.Quotient.mkₐ K P)
  have hf (i : ι) : q (AddMonoidAlgebra.single (Finsupp.single i 1) 1) ≠ 0 :=
    ((Group.isUnit (Multiplicative.ofAdd (Finsupp.single i 1))).map
      (q.toMonoidHom.comp (AddMonoidAlgebra.of K (ι →₀ ℤ)))).ne_zero
  have hconst := coordinates_constant_of_log_form_via_normal_model p c hc
    (fun i => q (AddMonoidAlgebra.single (Finsupp.single i 1) 1)) hf φ
    (by simpa only [logarithmicForm, div_eq_mul_inv, q, B, AlgHom.comp_apply,
      IsScalarTower.toAlgHom_apply, Ideal.Quotient.mkₐ_eq_mk] using hform)
  obtain ⟨i, hi⟩ := laurent_quotient_exists_nonconstant_coordinate P hdim
  obtain ⟨a, ha⟩ := hconst i
  exact hi ⟨a, ha.symm⟩

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

universe u

open CategoryTheory _root_.AlgebraicGeometry

theorem logarithmicForm_ne_zero_on_torus_subvariety
    {K : Type u} {ι : Type} [Field K] [CharZero K] [IsAlgClosed K] [Fintype ι]
    (P : Ideal (AddMonoidAlgebra K (ι →₀ ℤ))) [P.IsPrime]
    (hdim : 0 < ringKrullDim (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
    (c : ι → K) (hc : LinearIndependent ℚ c) :
    logarithmicForm c (fun i ↦ algebraMap _
      (FractionRing (AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P))
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) ≠ 0 := by
  let B := AddMonoidAlgebra K (ι →₀ ℤ) ⧸ P
  have : Algebra.FiniteType K (AddMonoidAlgebra K (ι →₀ ℤ)) := laurent_finiteType
  obtain ⟨N, hN, hrest⟩ := exists_normal_proper_model_of_finiteType_domain K B
  let := hN
  obtain ⟨p, hNoeth, hNormal, hFT, hClosed, hφ⟩ := hrest
  have := hNoeth
  have := hFT
  have := hClosed
  have : ∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x) := hNormal
  let : Algebra K N.functionField := schemeBaseStalkAlgebra p (genericPoint N)
  obtain ⟨φ⟩ := hφ
  exact logarithmicForm_ne_zero_on_torus_subvariety_of_normal_model P hdim c hc p φ

end WeightedTorusJets.Geometry






end

open Module CategoryTheory _root_.AlgebraicGeometry
open scoped BigOperators TensorProduct

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_NormalizationPresentationLocalEquiv
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isIntegral _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
section
section
open scoped BigOperators
open Module
open MvPolynomial
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section

open Module TensorProduct

namespace WeightedTorusJets.Geometry

variable {R : Type*} [CommRing R] (I p : Ideal R) [p.IsPrime]

variable {K : Type*} [Field K]

theorem regular_localization_component [IsRegularRing R]
    (M : Submonoid R) (q : Ideal (Localization M)) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) :=
  IsRegularLocalRing.of_ringEquiv
    (IsLocalization.localizationLocalizationAtPrimeIsoLocalization M q).toRingEquiv

end WeightedTorusJets.Geometry

end
end
end
end
end
end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_PolynomialLaurent
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra _root_.OAI.Erdos970.WeightedTorusJets.affineFunctionFieldAlgebra _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isIntegral _root_.OAI.Erdos970.WeightedTorusJets.schemeImage_isSeparated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

section SamePrimeDimensionPrerequisites

namespace WeightedTorusJets.Geometry

theorem prime_height_eq_under_of_integral_goingDown
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  let f := PrimeSpectrum.comap (algebraMap R S)
  have hf : StrictMono f := by
    intro p q hpq
    exact Ideal.IsIntegral.comap_lt_comap (R := R) (I := p.asIdeal) (J := q.asIdeal) hpq
  have hlift : ∀ a : PrimeSpectrum S, ∀ b : PrimeSpectrum R, b < f a →
      ∃ a' : PrimeSpectrum S, a' < a ∧ f a' = b := by
    intro a b hba
    obtain ⟨Q, hQa, hQ, hQb⟩ :=
      Ideal.exists_ideal_lt_liesOver_of_lt a.asIdeal hba
    let := hQ
    let := hQb
    refine ⟨⟨Q, hQ⟩, hQa, ?_⟩
    apply PrimeSpectrum.ext
    exact (Q.over_def b.asIdeal).symm
  have h := Order.height_eq_of_strictMono f hf hlift
    (⟨P, inferInstance⟩ : PrimeSpectrum S)
  rw [← PrimeSpectrum.height_eq_orderHeight,
    ← PrimeSpectrum.height_eq_orderHeight] at h
  exact h



theorem maximal_height_eq_ringKrullDim_of_finiteType
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (P : Ideal A) [P.IsMaximal] :
    (P.height : WithBot ℕ∞) = ringKrullDim A := by
  obtain ⟨n, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg K A
  let : Algebra (MvPolynomial (Fin n) K) A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral (MvPolynomial (Fin n) K) A := ⟨hint⟩
  let : FaithfulSMul (MvPolynomial (Fin n) K) A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  let : (P.under (MvPolynomial (Fin n) K)).IsMaximal :=
    inferInstance
  rw [prime_height_eq_under_of_integral_goingDown (R := MvPolynomial (Fin n) K) P,
    maximal_polynomial_height n (P.under (MvPolynomial (Fin n) K)),
    ringKrullDim_eq_of_integral_faithful_goingDown (R := MvPolynomial (Fin n) K)]
  simp

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

universe uK uA uF uC uE

theorem altitude_of_relative_fraction_fields
    {K : Type uK} {A : Type uA} {F : Type uF} {C : Type uC} {E : Type uE}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    [Field F] [Algebra K F] [CommRing C] [IsDomain C] [Algebra F C]
    [Algebra.FiniteType F C] [Field E] [Algebra K E] [Algebra A E]
    [IsScalarTower K A E] [IsFractionRing A E] [Algebra F E] [Algebra C E]
    [IsScalarTower F C E] [IsFractionRing C E] [IsScalarTower K F E]
    (p : Ideal A) [p.IsPrime] (P : Ideal C) [P.IsMaximal]
    (hpht : p.height = P.height)
    (hF : Cardinal.lift.{uA} (Algebra.trdeg K F) =
      Cardinal.lift.{uF} (Algebra.trdeg K (A ⧸ p))) :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  obtain ⟨nA, hdimA, htrdegA⟩ := finiteType_dimension_trdeg (K := K) (A := A)
  obtain ⟨nC, hdimC, htrdegC⟩ := finiteType_dimension_trdeg (K := F) (A := C)
  obtain ⟨nQ, hdimQ, htrdegQ⟩ := finiteType_dimension_trdeg (K := K) (A := A ⧸ p)
  have hAE : Algebra.trdeg K E = nA := fractionField_trdeg_eq_nat nA htrdegA
  have hCE : Algebra.trdeg F E = nC := fractionField_trdeg_eq_nat nC htrdegC
  have hKF : Algebra.trdeg K F = nQ := by simpa [htrdegQ] using hF
  have htower := lift_trdeg_add_eq K F E
  have hsum : nQ + nC = nA := by
    simpa [hKF, hCE, hAE, ← Nat.cast_add] using htower
  rw [hpht, maximal_height_eq_ringKrullDim_of_finiteType (K := F), hdimC, hdimQ,
    hdimA, ← Nat.cast_add, Nat.add_comm nC nQ, hsum]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem exists_injective_polynomial_quotient_lift
    {K A ι : Type*} [CommRing K] [CommRing A] [Algebra K A]
    (p : Ideal A) (g : MvPolynomial ι K →ₐ[K] A ⧸ p)
    (hinj : Function.Injective g) :
    ∃ f : MvPolynomial ι K →ₐ[K] A,
      (Ideal.Quotient.mkₐ K p).comp f = g ∧ Function.Injective f := by
  classical
  choose x hx using fun i : ι => Ideal.Quotient.mkₐ_surjective K p (g (MvPolynomial.X i))
  let f : MvPolynomial ι K →ₐ[K] A := MvPolynomial.aeval x
  have hf : (Ideal.Quotient.mkₐ K p).comp f = g := by
    ext i
    simpa [f] using hx i
  refine ⟨f, hf, ?_⟩
  intro a b hab
  apply hinj
  simpa only [← hf, AlgHom.comp_apply] using congrArg (Ideal.Quotient.mkₐ K p) hab

theorem polynomial_quotient_lift_properties
    {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
    (p : Ideal A) [p.IsPrime] (f : MvPolynomial ι K →ₐ[K] A)
    (g : MvPolynomial ι K →ₐ[K] A ⧸ p)
    (hf : (Ideal.Quotient.mkₐ K p).comp f = g)
    (hinj : Function.Injective g) (hint : g.IsIntegral) :
    let : Algebra (MvPolynomial ι K) A := f.toRingHom.toAlgebra
    p.under (MvPolynomial ι K) = ⊥ ∧
      Algebra.IsIntegral (MvPolynomial ι K) (A ⧸ p) ∧
      Algebra.algebraMapSubmonoid A (nonZeroDivisors (MvPolynomial ι K)) ≤ p.primeCompl := by
  let : Algebra (MvPolynomial ι K) A := f.toRingHom.toAlgebra
  have hm : algebraMap (MvPolynomial ι K) (A ⧸ p) = g.toRingHom := by
    apply RingHom.ext
    intro b
    exact congrArg (fun h : MvPolynomial ι K →ₐ[K] A ⧸ p => h b) hf
  have hzero (b : MvPolynomial ι K) (hb : f b ∈ p) : b = 0 := by
    apply hinj
    rw [map_zero, ← hf, AlgHom.comp_apply]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hb
  refine ⟨?_, ⟨?_, ?_⟩⟩
  · apply le_antisymm _ bot_le
    intro b hb
    exact Ideal.mem_bot.mpr (hzero b hb)
  · constructor
    intro b
    change (algebraMap (MvPolynomial ι K) (A ⧸ p)).IsIntegralElem b
    rw [hm]
    exact hint b
  · rintro b ⟨c, hc, rfl⟩
    change f c ∉ p
    intro hp
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hc) (hzero c hp)



theorem localized_prime_isMaximal_of_quotient_integral
    {B A : Type*} [CommRing B] [IsDomain B] [CommRing A] [Algebra B A]
    (C : Type*) [CommRing C] [Algebra A C]
    [IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)) C]
    (p : Ideal A) [p.IsPrime] (hp : p.under B = ⊥)
    [Algebra.IsIntegral B (A ⧸ p)] :
    (p.map (algebraMap A C)).IsMaximal := by
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors B)
  have hdisj : Disjoint (M : Set A) (p : Set A) := by
    apply Set.disjoint_left.mpr
    rintro a ⟨b, hb, rfl⟩ ha
    have hbp : b ∈ p.under B := ha
    rw [hp] at hbp
    exact nonZeroDivisors.ne_zero hb hbp
  have : (p.map (algebraMap A C)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M C p inferInstance hdisj
  let Q := C ⧸ p.map (algebraMap A C)
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ p) (nonZeroDivisors B)) Q := by
    simpa only [M, Algebra.algebraMapSubmonoid_map_map] using
      (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ p) M) Q)
  let f : FractionRing B →+* Q := IsLocalization.map Q (algebraMap B (A ⧸ p))
    (show nonZeroDivisors B ≤
      (Algebra.algebraMapSubmonoid (A ⧸ p) (nonZeroDivisors B)).comap _ from
        (nonZeroDivisors B).le_comap_map)
  let : Algebra (FractionRing B) Q := f.toAlgebra
  have : Algebra.IsIntegral (FractionRing B) Q :=
    ⟨isIntegral_localization (M := nonZeroDivisors B)⟩
  apply Ideal.Quotient.maximal_of_isField
  exact isField_of_isIntegral_of_isField' (R := FractionRing B) (S := Q) (Field.toIsField _)



variable {B A : Type*} [CommRing B] [CommRing A] [IsDomain A]
  [Algebra B A] [FaithfulSMul B A]

attribute [local instance] relativeLocalizationFractionAlgebra

attribute [local instance] relativeLocalizationFraction_scalarTower

attribute [local instance] FractionRing.liftAlgebra

theorem relativeLocalization_fractionBase_scalarTower :
    IsScalarTower (FractionRing B)
      (Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B)))
      (FractionRing A) := by
  let C := Localization (Algebra.algebraMapSubmonoid A (nonZeroDivisors B))
  have : IsScalarTower B C (FractionRing A) := IsScalarTower.to₁₃₄ B A C (FractionRing A)
  apply IsScalarTower.of_algebraMap_eq'
  apply IsLocalization.ringHom_ext (nonZeroDivisors B)
  ext b
  simp only [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply]

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem prime_height_add_quotient_dim_eq_of_finiteType
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : Ideal A) [p.IsPrime] :
    (p.height : WithBot ℕ∞) + ringKrullDim (A ⧸ p) = ringKrullDim A := by
  obtain ⟨n, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K (A ⧸ p)
  obtain ⟨f, hf, hfinj⟩ := exists_injective_polynomial_quotient_lift p g hginj
  let B := MvPolynomial (Fin n) K
  let : Algebra B A := f.toRingHom.toAlgebra
  let : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hfinj
  obtain ⟨hpB, hqint, hdenom⟩ := polynomial_quotient_lift_properties p f g hf hginj hgint
  let : Algebra.IsIntegral B (A ⧸ p) := hqint
  let : Algebra.FiniteType B A := Algebra.FiniteType.of_restrictScalars_finiteType K B A
  let M := Algebra.algebraMapSubmonoid A (nonZeroDivisors B)
  let C := Localization M
  let : IsDomain C := IsLocalization.isDomain_of_le_nonZeroDivisors C
    (relative_denominators_le_nonZeroDivisors (B := B) (A := A))
  let : Algebra.FiniteType (FractionRing B) C := Algebra.FiniteType.equiv inferInstance
    (Localization.tensorRightAlgEquiv (nonZeroDivisors B) A)
  let P := p.map (algebraMap A C)
  let : P.IsMaximal := localized_prime_isMaximal_of_quotient_integral C p hpB
  have hdisj : Disjoint (M : Set A) (p : Set A) := by
    apply Set.disjoint_left.mpr
    intro a ha hpa
    exact hdenom ha hpa
  have hpht : p.height = P.height := by
    have hu : P.under A = p := IsLocalization.under_map_of_isPrime_disjoint M C
      inferInstance hdisj
    simpa only [hu] using IsLocalization.height_under M P
  let : Algebra C (FractionRing A) := relativeLocalizationFractionAlgebra
  let : IsScalarTower A C (FractionRing A) := relativeLocalizationFraction_scalarTower
  let : IsFractionRing C (FractionRing A) :=
    IsFractionRing.isFractionRing_of_isLocalization M _ _
      (relative_denominators_le_nonZeroDivisors (B := B) (A := A))
  let : Algebra (FractionRing B) (FractionRing A) := FractionRing.liftAlgebra B (FractionRing A)
  let : IsScalarTower (FractionRing B) C (FractionRing A) :=
    relativeLocalization_fractionBase_scalarTower
  have hqtr : Algebra.trdeg K (A ⧸ p) = n :=
    trdeg_eq_of_integral_polynomial_base n g hginj hgint
  have hftr : Algebra.trdeg K (FractionRing B) = n :=
    fractionField_trdeg_eq_nat (K := K) (A := B) (F := FractionRing B) n
      (by simp [B, MvPolynomial.trdeg_of_isDomain])
  apply altitude_of_relative_fraction_fields (K := K) (F := FractionRing B)
    (C := C) (E := FractionRing A) p P hpht
  simp [hftr, hqtr]



variable {K : Type*} [Field K]

theorem localization_mvPolynomial_ringKrullDim_le (n : ℕ)
    (M : Submonoid (MvPolynomial (Fin n) K))
    (S : Type*) [CommRing S] [Algebra (MvPolynomial (Fin n) K) S] [IsLocalization M S] :
    ringKrullDim S ≤ n := by
  apply (ringKrullDim_le_iff_height_le _).mpr
  intro p hp
  have := hp
  rw [← IsLocalization.height_under M p]
  have h := (p.under (MvPolynomial (Fin n) K)).height_le_ringKrullDim_of_isPrime
  simpa using h

theorem torus_chart_ringKrullDim (n : ℕ) :
    ringKrullDim (Localization.Away (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K))) = n := by
  let R := MvPolynomial (Fin n) K
  let t : R := ∏ i : Fin n, MvPolynomial.X i
  let T := Localization.Away t
  have hle : ringKrullDim T ≤ n :=
    localization_mvPolynomial_ringKrullDim_le n (Submonoid.powers t) T
  apply le_antisymm hle
  let p : Ideal R := RingHom.ker (MvPolynomial.eval (fun _ : Fin n ↦ (1 : K)))
  have hp : p.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (by
    intro c
    exact ⟨MvPolynomial.C c, MvPolynomial.eval_C c⟩)
  have hdisj : Disjoint (Submonoid.powers t : Set R) (p : Set R) := by
    apply (Ideal.disjoint_powers_iff_notMem_of_isPrime t).mpr
    change MvPolynomial.eval (fun _ : Fin n ↦ (1 : K))
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ≠ 0
    simp only [map_prod, MvPolynomial.eval_X, Finset.prod_const_one, ne_eq, one_ne_zero, not_false_eq_true]
  have hpT : (p.map (algebraMap R T)).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers t) T p hp.isPrime hdisj
  have hheight : (p.map (algebraMap R T)).height = n := by
    rw [IsLocalization.height_map_of_disjoint (Submonoid.powers t) p hdisj]
    exact maximal_polynomial_height n p
  have h := (p.map (algebraMap R T)).height_le_ringKrullDim_of_isPrime
  simpa [hheight] using h

end WeightedTorusJets.Geometry

namespace WeightedTorusJets.Geometry

theorem torus_component_cotangent_eq_codimension {K : Type*} [Field K] (n : ℕ)
    (q : Ideal (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)))) [q.IsPrime] :
    Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) =
      n - ((ringKrullDim (Localization.Away
        (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ⧸ q)).unbotD 0).toNat := by
  let R := MvPolynomial (Fin n) K
  let t : R := ∏ i : Fin n, MvPolynomial.X i
  let T := Localization.Away t
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ MvPolynomial.X_ne_zero i
  have : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T
    (powers_le_nonZeroDivisors_of_noZeroDivisors ht)
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    regular_localization_component (Submonoid.powers t) q
  have hheight : (Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) : WithBot ℕ∞) = q.height :=
    ((IsRegularLocalRing.iff_finrank_cotangentSpace (Localization.AtPrime q)).mp inferInstance).trans
      (IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q))
  have htotal := prime_height_add_quotient_dim_eq_of_finiteType (K := K) q
  rw [torus_chart_ringKrullDim, ← hheight] at htotal
  obtain ⟨d, hquot, _⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := T ⧸ q)
  change Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) =
    n - ((ringKrullDim (T ⧸ q)).unbotD 0).toNat
  have hsum : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) + d = n := by
    rw [show ringKrullDim (Localization.Away
      (∏ i : Fin n, (MvPolynomial.X i : MvPolynomial (Fin n) K)) ⧸ q) =
        (d : WithBot ℕ∞) from hquot] at htotal
    exact_mod_cast htotal
  simpa [hquot] using Nat.eq_sub_of_add_eq hsum

end WeightedTorusJets.Geometry

end SamePrimeDimensionPrerequisites

section

namespace WeightedTorusJets.Geometry

theorem localization_residue_algEquiv_algebraMap {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] (x : R) :
    localizationResidueAlgEquiv (A := A) p (algebraMap R p.ResidueField x) =
      algebraMap R (IsLocalRing.ResidueField A) x :=
  (localizationResidueAlgEquiv (A := A) p).commutes x

theorem localization_residue_isFractionRing {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p]
    [Algebra (R ⧸ p) (IsLocalRing.ResidueField A)]
    [IsScalarTower R (R ⧸ p) (IsLocalRing.ResidueField A)] :
    IsFractionRing (R ⧸ p) (IsLocalRing.ResidueField A) :=
  IsFractionRing.of_algEquiv
    ((localizationResidueAlgEquiv (A := A) p).extendScalarsOfSurjective
      (S := R ⧸ p) Ideal.Quotient.mk_surjective)

theorem localization_residue_quotientAlgebra_data {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] :
    let : Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
      localizationResidueQuotientAlgebra (A := A) p
    IsScalarTower R (R ⧸ p) (IsLocalRing.ResidueField A) ∧
      IsFractionRing (R ⧸ p) (IsLocalRing.ResidueField A) := by
  let : Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
    localizationResidueQuotientAlgebra (A := A) p
  have h : IsScalarTower R (R ⧸ p) (IsLocalRing.ResidueField A) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (localization_residue_algEquiv_algebraMap (A := A) p x).symm
  exact ⟨h, localization_residue_isFractionRing p⟩

theorem localization_residue_quotientAlgebra_mk {R A : Type*} [CommRing R]
    [CommRing A] [IsLocalRing A] [Algebra R A]
    (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime A p] (x : R) :
    let : Algebra (R ⧸ p) (IsLocalRing.ResidueField A) :=
      localizationResidueQuotientAlgebra (A := A) p
    algebraMap (R ⧸ p) (IsLocalRing.ResidueField A) (Ideal.Quotient.mk p x) =
      algebraMap R (IsLocalRing.ResidueField A) x :=
  localization_residue_algEquiv_algebraMap (A := A) p x

end WeightedTorusJets.Geometry

end

end

end Erdos970

end OAI
end

section
-- module Solutions.OAIQ247_JB.Jacobsthal_Siegel_TorusQuotientDimensionPosCotangentFinrankThree
attribute [-instance] _root_.OAI.Erdos970.WeightedTorusJets.Geometry.spec_stalk_presheaf_algebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section
namespace WeightedTorusJets.Geometry

theorem torus_quotient_dimension_pos_of_cotangent_finrank_le_three
    {K : Type*} [Field K]
    (q : Ideal (Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) [q.IsPrime]
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≤ 3) :
    0 < ringKrullDim (Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) ⧸ q) := by
  obtain ⟨d, hd, _⟩ := WeightedTorusJets.finiteType_dimension_trdeg
    (K := K) (A := Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)) ⧸ q)
  have hrank : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) = 4 - d := by
    simpa [hd] using
      torus_component_cotangent_eq_codimension (K := K) 4 q
  have hpos : 0 < d := by omega
  rw [hd]
  exact_mod_cast hpos

theorem laurent_quotient_dimension_pos_of_torus_cotangent_finrank_le_three
    {K : Type*} [Field K]
    (q : Ideal (Localization.Away
      (∏ i : Fin 4, (MvPolynomial.X i : MvPolynomial (Fin 4) K)))) [q.IsPrime]
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q)) ≤ 3) :
    0 < ringKrullDim (AddMonoidAlgebra K (Fin 4 →₀ ℤ) ⧸
      q.comap (laurentEquivLocalization K (Fin 4)).toRingHom) := by
  let e := laurentEquivLocalization K (Fin 4)
  have he : q = (q.comap e.toRingHom).map e.toRingHom :=
    (Ideal.map_comap_of_surjective e.toRingHom e.surjective q).symm
  rw [ringKrullDim_eq_of_ringEquiv
    (Ideal.quotientEquivAlg _ q e he).toRingEquiv]
  exact torus_quotient_dimension_pos_of_cotangent_finrank_le_three q hdim



open MvPolynomial

theorem torus_prime_fractionField_residue_equiv
    {K : Type*} [Field K]
    (q : PrimeSpectrum (Localization.Away
      (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K)))) :
    let L := AddMonoidAlgebra K (Fin 4 →₀ ℤ)
    let T := Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))
    let P := q.asIdeal.comap (laurentEquivLocalization K (Fin 4)).toRingHom
    let S := Localization.AtPrime q.asIdeal
    ∃ E : FractionRing (L ⧸ P) ≃ₐ[K] IsLocalRing.ResidueField S,
      ∀ i : Fin 4, E (algebraMap (L ⧸ P) (FractionRing (L ⧸ P))
        (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) =
          algebraMap T (IsLocalRing.ResidueField S)
            (algebraMap (MvPolynomial (Fin 4) K) T (X i)) := by
  dsimp only
  let L := AddMonoidAlgebra K (Fin 4 →₀ ℤ)
  let T := Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))
  let e := laurentEquivLocalization K (Fin 4)
  let P := q.asIdeal.comap e.toRingHom
  let S := Localization.AtPrime q.asIdeal
  let F := IsLocalRing.ResidueField S
  have : P.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  let : Algebra (T ⧸ q.asIdeal) F := localizationResidueQuotientAlgebra (A := S) q.asIdeal
  obtain ⟨htower, hfrac⟩ := localization_residue_quotientAlgebra_data (A := S) q.asIdeal
  have : IsScalarTower K (T ⧸ q.asIdeal) F := by
    apply IsScalarTower.of_algebraMap_eq' (R := K) (S := T ⧸ q.asIdeal) (A := F)
    ext c
    change algebraMap K F c = algebraMap (T ⧸ q.asIdeal) F
      (Ideal.Quotient.mk q.asIdeal (algebraMap K T c))
    rw [localization_residue_quotientAlgebra_mk]
    exact IsScalarTower.algebraMap_apply K T F c
  let E₀ : (L ⧸ P) ≃ₐ[K] (T ⧸ q.asIdeal) := Ideal.quotientEquivAlg P q.asIdeal e
    (q.asIdeal.map_comap_of_surjective e.toRingHom e.surjective).symm
  let E : FractionRing (L ⧸ P) ≃ₐ[K] F := IsFractionRing.algEquivOfAlgEquiv E₀
  refine ⟨E, fun i ↦ ?_⟩
  rw [IsFractionRing.algEquivOfAlgEquiv_algebraMap]
  change algebraMap (T ⧸ q.asIdeal) F
    (Ideal.Quotient.mk q.asIdeal (e (AddMonoidAlgebra.single (Finsupp.single i 1) 1))) = _
  rw [localization_residue_quotientAlgebra_mk, laurentEquivLocalization_coordinate]

theorem torus_prime_residue_logarithmicForm_ne_zero_jb247_oai
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    (q : PrimeSpectrum (Localization.Away
      (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))))
    (hdim : Module.finrank (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal))
      (IsLocalRing.CotangentSpace (Localization.AtPrime q.asIdeal)) ≤ 3)
    (c : Fin 4 → K) (hc : LinearIndependent ℚ c) :
    let S := Localization.AtPrime q.asIdeal
    logarithmicForm (F := IsLocalRing.ResidueField S) c
      (fun i : Fin 4 ↦ Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)
      (algebraMap (MvPolynomial (Fin 4) K) S (X i))) ≠ 0 := by
  dsimp only
  let L := AddMonoidAlgebra K (Fin 4 →₀ ℤ)
  let T := Localization.Away (∏ i : Fin 4, (X i : MvPolynomial (Fin 4) K))
  let P := q.asIdeal.comap (laurentEquivLocalization K (Fin 4)).toRingHom
  let S := Localization.AtPrime q.asIdeal
  let F := IsLocalRing.ResidueField S
  have : P.IsPrime := Ideal.comap_isPrime _ q.asIdeal
  have hpos := laurent_quotient_dimension_pos_of_torus_cotangent_finrank_le_three
    q.asIdeal hdim
  have hn := logarithmicForm_ne_zero_on_torus_subvariety P hpos c hc
  obtain ⟨E, hE⟩ := torus_prime_fractionField_residue_equiv q
  let x : Fin 4 → FractionRing (L ⧸ P) := fun i ↦ algebraMap (L ⧸ P) _
    (Ideal.Quotient.mk P (AddMonoidAlgebra.single (Finsupp.single i 1) 1))
  have hcoords (i : Fin 4) : E (x i) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal S)
        (algebraMap (MvPolynomial (Fin 4) K) S (X i)) := by
    rw [hE]
    rw [← IsScalarTower.algebraMap_apply (MvPolynomial (Fin 4) K) T F]
    rfl
  dsimp only [S] at hcoords
  intro hzero
  apply hn
  have hm := WeightedTorusJets.logarithmic_relation_map_algHom E.symm.toAlgHom c _
    (by simpa only [logarithmicForm, div_eq_mul_inv] using hzero)
  simpa only [AlgEquiv.coe_toAlgHom, ← hcoords, AlgEquiv.symm_apply_apply,
    logarithmicForm, div_eq_mul_inv] using hm

end WeightedTorusJets.Geometry

end

end Erdos970

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos970.WeightedTorusJets.Geometry.torus_prime_residue_logarithmicForm_ne_zero_jb247_oai.{u_1} := @OAI.Erdos970.WeightedTorusJets.Geometry.torus_prime_residue_logarithmicForm_ne_zero_jb247_oai.{u_1}
