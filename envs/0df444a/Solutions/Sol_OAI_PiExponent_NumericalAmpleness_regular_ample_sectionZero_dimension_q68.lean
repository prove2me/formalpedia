-- Prove2me | solution 1 for OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:26:30.163186+00:00
-- url     : https://prove2.me/submissions/e3325247-e11f-4a3c-b1a9-2fe1763f37a2

import Mathlib
import Definitions.Def_OAIQ068A040
import Definitions.Def_OAIQ068A042
import Theorems.Thm_OAI_PiExponent_NumericalAmpleness_curveDegree_pos_of_ample_q68

section
-- module Solutions.OAIQ068_PI.PiExponent_Geometry_IntegralCurveExistence
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open CategoryTheory AlgebraicGeometry TopologicalSpace Topology Order

namespace PiExponent.NumericalAmpleness

noncomputable section

theorem topologicalKrullDim_irreducibleClosed {X : Type*} [TopologicalSpace X]
    (Z : IrreducibleCloseds X) :
    topologicalKrullDim (Z : Set X) = (Order.height Z : WithBot ℕ∞) := by
  rw [topologicalKrullDim, Order.krullDim_eq_of_orderIso (irreducibleClosedsBelowEquiv Z),
    ← Order.height_eq_krullDim_Iic]

theorem exists_irreducibleClosed_dimension_one (X : Type*) [TopologicalSpace X]
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    ∃ Z : IrreducibleCloseds X, topologicalKrullDim (Z : Set X) = 1 := by
  have hdim' : Order.krullDim (IrreducibleCloseds X) = d := hdim
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hdim'.symm)
  have hlast : (p.length : ℕ∞) = Order.height p.last := by
    apply le_antisymm (Order.length_le_height_last (p := p))
    have hh := Order.height_le_krullDim p.last
    rw [hdim', ← hp] at hh
    exact_mod_cast hh
  have hidx : 1 < p.length + 1 := by omega
  refine ⟨p ⟨1, hidx⟩, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed]
  have hh := Order.height_eq_index_of_length_eq_height_last hlast ⟨1, hidx⟩
  simpa using congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) hh

theorem nonempty_integralCurve_of_dimension_pos (X : Scheme.{0})
    (d : ℕ) (hdim : topologicalKrullDim X = d) (hd : 0 < d) :
    Nonempty (IntegralCurve X) := by
  obtain ⟨Z, hZ⟩ := exists_irreducibleClosed_dimension_one X d hdim hd
  exact ⟨integralCurveOfIrreducibleClosed Z hZ⟩

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleDivisorDimensionBase
attribute [-instance] _root_.OAI.PiExponent.CurveBlowupImage.imageMap_isDominant _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace Order
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

theorem exists_irreducibleClosed_full_dimension (T : Type*) [TopologicalSpace T]
    (n : ℕ) (hdim : topologicalKrullDim T = n) :
    ∃ Z : IrreducibleCloseds T, topologicalKrullDim (Z : Set T) = n := by
  have hdim' : Order.krullDim (IrreducibleCloseds T) = n := hdim
  obtain ⟨p, hp⟩ := Order.le_krullDim_iff.mp (le_of_eq hdim'.symm)
  have hlast : (p.length : ℕ∞) = Order.height p.last := by
    apply le_antisymm (Order.length_le_height_last (p := p))
    have hh := Order.height_le_krullDim p.last
    rw [hdim', ← hp] at hh
    exact_mod_cast hh
  refine ⟨p.last, ?_⟩
  rw [topologicalKrullDim_irreducibleClosed, ← hlast, hp]
  rfl

theorem exists_integral_closed_full_dimension (X : Scheme.{0})
    (n : ℕ) (hdim : topologicalKrullDim X = n) :
    ∃ Y : Scheme.{0}, ∃ i : Y ⟶ X,
      IsClosedImmersion i ∧ IsIntegral Y ∧ topologicalKrullDim Y = n := by
  obtain ⟨Z, hZ⟩ := exists_irreducibleClosed_full_dimension X n hdim
  let C : Closeds X := ⟨Z, Z.isClosed⟩
  let I := Scheme.IdealSheafData.vanishingIdeal C
  have hs : (I.support : Set X) = (Z : Set X) := by
    simp only [I, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have : IsReduced I.subscheme := isReduced_vanishingIdeal_subscheme C
  have : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [hs]
    exact Subtype.irreducibleSpace Z.isIrreducible
  refine ⟨I.subscheme, I.subschemeι, inferInstance,
    isIntegral_of_irreducibleSpace_of_isReduced _, ?_⟩
  change topologicalKrullDim (I.support : Set X) = n
  rw [hs]
  exact hZ

variable {X : Scheme.{0}}

theorem ample_section_has_zero
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 0 < n) :
    ∃ y : X, y ∉ sectionOpen X s := by
  by_contra h
  push Not at h
  have : IsIso s := isIso_of_locally_isIso s (by
    intro x
    exact ⟨isoOpen s, h x, isIso_restrict_isoOpen s⟩)
  obtain ⟨C⟩ := nonempty_integralCurve_of_dimension_pos X n hdim hn
  have hpos := curveDegree_pos_of_ample_q68 p H hH C
  let e : H.sheaf ≅ structureSheaf X := (asIso s).symm
  have he := eulerCharacteristic_iso (C.embedding ≫ p)
    ((Scheme.Modules.pullback C.embedding).mapIso e ≪≫ pullbackUnitIso C.embedding) 1
  have hz : curveDegree p H C = 0 := by
    unfold curveDegree
    change eulerCharacteristic (C.embedding ≫ p) 1
      ((Scheme.Modules.pullback C.embedding).obj H.sheaf) =
      eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme) at he
    rw [he]
    exact sub_self _
  omega

theorem ample_section_zero_nonempty
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) (n : ℕ)
    (hdim : topologicalKrullDim X = n) (hn : 0 < n) :
    Nonempty (zeroIdeal H s).subscheme := by
  obtain ⟨y, hy⟩ := ample_section_has_zero p H hH s n hdim hn
  have hm : y ∈ Set.range (zeroIdeal H s).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, zeroIdeal_support]
    exact hy
  obtain ⟨z, -⟩ := hm
  exact ⟨z⟩

end
end PiExponent.NumericalAmpleness

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrimeHilbertDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section OrderLifting

variable {α β : Type*} [PartialOrder α] [PartialOrder β]

theorem exists_chain_lift_last (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b)
    (p : LTSeries β) :
    ∃ q : LTSeries α, q.length = p.length ∧ f q.last = p.last := by
  induction p using RelSeries.inductionOn' with
  | singleton b =>
      obtain ⟨a, ha⟩ := hs b
      exact ⟨RelSeries.singleton _ a, rfl, ha⟩
  | snoc p b hb ih =>
      obtain ⟨q, hlen, hlast⟩ := ih
      obtain ⟨a, ha, hab⟩ := hu q.last b (hlast.symm ▸ hb)
      refine ⟨q.snoc a ha, ?_, ?_⟩
      · simp only [RelSeries.snoc_length, hlen]
      · simpa only [RelSeries.last_snoc] using hab

theorem krullDim_le_of_goingUp (f : α → β) (hs : Function.Surjective f)
    (hu : ∀ a b, f a < b → ∃ a', a < a' ∧ f a' = b) :
    Order.krullDim β ≤ Order.krullDim α := by
  unfold Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨q, hlen, _⟩ := exists_chain_lift_last f hs hu p
  exact hlen ▸ le_iSup (fun q : LTSeries α => (q.length : WithBot ℕ∞)) q

end OrderLifting

section IntegralDimension

variable {A B : Type*} [CommRing A] [CommRing B]

theorem ringKrullDim_eq_of_integral_injective (f : A →+* B)
    (hf : Function.Injective f) (hi : f.IsIntegral) :
    ringKrullDim B = ringKrullDim A := by
  let : Algebra A B := f.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hi⟩
  let c : PrimeSpectrum B → PrimeSpectrum A :=
    fun p => ⟨p.asIdeal.comap f, inferInstance⟩
  have hc : StrictMono c := by
    intro p q hpq
    obtain ⟨hpq', x, hxq, hxp⟩ := SetLike.lt_iff_le_and_exists.mp (show p.asIdeal < q.asIdeal from hpq)
    exact Ideal.comap_lt_comap_of_integral_mem_sdiff hpq' ⟨hxq, hxp⟩
      (Algebra.IsIntegral.isIntegral x)
  have hs : Function.Surjective c := by
    intro p
    obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      p.asIdeal (⊥ : Ideal B) (by
        change RingHom.ker f ≤ p.asIdeal
        rw [(RingHom.injective_iff_ker_eq_bot f).mp hf]
        exact bot_le)
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
  have hu : ∀ a b, c a < b → ∃ a', a < a' ∧ c a' = b := by
    intro a b hab
    obtain ⟨q, haq, hq, hqb⟩ :=
      Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime b.asIdeal a.asIdeal hab.le
    refine ⟨⟨q, hq⟩, lt_of_le_of_ne haq ?_, PrimeSpectrum.ext hqb⟩
    intro heq
    have he : c a = b := by
      rw [heq]
      exact PrimeSpectrum.ext hqb
    exact hab.ne he
  exact le_antisymm (Order.krullDim_le_of_strictMono c hc)
    (krullDim_le_of_goingUp c hs hu)

end IntegralDimension

variable (k R : Type*) [Field k] [CommRing R] [Nontrivial R] [Algebra k R]
  [Algebra.FiniteType k R]

theorem exists_finite_normalization_with_dimension :
    ∃ s : ℕ, ∃ g : MvPolynomial (Fin s) k →ₐ[k] R,
      Function.Injective g ∧ g.Finite ∧ ringKrullDim R = (s : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  refine ⟨s, g, hg, hfin, ?_⟩
  have hd := ringKrullDim_eq_of_integral_injective g.toRingHom hg hfin.to_isIntegral
  simpa only [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field, ENat.card_eq_coe_natCard, Nat.card_fin, zero_add, WithBot.coe_natCast] using hd

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_AffineTranscendenceDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W24

section Normalization

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B] [Algebra k B]

theorem normalization_trdeg_toNat (s : ℕ)
    (g : MvPolynomial (Fin s) k →ₐ[k] B)
    (hg : Function.Injective g) (hi : g.IsIntegral) :
    (Algebra.trdeg k B).toNat = s := by
  let : Algebra (MvPolynomial (Fin s) k) B := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) B :=
    IsScalarTower.of_algebraMap_eq fun x => (g.commutes x).symm
  have : FaithfulSMul (MvPolynomial (Fin s) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  have : Algebra.IsIntegral (MvPolynomial (Fin s) k) B := ⟨hi⟩
  have : Algebra.IsAlgebraic (MvPolynomial (Fin s) k) B :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral x).isAlgebraic⟩
  have ht := congrArg Cardinal.toNat
    (lift_trdeg_add_eq k (MvPolynomial (Fin s) k) B)
  simpa [trdeg_eq_zero] using ht.symm

theorem finiteType_domain_krullDim_eq_trdeg [Algebra.FiniteType k B] :
    ringKrullDim B = ((Algebra.trdeg k B).toNat : WithBot ℕ∞) := by
  obtain ⟨s, g, hg, hfin, hdim⟩ := exists_finite_normalization_with_dimension k B
  rw [hdim, normalization_trdeg_toNat k B s g hg hfin.to_isIntegral]

end Normalization

section AlgebraicTower

variable (k B C : Type*) [Field k] [CommRing B] [IsDomain B]
  [CommRing C] [IsDomain C] [Algebra k B] [Algebra k C] [Algebra B C]
  [IsScalarTower k B C] [FaithfulSMul B C]

theorem trdeg_toNat_eq_of_algebraic_tower [Algebra.IsAlgebraic B C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have ht := congrArg Cardinal.toNat (lift_trdeg_add_eq k B C)
  simpa only [trdeg_eq_zero, Cardinal.lift_zero, add_zero, Cardinal.toNat_lift] using ht

theorem localization_trdeg_toNat_eq (M : Submonoid B) [IsLocalization M C] :
    (Algebra.trdeg k B).toNat = (Algebra.trdeg k C).toNat := by
  have : Algebra.IsAlgebraic B C := IsLocalization.isAlgebraic C M
  exact trdeg_toNat_eq_of_algebraic_tower k B C

end AlgebraicTower

end PiExponentJets.W24

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_IntegralAffineOpenDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponent.IntegralAffineOpenDimension
open CategoryTheory AlgebraicGeometry TopologicalSpace
universe u
variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (.of k))

theorem germToFunctionField_fromSpec (U : X.affineOpens) [Nonempty U.1] :
    Spec.map (X.germToFunctionField U.1) ≫ U.2.fromSpec =
      X.fromSpecStalk (genericPoint X) :=
  U.2.fromSpecStalk_eq_fromSpecStalk _

theorem chart_functionField_scalarTower (U : X.affineOpens) [Nonempty U.1] :
    letI := chartAlgebra p U
    letI := functionFieldAlgebra p
    IsScalarTower k Γ(X, U.1) X.functionField := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  have h : Spec.preimage (U.2.fromSpec ≫ p) ≫ X.germToFunctionField U.1 =
      Spec.preimage (X.fromSpecStalk (genericPoint X) ≫ p) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, ← Category.assoc,
      germToFunctionField_fromSpec, Spec.map_preimage]
  exact IsScalarTower.of_algebraMap_eq' (CommRingCat.hom_ext_iff.mp h).symm

omit [IsIntegral X] in
theorem chart_finiteType [LocallyOfFiniteType p] (U : X.affineOpens) :
    letI := chartAlgebra p U
    Algebra.FiniteType k Γ(X, U.1) := by
  let := chartAlgebra p U
  have h : LocallyOfFiniteType (Spec.map (Spec.preimage (U.2.fromSpec ≫ p))) := by
    rw [Spec.map_preimage]
    let hOpen : IsOpenImmersion U.2.fromSpec := U.2.isOpenImmersion_fromSpec
    let : LocallyOfFiniteType U.2.fromSpec :=
      @locallyOfFiniteType_of_isOpenImmersion _ _ U.2.fromSpec hOpen
    exact locallyOfFiniteType_comp U.2.fromSpec p
  have h' : RingHom.FiniteType (chartConstants p U) := HasRingHomProperty.Spec_iff.mp h
  exact RingHom.finiteType_algebraMap.mp h'

theorem chart_ring_dimension [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    letI := functionFieldAlgebra p
    ringKrullDim Γ(X, U.1) = ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) := by
  let := chartAlgebra p U
  let := functionFieldAlgebra p
  let := chart_functionField_scalarTower p U
  let := chart_finiteType p U
  let := functionField_isFractionRing_of_isAffineOpen X U.1 U.2
  let : FaithfulSMul Γ(X, U.1) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  rw [PiExponentJets.W24.finiteType_domain_krullDim_eq_trdeg k Γ(X, U.1),
    PiExponentJets.W24.localization_trdeg_toNat_eq k Γ(X, U.1) X.functionField
      (nonZeroDivisors Γ(X, U.1))]

omit [IsIntegral X] in
theorem affine_dimension_eq_ring (U : X.affineOpens) :
    topologicalKrullDim U.1 = ringKrullDim Γ(X, U.1) := by
  have h := U.2.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq
  change topologicalKrullDim U.1 = topologicalKrullDim (PrimeSpectrum Γ(X, U.1)) at h
  exact h.trans (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)

theorem affine_open_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    topologicalKrullDim U.1 = topologicalKrullDim X := by
  let := functionFieldAlgebra p
  have hU : topologicalKrullDim U.1 =
      ((Algebra.trdeg k X.functionField).toNat : WithBot ℕ∞) :=
    (affine_dimension_eq_ring U).trans (chart_ring_dimension p U)
  apply le_antisymm (topologicalKrullDim_subspace_le X U.1)
  change topologicalKrullDim X ≤ topologicalKrullDim U.1
  rw [hU]
  apply PiExponent.NumericalAmpleness.dimension_le_of_local_bound
  intro x
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
  let : Nonempty V := ⟨⟨x, hxV⟩⟩
  exact ⟨V, hxV, ((affine_dimension_eq_ring ⟨V, hV⟩).trans
    (chart_ring_dimension p ⟨V, hV⟩)).le⟩

theorem affine_ring_dimension_eq [LocallyOfFiniteType p] (U : X.affineOpens) [Nonempty U.1] :
    ringKrullDim Γ(X, U.1) = topologicalKrullDim X :=
  (affine_dimension_eq_ring U).symm.trans (affine_open_dimension_eq p U)

end PiExponent.IntegralAffineOpenDimension

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Polynomials_PolynomialMaximalHeight
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PiExponentSiegelAux.W09

variable (K : Type*) [Field K]

theorem polynomialMaximal_height (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) K)) [m.IsMaximal] :
    m.height = (n : ℕ∞) := by
  induction n with
  | zero =>
      let e := MvPolynomial.isEmptyAlgEquiv K (Fin 0)
      let p : Ideal K := m.comap e.symm.toRingHom
      let : p.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      have hp : p = ⊥ := p.eq_bot_or_top.resolve_right (Ideal.IsMaximal.ne_top (inferInstance : p.IsMaximal))
      calc
        m.height = p.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = (0 : ℕ∞) := by rw [hp, Ideal.height_bot]
  | succ n ih =>
      let e := MvPolynomial.finSuccEquiv K n
      let P : Ideal (Polynomial (MvPolynomial (Fin n) K)) :=
        m.comap e.symm.toRingHom
      let : P.IsMaximal := Ideal.comap_isMaximal_of_equiv e.symm
      let p : Ideal (MvPolynomial (Fin n) K) := P.comap Polynomial.C
      let : p.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing P
      let : P.LiesOver p := ⟨rfl⟩
      calc
        m.height = P.height := (e.symm.toRingEquiv.height_comap m).symm
        _ = p.height + 1 := Polynomial.height_eq_height_add_one p P
        _ = ((n + 1 : ℕ) : ℕ∞) := by rw [ih p]; simp

end PiExponentSiegelAux.W09

end

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_ClosedPointLocalDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponentJets.W29

section GoingDownHeight

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Algebra.HasGoingDown A B]

theorem under_height_le_of_goingDown (P : Ideal B) [P.IsPrime] :
    (P.under A).height ≤ P.height := by
  rw [PrimeSpectrum.height_eq_orderHeight (⟨P.under A, inferInstance⟩ : PrimeSpectrum A),
    PrimeSpectrum.height_eq_orderHeight (⟨P, inferInstance⟩ : PrimeSpectrum B)]
  apply Order.height_le
  intro l hl
  let : P.LiesOver l.last.asIdeal := ⟨congrArg PrimeSpectrum.asIdeal hl⟩
  obtain ⟨L, hlen, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have h : (L.length : ℕ∞) ≤ Order.height (⟨P, inferInstance⟩ : PrimeSpectrum B) :=
    Order.length_le_height (le_of_eq hlast)
  simpa only [hlen] using h

end GoingDownHeight

variable (k B : Type*) [Field k] [CommRing B] [IsDomain B]
  [Algebra k B] [Algebra.FiniteType k B]

include k

theorem affineDomain_maximal_height (m : Ideal B) [m.IsMaximal] :
    (m.height : WithBot ℕ∞) = ringKrullDim B := by
  obtain ⟨d, g, hg, hfin, hdim⟩ := W24.exists_finite_normalization_with_dimension k B
  let A := MvPolynomial (Fin d) k
  let : Algebra A B := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral A B := ⟨hfin.to_isIntegral⟩
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr hg
  have : IsIntegrallyClosed A := inferInstance
  have : Algebra.HasGoingDown A B := inferInstance
  let p : Ideal A := m.under A
  have : p.IsMaximal := by
    dsimp [p]
    infer_instance
  have hp : p.height = (d : ℕ∞) :=
    PiExponentSiegelAux.W09.polynomialMaximal_height k d p
  have hlo : (d : ℕ∞) ≤ m.height := by
    rw [← hp]
    exact under_height_le_of_goingDown m
  apply le_antisymm
  · exact Ideal.height_le_ringKrullDim_of_ne_top
      (Ideal.IsMaximal.ne_top (inferInstance : m.IsMaximal))
  · rw [hdim]
    exact WithBot.coe_le_coe.mpr hlo

end PiExponentJets.W29

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_LocalAlgebra_PrincipalQuotientDimension
attribute [-instance] _root_.OAI.PiExponent.ClosedImmersionSerreTransfer.pushforward_flasque _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.FiniteGlobalPresentation.presentation_map_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponent.instFiniteTypeSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNatOfFinite_solutions _root_.OAI.PiExponent.instIsScalarTowerSubtypeMvPolynomialMemSubmoduleHomogeneousSubmoduleOfNatNat_solutions _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesEpis _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesFiniteColimits _root_.OAI.PiExponentSeshadri.ClosedPushforward.preservesHomology _root_.OAI.PiExponentSeshadri.ClosedPushforward.pushforward_isFinitePresentation _root_.OAI.PiExponentSeshadri.FlasqueCohomology.moduleSheafHasExt _root_.OAI.PiExponentSeshadri.Geometry.opensMap_final _root_.OAI.PiExponentSeshadri.Geometry.schemeHasExt _root_.OAI.PiExponentSeshadri.Geometry.sheafHomModule _root_.OAI.PiExponentSeshadri.Geometry.sheafLinear _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ModuleFlasque.injective_isFlasque _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.presheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafAB5 _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafGrothendieck _root_.OAI.PiExponentSeshadri.ModuleGrothendieck.sheafHasSeparator _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimit _root_.OAI.PiExponentSeshadri.ModuleSheafExact.toSheafPreservesColimits _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_additive _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_flasque _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_mono _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesFiniteLimits _root_.OAI.PiExponentSeshadri.RestrictionExact.restriction_preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeExact.map_mono _root_.OAI.PiExponentSeshadri.TildeExact.preservesFiniteLimits _root_.OAI.PiExponentSeshadri.TildeExact.preservesHomology _root_.OAI.PiExponentSeshadri.TildeExact.preservesMonomorphisms _root_.OAI.PiExponentSeshadri.TildeFlasque.tilde_injective_isFlasque _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.GeometrySupport.PrincipalQuotientDimension

variable (k R : Type*) [Field k] [CommRing R] [IsDomain R]
  [Algebra k R] [Algebra.FiniteType k R]

include k

theorem le_quotient_succ (a : R) (hu : ¬ IsUnit a) :
    ringKrullDim R ≤ ringKrullDim (R ⧸ Ideal.span {a}) + 1 := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  obtain ⟨m, hm, ham⟩ := Ideal.exists_le_maximal (Ideal.span {a})
    (Ideal.span_singleton_ne_top hu)
  let : m.IsMaximal := hm
  rw [← PiExponentJets.W29.affineDomain_maximal_height k R m]
  exact Ideal.height_le_ringKrullDim_quotient_add_one
    (ham (Ideal.subset_span (by simp)))

end PiExponent.GeometrySupport.PrincipalQuotientDimension

end OAI
end

section
-- module Solutions.OAIQ068_PI.PiExponent_Ampleness_AmpleDivisorDimension
attribute [-instance] _root_.OAI.PiExponent.CurveCycle.finite_componentZero _root_.OAI.PiExponent.CurveCycle.finite_componentsThrough _root_.OAI.PiExponent.CurveFinitePushforwardCoherent.pushforward_isFinitePresentation _root_.OAI.PiExponent.PresentedIdealIso.toIdealModule_isIso _root_.OAI.PiExponent.ProjectivePencil.sectionsMorphism_isFinite _root_.OAI.PiExponent.fromSpecStalk_stalkMap_isIso _root_.OAI.PiExponentJets.PolynomialLocalResidueResolution.primeResidueImage_isPrime _root_.OAI.PiExponentJets.W64.homogeneousSection_finite _root_.OAI.PiExponentSeshadri.Geometry.LineBundle.quasicoherent _root_.OAI.PiExponentSeshadri.LaurentLattices.instIsPrincipalIdealRingLaurentPolynomial_solutions _root_.OAI.PiExponentSeshadri.LaurentLattices.laurent_finiteType _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.homogeneous_isReduced _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_irreducible _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isIntegral _root_.OAI.PiExponentSeshadri.ProjectiveGeometry.proj_isReduced _root_.OAI.PiExponentSeshadri.ReesGrading.exceptionalInclusion_mono _root_.OAI.PiExponentSeshadri.ReesGrading.polynomial_isReduced _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_flat _root_.OAI.PiExponentSiegel.W17.ConeLocalLength.laurent_polynomial_tower _root_.OAI.PiExponentSiegel.W58.cotangentQuotientScalarTower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open PiExponentSeshadri.Geometry PiExponentSeshadri.Frames PiExponentSeshadri.SectionOpens
open PiExponent.SectionZeroIdeal

variable {X Y : Scheme.{0}}

theorem sectionZero_pullback_dimension_le (H : LineBundle X)
    (s : GlobalSections X H.sheaf) (i : Y ⟶ X) [IsClosedImmersion i] :
    topologicalKrullDim (zeroIdeal (H.pullback i) (pullbackSection i s)).subscheme ≤
      topologicalKrullDim (zeroIdeal H s).subscheme := by
  let I := zeroIdeal H s
  let J := zeroIdeal (H.pullback i) (pullbackSection i s)
  have hmap (z : J.subscheme) : i (J.subschemeι z) ∈ (I.support : Set X) := by
    have hz := z.property
    change J.subschemeι z ∈ (J.support : Set Y) at hz
    erw [zeroIdeal_support] at hz ⊢
    change J.subschemeι z ∉ isoOpen (pullbackSection i s) at hz
    rw [pullback_isoOpen_eq H s i] at hz
    exact hz
  have he := (i.isEmbedding.comp J.subschemeι.isEmbedding).codRestrict
    (I.support : Set X) hmap
  exact he.isInducing.topologicalKrullDim_le

theorem sectionZero_dimension_succ_ge_of_zero [IsIntegral X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p]
    (H : LineBundle X) (s : GlobalSections X H.sheaf)
    (y : X) (hy : y ∉ sectionOpen X s) :
    topologicalKrullDim X ≤ topologicalKrullDim (zeroIdeal H s).subscheme + 1 := by
  obtain ⟨V, hyV, ⟨eV⟩⟩ := H.locallyRankOne y
  obtain ⟨W, hW, hyW, hWV⟩ := exists_isAffineOpen_mem_and_subset hyV
  let U : X.affineOpens := ⟨W, hW⟩
  let e := restrictOpenFrame hWV eV
  let : Nonempty U.1 := ⟨⟨y, hyW⟩⟩
  let a : Γ(X,U) := U.1.topIso.hom (coefficient e (restrictSection U.1.ι s))
  have ha : ¬ IsUnit a := by
    intro ha
    have hc : IsUnit (coefficient e (restrictSection U.1.ι s)) := by
      have hh := ha.map U.1.topIso.inv.hom
      simpa only [a, ← CommRingCat.comp_apply, Iso.hom_inv_id,
        CommRingCat.id_apply] using hh
    have hopen := preimage_isoOpen s U.1.ι e
    rw [U.1.toScheme.basicOpen_of_isUnit hc] at hopen
    have hm : (⟨y,hyW⟩ : U.1.toScheme) ∈ U.1.ι ⁻¹ᵁ isoOpen s :=
      hopen.ge trivial
    exact hy hm
  let := IntegralAffineOpenDimension.chartAlgebra p U
  let := IntegralAffineOpenDimension.chart_finiteType p U
  have hdrop := GeometrySupport.PrincipalQuotientDimension.le_quotient_succ
    ℂ Γ(X,U) a ha
  rw [← zeroIdeal_on_frame H s U e] at hdrop
  rw [IntegralAffineOpenDimension.affine_ring_dimension_eq p U] at hdrop
  let I := zeroIdeal H s
  have hquot : ringKrullDim (Γ(X,U) ⧸ I.ideal U) ≤
      topologicalKrullDim I.subscheme := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    let : IsOpenImmersion (I.subschemeCover.f U) := I.subschemeCover.map_prop U
    exact (I.subschemeCover.f U).isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  exact hdrop.trans (add_le_add hquot le_rfl)

theorem regular_ample_sectionZero_dimension_q68_oai
    [IsNoetherian X] [Nonempty X]
    (p : X ⟶ Spec (CommRingCat.of ℂ)) [IsProper p]
    (H : LineBundle X) (hH : H.IsAmple)
    (s : GlobalSections X H.sheaf) [Mono s] (d : ℕ)
    (hdim : topologicalKrullDim X = ((d+1 : ℕ) : WithBot ℕ∞)) :
    Nonempty (zeroIdeal H s).subscheme ∧
      topologicalKrullDim (zeroIdeal H s).subscheme = d := by
  refine ⟨ample_section_zero_nonempty p H hH s (d+1) hdim (Nat.succ_pos d), ?_⟩
  apply le_antisymm
  · apply regular_sectionZero_dimension_le H s d
    simpa only [Nat.cast_add, Nat.cast_one] using hdim.le
  · obtain ⟨Y, i, hi, hY, hdimY⟩ := exists_integral_closed_full_dimension X (d+1) hdim
    let := hi
    let := hY
    have hample := LineBundle.IsAmple.pullback_closedImmersion H hH i
    obtain ⟨y, hy⟩ := ample_section_has_zero (i ≫ p) (H.pullback i) hample
      (pullbackSection i s) (d+1) hdimY (Nat.succ_pos d)
    have hlow := sectionZero_dimension_succ_ge_of_zero (i ≫ p)
      (H.pullback i) (pullbackSection i s) y hy
    rw [hdimY] at hlow
    have hbound := hlow.trans (add_le_add (sectionZero_pullback_dimension_le H s i) le_rfl)
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    simpa only [Nat.cast_add, Nat.cast_one] using hbound

end
end PiExponent.NumericalAmpleness

end OAI
end

theorem solution : type_of% @OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68_oai := @OAI.PiExponent.NumericalAmpleness.regular_ample_sectionZero_dimension_q68_oai
