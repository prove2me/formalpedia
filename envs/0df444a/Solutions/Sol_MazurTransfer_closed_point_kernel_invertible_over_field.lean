-- Prove2me | solution 1 for MazurTransfer.closed_point_kernel_invertible_over_field
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-09T21:37:48.480324+00:00
-- url     : https://prove2.me/submissions/397cb183-fc33-4d72-a1e2-b105e40dbda2

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Official Anthropic FLT proof infrastructure at
6e837e75355538c7f80bab5b956861e86c4eacc2, with separately checked
arbitrary-residue-field adaptations; originals unchanged.
Design boundary: nonrational closed-point ideals and their actual valuation
orders. Named downstream consumer: divisor-class realization and surjectivity
in the literal order-13 arithmetic Picard group correspondence.
-/
import Mathlib
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_isDiscreteValuationRing_stalk_of_isClosed

universe u
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Adapted from the complete official Anthropic FLT vanishing-ideal proof at
6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0. The original source
is unchanged. Its regular-local height-one principal-ideal step is replaced
by the DVR principal-ideal instance, supplied by smooth-curve stalk geometry.
Design boundary: closed points over the actual base field give invertible
ideal sheaves without requiring those points to be rational. Named downstream
consumer: realization of arbitrary function-field divisor classes as actual
line bundles for the order-13 Picard/divisor-class bijection over F₃ and F₅.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace MazurTransfer.PublicClosedPointKernelProof
namespace CompInv
open _root_.AlgebraicGeometry

theorem exists_notMem_and_map_eq_span_singleton {A : Type u} [CommRing A] [IsNoetherianRing A]
    (𝔭 : Ideal A) [𝔭.IsPrime] (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S 𝔭]
    (𝔮 : Ideal A) (γ : S) (hγ : 𝔮.map (algebraMap A S) = Ideal.span {γ}) (hγ0 : γ ∈ nonZeroDivisors S) :
    ∃ f : A, f ∉ 𝔭 ∧ ∃ g : A, g ∈ 𝔮 ∧ ∀ (B : Type u) [CommRing B] [Algebra A B] [IsLocalization.Away f B],
      𝔮.map (algebraMap A B) = Ideal.span {algebraMap A B g} ∧ algebraMap A B g ∈ nonZeroDivisors B := by
  classical

  have hγmem : γ ∈ 𝔮.map (algebraMap A S) := hγ ▸ Ideal.mem_span_singleton_self γ
  obtain ⟨⟨⟨g, hg𝔮⟩, ⟨s, hs⟩⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔭.primeCompl S).mp hγmem
  simp only at hgs

  have hsu : IsUnit (algebraMap A S s) := IsLocalization.map_units S ⟨s, hs⟩
  have hspan : Ideal.span {algebraMap A S g} = Ideal.span {γ} := by
    rw [← hgs]
    exact Ideal.span_singleton_mul_right_unit hsu γ
  have hg0 : algebraMap A S g ∈ nonZeroDivisors S := by
    rw [← hgs]; exact mul_mem hγ0 hsu.mem_nonZeroDivisors
  have h𝔮S : 𝔮.map (algebraMap A S) = Ideal.span {algebraMap A S g} := hγ.trans hspan.symm

  have hdiv : ∀ h ∈ 𝔮, ∃ u ∈ 𝔭.primeCompl, ∃ a : A, u * h = a * g := by
    intro h hh
    have h1 : algebraMap A S h ∈ Ideal.span {algebraMap A S g} := h𝔮S ▸ Ideal.mem_map_of_mem _ hh
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h1
    obtain ⟨⟨a, ⟨t, ht⟩⟩, hat⟩ := IsLocalization.surj 𝔭.primeCompl c
    simp only at hat

    have h2 : algebraMap A S (h * t) = algebraMap A S (a * g) := by
      rw [map_mul, map_mul, ← hc, ← hat]; ring
    obtain ⟨⟨v, hv⟩, hv'⟩ := (IsLocalization.eq_iff_exists 𝔭.primeCompl S).mp h2
    simp only at hv'
    exact ⟨v * t, mul_mem hv ht, v * a, by
      calc v * t * h = v * (h * t) := by ring
        _ = v * (a * g) := hv'
        _ = v * a * g := by ring⟩

  obtain ⟨T, hT⟩ := (isNoetherianRing_iff_ideal_fg A).mp inferInstance 𝔮
  choose! u hu a ha using hdiv
  let N : Ideal A := LinearMap.ker (LinearMap.mulRight A g)
  have hN : ∀ n : A, n ∈ N ↔ n * g = 0 := fun n => LinearMap.mem_ker
  obtain ⟨T', hT'⟩ := (isNoetherianRing_iff_ideal_fg A).mp inferInstance N
  have hann : ∀ n ∈ N, ∃ v ∈ 𝔭.primeCompl, v * n = 0 := by
    intro n hn
    have h1 : algebraMap A S n * algebraMap A S g = 0 := by rw [← map_mul, (hN n).mp hn, map_zero]
    have h2 : algebraMap A S n = 0 := (mem_nonZeroDivisors_iff_right.mp hg0) _ h1
    obtain ⟨⟨v, hv⟩, hvn⟩ := (IsLocalization.map_eq_zero_iff 𝔭.primeCompl S n).mp h2
    exact ⟨v, hv, hvn⟩
  choose! v hv hvn using hann

  let f₁ : A := ∏ h ∈ T, u h
  let f₂ : A := ∏ n ∈ T', v n
  have hTsub : ∀ h ∈ T, h ∈ 𝔮 := fun h hh => hT ▸ Ideal.subset_span hh
  have hT'sub : ∀ n ∈ T', n ∈ N := fun n hn => hT' ▸ Ideal.subset_span hn
  have hf₁ : f₁ ∈ 𝔭.primeCompl := prod_mem fun h hh => hu h (hTsub h hh)
  have hf₂ : f₂ ∈ 𝔭.primeCompl := prod_mem fun n hn => hv n (hT'sub n hn)
  refine ⟨f₁ * f₂, mul_mem hf₁ hf₂, g, hg𝔮, fun B _ _ _ => ?_⟩
  have hfu : IsUnit (algebraMap A B (f₁ * f₂)) := IsLocalization.Away.algebraMap_isUnit (f₁ * f₂)
  have hu_unit : ∀ h ∈ T, IsUnit (algebraMap A B (u h)) := by
    intro h hh
    have : u h ∣ f₁ * f₂ := (Finset.dvd_prod_of_mem u hh).mul_right f₂
    obtain ⟨c, hc⟩ := this
    rw [hc, map_mul] at hfu
    exact isUnit_of_mul_isUnit_left hfu
  have hf₂u : IsUnit (algebraMap A B f₂) := by
    rw [map_mul] at hfu; exact isUnit_of_mul_isUnit_right hfu
  constructor
  ·
    apply le_antisymm
    · rw [← hT, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨h, hh, rfl⟩
      obtain ⟨w, hw⟩ := hu_unit h hh
      refine Ideal.mem_span_singleton'.mpr ⟨↑w⁻¹ * algebraMap A B (a h), ?_⟩
      have key : algebraMap A B (u h) * algebraMap A B h = algebraMap A B (a h) * algebraMap A B g := by
        rw [← map_mul, ← map_mul, ha h (hTsub h hh)]
      rw [← hw] at key
      calc ↑w⁻¹ * algebraMap A B (a h) * algebraMap A B g
          = ↑w⁻¹ * (↑w * algebraMap A B h) := by rw [key, mul_assoc]
        _ = algebraMap A B h := by rw [← mul_assoc, Units.inv_mul, one_mul]
    · rw [Ideal.span_singleton_le_iff_mem]; exact Ideal.mem_map_of_mem _ hg𝔮
  ·
    refine mem_nonZeroDivisors_iff_right.mpr fun z hz => ?_
    obtain ⟨⟨c, ⟨m, hm⟩⟩, hcm⟩ := IsLocalization.surj (Submonoid.powers (f₁ * f₂)) z
    simp only at hcm

    have h1 : algebraMap A B (c * g) = 0 := by
      rw [map_mul, ← hcm, mul_right_comm, hz, zero_mul]
    obtain ⟨⟨m', hm'⟩, hm'c⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers (f₁ * f₂)) B _).mp h1
    simp only at hm'c

    have h2 : m' * c ∈ N := (hN _).mpr (by rw [mul_assoc]; exact hm'c)
    have h3 : f₂ * (m' * c) = 0 := by
      have hle : N ≤ LinearMap.ker (LinearMap.mulLeft A f₂) := by
        rw [← hT', Ideal.span_le]
        intro n hn
        change f₂ * n = 0
        obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem v hn
        change (∏ n ∈ T', v n) * n = 0
        rw [hd, mul_right_comm, hvn n (hT'sub n hn), zero_mul]
      exact hle h2
    have h4 : algebraMap A B c = 0 := by
      have := congrArg (algebraMap A B) h3
      rw [map_mul, map_mul, map_zero] at this
      have hm'u : IsUnit (algebraMap A B m') := IsLocalization.map_units B ⟨m', hm'⟩
      exact hm'u.mul_right_eq_zero.mp (hf₂u.mul_right_eq_zero.mp this)
    have h5 : z * algebraMap A B m = 0 := hcm.trans h4
    exact (IsLocalization.map_units B ⟨m, hm⟩).mul_left_eq_zero.mp h5

end CompInv

open AlgebraicGeometry.Scheme.IdealSheafData in
theorem isInvertible_vanishingIdeal_closure_of_stalkDVR
    {Y : Scheme.{u}} [IsIntegral Y] [IsLocallyNoetherian Y] (η : Y)
    (hη : ringKrullDim (Y.presheaf.stalk η) = 1)
    (hreg : ∀ y ∈ closure ({η} : Set Y),
      IsDiscreteValuationRing (Y.presheaf.stalk y)) :
    (Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨closure ({η} : Set Y), isClosed_closure⟩).IsInvertible := by
  classical
  set Z : Closeds Y := ⟨closure ({η} : Set Y), isClosed_closure⟩ with hZ
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  change IsAffineOpen U at hU
  haveI : IsNoetherianRing Γ(Y, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  by_cases hx : x ∈ closure ({η} : Set Y)
  ·
    have hηU : η ∈ U := by
      obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp hx U U.isOpen hxU
      rw [Set.mem_singleton_iff.mp hz2] at hz1
      exact hz1
    letI algx := Y.presheaf.algebra_section_stalk (⟨x, hxU⟩ : U)
    letI algη := Y.presheaf.algebra_section_stalk (⟨η, hηU⟩ : U)
    haveI hlocx := hU.isLocalization_stalk ⟨x, hxU⟩
    haveI hlocη := hU.isLocalization_stalk ⟨η, hηU⟩
    set 𝔭 : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal with h𝔭def
    set 𝔮 : Ideal Γ(Y, U) := (hU.primeIdealOf ⟨η, hηU⟩).asIdeal with h𝔮def
    have hinj : Function.Injective hU.fromSpec := hU.fromSpec.isOpenEmbedding.injective
    have hpre : (hU.fromSpec : _ → Y) ⁻¹' ({η} : Set Y) = {hU.primeIdealOf ⟨η, hηU⟩} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hz
        apply hinj
        rw [hz, IsAffineOpen.fromSpec_primeIdealOf]
      · rintro rfl
        exact hU.fromSpec_primeIdealOf ⟨η, hηU⟩
    have hcl : (hU.fromSpec : _ → Y) ⁻¹' closure ({η} : Set Y) = closure ((hU.fromSpec : _ → Y) ⁻¹' {η}) :=
      hU.fromSpec.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage hU.fromSpec.continuous _
    have hIU : (vanishingIdeal Z).ideal ⟨U, hU⟩ = 𝔮 := by
      rw [vanishingIdeal_ideal]
      change PrimeSpectrum.vanishingIdeal ((hU.fromSpec : _ → Y) ⁻¹' closure ({η} : Set Y)) = _
      have h3 : PrimeSpectrum.vanishingIdeal ((hU.fromSpec : _ → Y) ⁻¹' closure ({η} : Set Y)) =
          PrimeSpectrum.vanishingIdeal (closure {hU.primeIdealOf ⟨η, hηU⟩}) := by
        congr 1
        exact hcl.trans (congrArg closure hpre)
      refine h3.trans ?_
      rw [PrimeSpectrum.vanishingIdeal_closure, PrimeSpectrum.vanishingIdeal_singleton]

    have hηx : η ⤳ x := specializes_iff_mem_closure.mpr hx
    have h𝔮𝔭 : 𝔮 ≤ 𝔭 := by
      change hU.primeIdealOf ⟨η, hηU⟩ ≤ hU.primeIdealOf ⟨x, hxU⟩
      rw [PrimeSpectrum.le_iff_specializes]
      have h2 : hU.fromSpec (hU.primeIdealOf ⟨η, hηU⟩) ⤳ hU.fromSpec (hU.primeIdealOf ⟨x, hxU⟩) := by
        rwa [IsAffineOpen.fromSpec_primeIdealOf, IsAffineOpen.fromSpec_primeIdealOf]
      exact (hU.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp h2

    have hq1 : 𝔮.height = 1 := by
      have h1 := IsLocalization.AtPrime.ringKrullDim_eq_height 𝔮 (Y.presheaf.stalk η)
      rw [hη] at h1
      exact_mod_cast h1.symm
    have hdisj : Disjoint (𝔭.primeCompl : Set Γ(Y, U)) (𝔮 : Set Γ(Y, U)) := by
      rw [Set.disjoint_left]
      intro r hr hrq
      exact hr (h𝔮𝔭 hrq)
    set P : Ideal (Y.presheaf.stalk x) := 𝔮.map (algebraMap Γ(Y, U) (Y.presheaf.stalk x)) with hPdef
    haveI hP : P.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint 𝔭.primeCompl _ 𝔮 inferInstance hdisj
    have hP1 : P.height = 1 := (IsLocalization.height_map_of_disjoint 𝔭.primeCompl 𝔮 hdisj).trans hq1
    haveI : IsDiscreteValuationRing (Y.presheaf.stalk x) := hreg x hx
    have hprin : Submodule.IsPrincipal P := inferInstance
    obtain ⟨γ, hγ⟩ : ∃ γ : Y.presheaf.stalk x, P = Ideal.span {γ} :=
      ⟨hprin.generator, (Submodule.IsPrincipal.span_singleton_generator P).symm⟩
    have hγ0 : γ ∈ nonZeroDivisors (Y.presheaf.stalk x) := by
      apply mem_nonZeroDivisors_of_ne_zero
      rintro rfl
      rw [hγ, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.height_bot] at hP1
      exact zero_ne_one hP1

    obtain ⟨f, hf𝔭, g, hg𝔮, hspread⟩ :=
      CompInv.exists_notMem_and_map_eq_span_singleton 𝔭 (Y.presheaf.stalk x) 𝔮 γ (hPdef ▸ hγ) hγ0
    have hxf : x ∈ Y.basicOpen f := by
      rw [Y.mem_basicOpen f x hxU]
      exact (IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk x) 𝔭 f).mpr hf𝔭
    haveI := hU.isLocalization_basicOpen f
    obtain ⟨hmap, hnzd⟩ := hspread Γ(Y, Y.basicOpen f)
    refine ⟨⟨U, hU⟩, f, hxf, (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) g : _), hnzd, ?_⟩
    rw [← (vanishingIdeal Z).map_ideal_basicOpen ⟨U, hU⟩ f, hIU]
    exact hmap
  ·
    have hxs : x ∉ (vanishingIdeal Z).support := by
      rw [← SetLike.mem_coe, coe_support_vanishingIdeal]; exact hx
    rw [mem_support_iff_of_mem (I := vanishingIdeal Z) (U := ⟨U, hU⟩) hxU, Scheme.mem_zeroLocus_iff] at hxs
    push Not at hxs
    obtain ⟨f, hf, hxf⟩ := hxs
    refine ⟨⟨U, hU⟩, f, hxf, 1, one_mem _, ?_⟩
    haveI := hU.isLocalization_basicOpen f
    have hunit : IsUnit (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) f) := IsLocalization.Away.algebraMap_isUnit f
    have hmem : algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) f ∈ (vanishingIdeal Z).ideal (Y.affineBasicOpen f) := by
      rw [← (vanishingIdeal Z).map_ideal_basicOpen ⟨U, hU⟩ f]
      exact Ideal.mem_map_of_mem _ hf
    rw [Ideal.span_singleton_one]
    exact Ideal.eq_top_of_isUnit_mem _ hmem hunit


/-- The vanishing ideal of an arbitrary closed point on a smooth integral curve
is invertible, including closed points with nontrivial residue extensions. -/
theorem isInvertible_closedPointIdeal
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 x]
    (y : X) (hy : IsClosed ({y} : Set X)) :
    (Scheme.IdealSheafData.vanishingIdeal (X := X)
      ⟨closure ({y} : Set X), isClosed_closure⟩).IsInvertible := by
  haveI := SmoothOfRelativeDimension.isDiscreteValuationRing_stalk_of_isClosed x y hy
  apply isInvertible_vanishingIdeal_closure_of_stalkDVR y
    (IsDiscreteValuationRing.ringKrullDim_eq_one (X.presheaf.stalk y))
  intro z hz
  have hz' : z = y := by simpa only [hy.closure_eq, Set.mem_singleton_iff] using hz
  subst z
  infer_instance

#print axioms isInvertible_vanishingIdeal_closure_of_stalkDVR
#print axioms isInvertible_closedPointIdeal
end MazurTransfer.PublicClosedPointKernelProof

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
The full kernel/vanishing-ideal equality proof is reused from official Anthropic
FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Design boundary: arbitrary residue-field points of a smooth integral curve
have invertible kernel ideals. Named downstream consumer: divisor realization
and surjectivity for the actual order-13 arithmetic Picard-point map.
-/

open CategoryTheory AlgebraicGeometry
namespace MazurTransfer.PublicClosedPointKernelProof
theorem ker_eq_vanishingIdeal_closure_genericPoint
    {C Y : Scheme.{u}} (f : C ⟶ Y) [IsIntegral C] [QuasiCompact f] :
    f.ker = Scheme.IdealSheafData.vanishingIdeal (X := Y) ⟨closure ({f.base (genericPoint C)} : Set Y), isClosed_closure⟩ := by
  classical

  have hsupp : (f.ker.support : Set Y) = closure ({f.base (genericPoint C)} : Set Y) := by
    rw [Scheme.Hom.support_ker]
    apply le_antisymm
    · refine closure_minimal ?_ isClosed_closure
      rintro _ ⟨c, rfl⟩
      exact specializes_iff_mem_closure.mp ((genericPoint_specializes c).map f.base.hom.continuous)
    · exact closure_mono (Set.singleton_subset_iff.mpr ⟨genericPoint C, rfl⟩)
  have hZ : (⟨closure ({f.base (genericPoint C)} : Set Y), isClosed_closure⟩ : TopologicalSpace.Closeds Y) = f.ker.support :=
    TopologicalSpace.Closeds.ext hsupp.symm
  rw [hZ, Scheme.IdealSheafData.vanishingIdeal_support]

  ext U : 2
  rw [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact ((Ideal.isRadical_bot (R := Γ(C, f ⁻¹ᵁ U))).comap (f.app U).hom).radical.symm


/-- A closed immersion of a field point has an invertible kernel on a smooth
integral curve, even when its field differs from the curve's base field. -/
theorem isInvertible_closedPoint_ker
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 x]
    {L : Type u} [Field L] (P : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion P] :
    P.ker.IsInvertible := by
  rw [ker_eq_vanishingIdeal_closure_genericPoint P]
  apply isInvertible_closedPointIdeal x
  have hrange : Set.range P.base = {P.base (genericPoint (Spec (CommRingCat.of L)))} := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact congrArg P.base (Subsingleton.elim _ _)
    · rintro rfl
      exact ⟨_, rfl⟩
  exact hrange ▸ P.isClosedEmbedding.isClosed_range

#print axioms ker_eq_vanishingIdeal_closure_genericPoint
#print axioms isInvertible_closedPoint_ker
end MazurTransfer.PublicClosedPointKernelProof

theorem solution
    {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (x : X ⟶ Spec (CommRingCat.of k)) [SmoothOfRelativeDimension 1 x]
    {L : Type u} [Field L] (P : Spec (CommRingCat.of L) ⟶ X) [IsClosedImmersion P] :
    P.ker.IsInvertible := by exact MazurTransfer.PublicClosedPointKernelProof.isInvertible_closedPoint_ker x P

#print axioms solution
