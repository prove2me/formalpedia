-- Prove2me | solution 1 for GlobalTheory.ZM.FullLevel.dim_generic_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:39:20.959527+00:00
-- url     : https://prove2.me/submissions/eb398dfd-6c92-46e7-94c5-77e96d3badc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_MinimalAndDimLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
namespace GlobalTheory.ZM.FullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
private theorem krullDim_zeroLocus_le_of_isEmbedding {S T : Type} [CommRing S] [CommRing T]
    (f : PrimeSpectrum S → PrimeSpectrum T) (hf : Topology.IsEmbedding f) (p : PrimeSpectrum S) :
    Order.krullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set S)) ≤
      Order.krullDim (PrimeSpectrum.zeroLocus ((f p).asIdeal : Set T)) := by
  have hle : ∀ a b, f a ≤ f b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hf.isInducing.specializes_iff]
  refine Order.krullDim_le_of_strictMono (fun a => ⟨f a.1, ?_⟩) ?_
  · have ha : p ≤ a.1 := by
      have := a.2
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at this
      exact this
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact (hle p a.1).2 ha
  · refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · exact (hle a.1 b.1).2 hab
    · exact Subtype.ext (hf.injective (congrArg Subtype.val hab))
end GlobalTheory.ZM.FullLevel
end

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.FullLevel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct
namespace GlobalTheory.ZM.FullLevel
namespace _root_.GlobalTheory.ZM.FullLevel
theorem _root_.solution {o K : Type} [CommRing o] [IsDomain o] [Field K]
    [Algebra o K] [IsFractionRing o K]
    {U : Scheme.{0}} (s : U ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp o) (d : WithBot ℕ∞)
    (h : ∀ (R : Type) [CommRing R] [Algebra o R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ U), IsOpenImmersion x →
      x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o R) →
      ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), d ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (R : Type) [CommRing R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)))
    [IsOpenImmersion x]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : d ≤ ringKrullDim (R ⧸ q) := by
  classical
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors o)
  let pr := pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K))
  have hpr : Topology.IsEmbedding pr := IsPreimmersion.isEmbedding pr
  let y₀ : PrimeSpectrum R := ⟨q, hq.1.1⟩
  obtain ⟨O, hO, hOx⟩ := hpr.isInducing.isOpen_iff.1 x.isOpenEmbedding.isOpen_range
  have hyO : pr (x y₀) ∈ O := by
    have : x y₀ ∈ pr ⁻¹' O := hOx ▸ ⟨y₀, rfl⟩
    exact this
  obtain ⟨V, hV, hyV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 U.isBasis_affineOpens
    (show pr (x y₀) ∈ (⟨O, hO⟩ : TopologicalSpace.Opens U) from hyO)
  have hVa : IsAffineOpen V := hV
  let A : Type := Γ(U, V)
  let j : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ U := hVa.fromSpec
  haveI : IsOpenImmersion j := hVa.isOpenImmersion_fromSpec
  letI : Algebra o A := (Spec.preimage (j ≫ s)).hom.toAlgebra
  have hjs : j ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o A) := by
    rw [RingHom.algebraMap_toAlgebra]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  have hbound := h A j inferInstance hjs
  let e : A ⊗[o] K ≃ₐ[o] FractionRing o ⊗[o] A :=
    (Algebra.TensorProduct.comm o A K).trans
      (Algebra.TensorProduct.congr (IsLocalization.algEquiv (nonZeroDivisors o) K (FractionRing o))
        AlgEquiv.refl)
  let I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing o ⊗[o] A) ≅ pullback j pr :=
    asIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom) ≪≫ (pullbackSpecIso o A K).symm ≪≫
      (pullback.congrHom hjs rfl).symm ≪≫ (pullbackRightPullbackFstIso s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) j).symm
  let F := I.hom ≫ pullback.snd j pr
  have hF : ∀ w, F w = pullback.snd j pr (I.hom w) := fun w => rfl
  have hrange : Set.range F ⊆ Set.range x := by
    rintro _ ⟨w, rfl⟩
    rw [← hOx]
    have hmem : pullback.snd j pr (I.hom w) ∈ Set.range (pullback.snd j pr) := ⟨_, rfl⟩
    rw [IsOpenImmersion.range_pullbackSnd] at hmem
    have hmem' : pr (pullback.snd j pr (I.hom w)) ∈ j.opensRange := hmem
    rw [hVa.opensRange_fromSpec] at hmem'
    show pr (F w) ∈ O
    rw [hF]
    exact hVO hmem'
  have hy : x y₀ ∈ Set.range F := by
    have : x y₀ ∈ Set.range (pullback.snd j pr) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      show pr (x y₀) ∈ j.opensRange
      rw [hVa.opensRange_fromSpec]
      exact hyV
    obtain ⟨p, hp⟩ := this
    refine ⟨I.inv p, ?_⟩
    show (I.inv ≫ I.hom ≫ pullback.snd j pr) p = _
    rw [Iso.inv_hom_id_assoc, hp]
  obtain ⟨z, hz⟩ := hy
  let g := IsOpenImmersion.lift x F hrange
  have hg : g ≫ x = F := IsOpenImmersion.lift_fac x F hrange
  haveI : IsOpenImmersion g := by
    haveI : IsOpenImmersion (g ≫ x) := hg ▸ inferInstance
    exact IsOpenImmersion.of_comp g x
  let gf : PrimeSpectrum (FractionRing o ⊗[o] A) → PrimeSpectrum R := fun a => g a
  have hgemb : Topology.IsEmbedding gf := g.isOpenEmbedding.isEmbedding
  have hgz : gf z = y₀ := x.isOpenEmbedding.injective (by
    show x (g z) = x y₀
    rw [← Scheme.Hom.comp_apply, hg, hz])
  have hle : ∀ a b, gf a ≤ gf b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hgemb.isInducing.specializes_iff]
  have hzmin : z.asIdeal ∈ minimalPrimes (FractionRing o ⊗[o] A) := by
    refine ⟨⟨z.isPrime, bot_le⟩, fun p' hp' hp'le => ?_⟩
    let w : PrimeSpectrum (FractionRing o ⊗[o] A) := ⟨p', hp'.1⟩
    have hwz : w ≤ z := hp'le
    have h1 : gf w ≤ y₀ := hgz ▸ (hle w z).2 hwz
    have h2 : y₀ ≤ gf w := hq.2 ⟨(gf w).isPrime, bot_le⟩ h1
    exact (hle z w).1 (hgz ▸ h2)
  have hq' : (gf z).asIdeal = q := congrArg PrimeSpectrum.asIdeal hgz
  calc d ≤ ringKrullDim ((FractionRing o ⊗[o] A) ⧸ z.asIdeal) := hbound _ hzmin
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (z.asIdeal : Set (FractionRing o ⊗[o] A))) :=
      ringKrullDim_quotient _
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus ((gf z).asIdeal : Set R)) :=
      krullDim_zeroLocus_le_of_isEmbedding gf hgemb z
    _ = ringKrullDim (R ⧸ q) := by rw [hq', ringKrullDim_quotient]
end _root_.GlobalTheory.ZM.FullLevel
end GlobalTheory.ZM.FullLevel
