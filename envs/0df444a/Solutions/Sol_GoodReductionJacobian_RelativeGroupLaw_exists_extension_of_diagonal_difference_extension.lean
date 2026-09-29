-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/1ac431f2-5e12-56d1-8413-6fddd7dd96ab

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

universe u

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian"

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "one mul_natural mul"
namespace DESC
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Setup

variable {R : Type u} [CommRing R]
  {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  (t : T ⟶ Spec (CommRingCat.of R))
  (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f)
  (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)

def Zop : (pullback t t).Opens := W ⊓ (pullback.snd t t) ⁻¹ᵁ V

theorem Zop_le_W : Zop t V W ≤ W := inf_le_left

theorem Zop_le_snd : Zop t V W ≤ (pullback.snd t t) ⁻¹ᵁ V := inf_le_right

def pZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ T := (Zop t V W).ι ≫ pullback.fst t t

theorem pZ_def : pZ t V W = (Zop t V W).ι ≫ pullback.fst t t := rfl

def aZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ (W : Scheme.{u}) :=
  (pullback t t).homOfLE (Zop_le_W t V W)

theorem aZ_ι : aZ t V W ≫ W.ι = (Zop t V W).ι := Scheme.homOfLE_ι _ _

def cZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ (V : Scheme.{u}) :=
  (pullback.snd t t).resLE V (Zop t V W) (Zop_le_snd t V W)

theorem cZ_ι : cZ t V W ≫ V.ι = (Zop t V W).ι ≫ pullback.snd t t := Scheme.Hom.resLE_comp_ι _ _

theorem aZ_fst : aZ t V W ≫ W.ι ≫ pullback.fst t t = pZ t V W := by
  rw [← Category.assoc, aZ_ι, pZ]

theorem aZ_snd : aZ t V W ≫ W.ι ≫ pullback.snd t t = cZ t V W ≫ V.ι := by
  rw [← Category.assoc, aZ_ι, cZ_ι]

abbrev tZ : ((Zop t V W : (pullback t t).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of R) :=
  aZ t V W ≫ W.ι ≫ pullback.fst t t ≫ t

theorem tZ_eq : tZ t V W = pZ t V W ≫ t := by
  rw [tZ, ← aZ_fst, Category.assoc, Category.assoc]

def dZ : SchemeHomOver (tZ t V W) f := ⟨aZ t V W ≫ d.1, by rw [Category.assoc, d.2]⟩

def vZ : SchemeHomOver (tZ t V W) f :=
  ⟨cZ t V W ≫ v.1, by
    rw [Category.assoc, v.2, ← Category.assoc, ← aZ_snd, Category.assoc, Category.assoc, ← pullback.condition]⟩

def rZ : SchemeHomOver (tZ t V W) f := G.mul (tZ t V W) (dZ t V W d) (vZ t V v W)

theorem rZ_base : (rZ G t V v W d).1 ≫ f = pZ t V W ≫ t := by
  rw [(rZ G t V v W d).2, tZ_eq]

theorem comp_rZ_eq_of_fst
    (hd : ∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)
    {S : Scheme.{u}} (s : S ⟶ ↑(Zop t V W)) (b : S ⟶ ↑V) (hb : s ≫ pZ t V W = b ≫ V.ι) :
    s ≫ (rZ G t V v W d).1 = b ≫ v.1 := by
  have hψ : s ≫ tZ t V W = (s ≫ aZ t V W) ≫ W.ι ≫ pullback.fst t t ≫ t := (Category.assoc _ _ _).symm
  have hnat := G.mul_natural (tZ t V W) ((s ≫ aZ t V W) ≫ W.ι ≫ pullback.fst t t ≫ t) s hψ
    (dZ t V W d) (vZ t V v W)
  have hb' : (s ≫ aZ t V W) ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι := by
    rw [Category.assoc, aZ_fst, hb]
  have hc' : (s ≫ aZ t V W) ≫ W.ι ≫ pullback.snd t t = (s ≫ cZ t V W) ≫ V.ι := by
    rw [Category.assoc, aZ_snd, Category.assoc]
  have key := hd S (s ≫ aZ t V W) b (s ≫ cZ t V W) hb' hc'
  have e1 : schemeHomOverComp s hψ (dZ t V W d) =
      ⟨(s ≫ aZ t V W) ≫ d.1, by rw [Category.assoc, d.2]⟩ := by
    apply Subtype.ext
    show s ≫ (aZ t V W ≫ d.1) = (s ≫ aZ t V W) ≫ d.1
    rw [Category.assoc]
  have e2 : schemeHomOverComp s hψ (vZ t V v W) =
      ⟨(s ≫ cZ t V W) ≫ v.1, by have h__af := (congrArg (fun k => s ≫ k) (vZ t V v W).2); simp only [Category.assoc] at h__af ⊢; exact h__af⟩ := by
    apply Subtype.ext
    show s ≫ (cZ t V W ≫ v.1) = (s ≫ cZ t V W) ≫ v.1
    rw [Category.assoc]
  have h1 : s ≫ (rZ G t V v W d).1 = (schemeHomOverComp s hψ (rZ G t V v W d)).1 :=
    (schemeHomOverComp_coe s hψ _).symm
  rw [h1, rZ, hnat, e1, e2, key]

end Setup

section Main

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
  (t : T ⟶ Spec (CommRingCat.of R))
  (V : T.Opens)
  (W : (pullback t t).Opens)

scoped instance pZ_smooth [Smooth t] : Smooth (pZ t V W) := by
  rw [pZ_def]; infer_instance

theorem pZ_surjective [Smooth t]
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (hW : ∀ x : T, (pullback.diagonal t).base x ∈ W) :
    Function.Surjective (pZ t V W).base := by
  intro x

  obtain ⟨ξ, hξV, hξt, hξx⟩ : ∃ ξ : T, ξ ∈ V ∧ t.base ξ = t.base x ∧ ξ ⤳ x := by
    by_cases hx : t.base x = IsLocalRing.closedPoint R
    · let S := {y : T // t.base y = IsLocalRing.closedPoint R}
      have hSc : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} :=
        (IsLocalRing.isClosed_singleton_closedPoint R).preimage (Scheme.Hom.continuous t)
      haveI : QuasiSober S := hSc.isClosedEmbedding_subtypeVal.quasiSober
      let x' : S := ⟨x, hx⟩
      have hC : irreducibleComponent x' ∈ irreducibleComponents S :=
        irreducibleComponent_mem_irreducibleComponents x'
      obtain ⟨ξ', hξ'⟩ : ∃ ξ' : S, IsGenericPoint ξ' (irreducibleComponent x') :=
        QuasiSober.sober isIrreducible_irreducibleComponent isClosed_irreducibleComponent
      obtain ⟨z, hzC, hzV⟩ := hVs _ hC
      have hUo : IsOpen {y : S | y.1 ∈ V} := V.2.preimage continuous_subtype_val
      have hξ'V : ξ' ∈ {y : S | y.1 ∈ V} := (hξ'.mem_open_set_iff hUo).mpr ⟨z, hzC, hzV⟩
      refine ⟨ξ'.1, hξ'V, by rw [ξ'.2, hx], ?_⟩
      exact (hξ'.specializes mem_irreducibleComponent).map continuous_subtype_val
    · exact ⟨x, hVη x hx, rfl, specializes_rfl⟩

  set s₀ := t.base x with hs₀
  let ιs := t.fiberι s₀
  let πs := t.fiberToSpecResidueField s₀
  let jx : Spec (T.residueField x) ⟶ Spec ((Spec (CommRingCat.of R)).residueField s₀) :=
    Spec.map (t.residueFieldMap x)
  haveI : Flat jx := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    show (t.residueFieldMap x).hom.Flat
    unfold RingHom.Flat
    letI := (t.residueFieldMap x).hom.toAlgebra
    infer_instance
  have hnat : T.fromSpecResidueField x ≫ t = jx ≫ (Spec (CommRingCat.of R)).fromSpecResidueField s₀ :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField t x).symm
  let l : Spec (T.residueField x) ⟶ t.fiber s₀ := pullback.lift (T.fromSpecResidueField x) jx hnat
  have hl : l ≫ ιs = T.fromSpecResidueField x := pullback.lift_fst _ _ _
  have hl' : l ≫ πs = jx := pullback.lift_snd _ _ _
  let F := pullback πs jx
  let pr : F ⟶ t.fiber s₀ := pullback.fst πs jx
  have hm : (pullback.snd πs jx ≫ T.fromSpecResidueField x) ≫ t = (pr ≫ ιs) ≫ t := by
    rw [Category.assoc, hnat, ← pullback.condition_assoc, Category.assoc]
    exact (congrArg (fun k => pr ≫ k) (pullback.condition (f := t)
      (g := (Spec (CommRingCat.of R)).fromSpecResidueField s₀))).symm
  let m : F ⟶ pullback t t := pullback.lift (pullback.snd πs jx ≫ T.fromSpecResidueField x) (pr ≫ ιs) hm
  have hm1 : m ≫ pullback.fst t t = pullback.snd πs jx ≫ T.fromSpecResidueField x := pullback.lift_fst _ _ _
  have hm2 : m ≫ pullback.snd t t = pr ≫ ιs := pullback.lift_snd _ _ _
  let σ : Spec (T.residueField x) ⟶ F := pullback.lift l (𝟙 _) (by rw [hl', Category.id_comp])
  have hσm : σ ≫ m = T.fromSpecResidueField x ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · rw [Category.assoc, hm1, ← Category.assoc, pullback.lift_snd, Category.id_comp, Category.assoc,
        pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, hm2, ← Category.assoc, pullback.lift_fst, hl, Category.assoc,
        pullback.diagonal_snd, Category.comp_id]
  have hσpr : σ ≫ pr ≫ ιs = T.fromSpecResidueField x := by
    rw [← Category.assoc, pullback.lift_fst, hl]
  let pt : Spec (T.residueField x) := IsLocalRing.closedPoint (T.residueField x)
  have hpt : (T.fromSpecResidueField x).base pt = x := Scheme.fromSpecResidueField_apply x pt
  let φ₀ : F := σ.base pt
  have hφ₀W : m.base φ₀ ∈ W := by
    have : m.base φ₀ = (pullback.diagonal t).base x := by
      rw [← hpt, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσm]
    rw [this]; exact hW x

  have hy₀ : ιs.base (pr.base φ₀) = x := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hσpr, hpt]
  obtain ⟨yξ, hyξ⟩ : ξ ∈ Set.range ιs.base := by
    rw [Scheme.Hom.range_fiberι]; exact hξt
  have hspec : yξ ⤳ pr.base φ₀ := by
    rw [← (IsPreimmersion.isEmbedding ιs).isInducing.specializes_iff, hyξ, hy₀]
    exact hξx

  obtain ⟨φ₁, hφ₁, hprφ₁⟩ := Flat.generalizingMap pr hspec
  have hwW : m.base φ₁ ∈ W := (hφ₁.map (Scheme.Hom.continuous m)).mem_open W.2 hφ₀W
  have hwsnd : (pullback.snd t t).base (m.base φ₁) = ξ := by
    rw [← Scheme.Hom.comp_apply, hm2, Scheme.Hom.comp_apply, hprφ₁, hyξ]
  have hwfst : (pullback.fst t t).base (m.base φ₁) = x := by
    rw [← Scheme.Hom.comp_apply, hm1, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply x _
  have hwZ : m.base φ₁ ∈ Zop t V W := by
    rw [Zop, TopologicalSpace.Opens.mem_inf]
    exact ⟨hwW, by rw [Scheme.Hom.mem_preimage, hwsnd]; exact hξV⟩
  refine ⟨⟨m.base φ₁, hwZ⟩, ?_⟩
  rw [pZ_def, Scheme.Hom.comp_apply]
  exact hwfst

theorem isReduced_kernelPair [Smooth t] :
    IsReduced (pullback (pZ t V W) (pZ t V W)) := by
  haveI : Smooth (pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W ≫ t) := inferInstance
  haveI : ∀ k : ↥(pullback (pZ t V W) (pZ t V W)),
      _root_.IsReduced ((pullback (pZ t V W) (pZ t V W)).presheaf.stalk k) := fun k =>
    haveI := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W ≫ t) k).1
    inferInstance
  exact isReduced_of_isReduced_stalk _

theorem dense_kernelPair_fstV [Smooth t]
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) :
    Dense (((pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W) ⁻¹ᵁ V : (pullback (pZ t V W) (pZ t V W)).Opens) :
      Set ↥(pullback (pZ t V W) (pZ t V W))) := by
  intro k
  let g := pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W ≫ t
  haveI : Flat g := inferInstance
  let η : ↥(Spec (CommRingCat.of R)) := (⟨⊥, Ideal.bot_prime⟩ : PrimeSpectrum R)
  have hη : η ⤳ g.base k :=
    (PrimeSpectrum.le_iff_specializes (x := η) (y := g.base k)).mp bot_le
  obtain ⟨k', hk', hgk'⟩ := Flat.generalizingMap g hη
  have hne : η ≠ IsLocalRing.closedPoint R := by
    intro h
    have := congrArg PrimeSpectrum.asIdeal h
    exact IsDiscreteValuationRing.not_a_field R (by simpa [IsLocalRing.closedPoint] using this.symm)
  have hk'V : k' ∈ ((pullback.fst (pZ t V W) (pZ t V W) ≫ pZ t V W) ⁻¹ᵁ V) := by
    rw [Scheme.Hom.mem_preimage]
    apply hVη
    rw [← Scheme.Hom.comp_apply]
    show g.base k' ≠ _
    rw [hgk']; exact hne
  exact closure_mono (Set.singleton_subset_iff.mpr hk'V) hk'.mem_closure

end Main

theorem main
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hd : (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 := by

  set p := pZ t V W with hp
  set r := rZ G t V v W d with hr
  have hsurj : Function.Surjective p.base := pZ_surjective R t V W hVη hVs hd.1
  haveI : Surjective p := ⟨hsurj⟩

  let K := pullback p p
  have hcompat : pullback.fst p p ≫ r.1 = pullback.snd p p ≫ r.1 := by
    haveI : IsReduced K := isReduced_kernelPair R t V W
    let KV : K.Opens := (pullback.fst p p ≫ p) ⁻¹ᵁ V
    haveI : IsDominant KV.ι := by
      rw [isDominant_iff, DenseRange, Scheme.Opens.range_ι]
      exact dense_kernelPair_fstV R t V W hVη
    have hfg : (pullback.fst p p ≫ r.1) ≫ f = (pullback.snd p p ≫ r.1) ≫ f := by
      rw [Category.assoc, Category.assoc, hr, rZ_base, ← hp, pullback.condition_assoc]
    refine ext_of_isDominant_of_isSeparated f hfg KV.ι ?_
    let b : (KV : Scheme.{u}) ⟶ (V : Scheme.{u}) := (pullback.fst p p ≫ p).resLE V KV le_rfl
    have hb : b ≫ V.ι = KV.ι ≫ pullback.fst p p ≫ p := Scheme.Hom.resLE_comp_ι _ _
    have h1 : (KV.ι ≫ pullback.fst p p) ≫ r.1 = b ≫ v.1 :=
      comp_rZ_eq_of_fst G t V v W d hd.2 _ b (by rw [hb, Category.assoc])
    have h2 : (KV.ι ≫ pullback.snd p p) ≫ r.1 = b ≫ v.1 :=
      comp_rZ_eq_of_fst G t V v W d hd.2 _ b (by rw [hb, Category.assoc, ← pullback.condition])
    rw [← Category.assoc, ← Category.assoc, h1, h2]

  have hmem : Sieve.generate (Presieve.singleton p) ∈ Scheme.fppfTopology.{u} T := by
    have h := (Scheme.Hom.cover.{u, 0} (P := @Flat ⊓ @LocallyOfFinitePresentation) p
      ⟨inferInstance, inferInstance⟩).mem_grothendieckTopology
    dsimp only [Scheme.Hom.cover, Precoverage.ZeroHypercover.singleton, PreZeroHypercover.singleton] at h
    rw [Sieve.ofArrows, Presieve.ofArrows_pUnit] at h
    exact h
  have hSA : Presieve.IsSheaf Scheme.fppfTopology.{u} (yoneda.obj A) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hSB : Presieve.IsSheaf Scheme.fppfTopology.{u} (yoneda.obj (Spec (CommRingCat.of R))) :=
    GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _
  have hsheafA : Presieve.IsSheafFor (yoneda.obj A) (Presieve.singleton p) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hSA _ hmem
  have hsheafB : Presieve.IsSheafFor (yoneda.obj (Spec (CommRingCat.of R))) (Presieve.singleton p) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hSB _ hmem
  rw [Presieve.isSheafFor_singleton] at hsheafA hsheafB
  have hcompat' : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ ↑(Zop t V W)), p₁ ≫ p = p₂ ≫ p →
      (yoneda.obj A).map p₁.op r.1 = (yoneda.obj A).map p₂.op r.1 := by
    intro Z p₁ p₂ h12
    change p₁ ≫ r.1 = p₂ ≫ r.1
    rw [← pullback.lift_fst p₁ p₂ h12, Category.assoc, hcompat, ← Category.assoc, pullback.lift_snd]
  obtain ⟨φ₁, hφ₁, huniq⟩ := hsheafA r.1 hcompat'
  change p ≫ φ₁ = r.1 at hφ₁

  have hover : φ₁ ≫ f = t := by
    have hcB : ∀ {Z : Scheme.{u}} (p₁ p₂ : Z ⟶ ↑(Zop t V W)), p₁ ≫ p = p₂ ≫ p →
        (yoneda.obj (Spec (CommRingCat.of R))).map p₁.op (p ≫ t) =
          (yoneda.obj (Spec (CommRingCat.of R))).map p₂.op (p ≫ t) := by
      intro Z p₁ p₂ h12
      change p₁ ≫ p ≫ t = p₂ ≫ p ≫ t
      rw [← Category.assoc, h12, Category.assoc]
    obtain ⟨ψ, hψ, hψuniq⟩ := hsheafB (p ≫ t) hcB
    have e1 : φ₁ ≫ f = ψ := hψuniq (φ₁ ≫ f) (by
      change p ≫ φ₁ ≫ f = p ≫ t
      rw [← Category.assoc, hφ₁, hr, rZ_base])
    have e2 : t = ψ := hψuniq t rfl
    rw [e1, ← e2]
  refine ⟨⟨φ₁, hover⟩, ?_⟩

  let e : (V : Scheme.{u}) ⟶ pullback t t := pullback.lift V.ι V.ι rfl
  have he : e = V.ι ≫ pullback.diagonal t := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, pullback.diagonal_snd, Category.comp_id]
  have herange : Set.range e.base ⊆ Set.range (Zop t V W).ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    show e.base y ∈ Zop t V W
    rw [Zop, TopologicalSpace.Opens.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [he, Scheme.Hom.comp_apply]; exact hd.1 _
    · rw [Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_snd]; exact y.2
  let δ : (V : Scheme.{u}) ⟶ ↑(Zop t V W) := IsOpenImmersion.lift (Zop t V W).ι e herange
  have hδ : δ ≫ (Zop t V W).ι = e := IsOpenImmersion.lift_fac _ _ _
  have hδp : δ ≫ p = 𝟙 _ ≫ V.ι := by
    rw [hp, pZ_def, ← Category.assoc, hδ, pullback.lift_fst, Category.id_comp]
  have hrec := comp_rZ_eq_of_fst G t V v W d hd.2 δ (𝟙 _) hδp
  rw [Category.id_comp] at hrec
  have hδp' : δ ≫ p = V.ι := by rw [hδp, Category.id_comp]
  show V.ι ≫ φ₁ = v.1
  calc V.ι ≫ φ₁ = (δ ≫ p) ≫ φ₁ := by rw [hδp']
    _ = δ ≫ r.1 := by rw [Category.assoc, hφ₁]
    _ = v.1 := hrec

end GoodReductionJacobian.RelativeGroupLaw.DESC
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian.RelativeGroupLaw.DESC"

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra _root_.GoodReductionJacobian _root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension.GoodReductionJacobian in
theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f)
    (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f)
    (hd : (∀ x : T, (pullback.diagonal t).base x ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩)) :
    ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 :=
  GoodReductionJacobian.RelativeGroupLaw.DESC.main R G t V hVη hVs v W d hd

end S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_extension_of_diagonal_difference_extension (solution)
