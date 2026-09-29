-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isGreatest_opens_difference_extension
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6d43f5d9-8891-59c9-bacd-2156e6e77081

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension.GoodReductionJacobian"

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "mul_inv_cancel one_natural mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul"
namespace GLUE
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem eq_on_inf_of_eq_on_dense {P A B : Scheme.{u}} (sP : P ⟶ B) (f : A ⟶ B) [IsSeparated f] [IsReduced P]
    (W₁ W₂ : P.Opens) (g₁ : ↑W₁ ⟶ A) (g₂ : ↑W₂ ⟶ A)
    (hg₁ : g₁ ≫ f = W₁.ι ≫ sP) (hg₂ : g₂ ≫ f = W₂.ι ≫ sP)
    (W₀ : P.Opens) (h₀ : W₀ ≤ W₁ ⊓ W₂)
    (hdense : ((W₁ ⊓ W₂ : P.Opens) : Set P) ⊆ closure (W₀ : Set P))
    (hagree : P.homOfLE (h₀.trans inf_le_left) ≫ g₁ = P.homOfLE (h₀.trans inf_le_right) ≫ g₂) :
    P.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁) ≫ g₁ = P.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂) ≫ g₂ := by
  haveI : IsReduced (↑(W₁ ⊓ W₂) : Scheme.{u}) := isReduced_of_isOpenImmersion (W₁ ⊓ W₂).ι
  haveI : IsDominant (P.homOfLE h₀) := by
    rw [isDominant_iff]
    have hrange : Set.range (P.homOfLE h₀).base = (Subtype.val : ↥(W₁ ⊓ W₂) → P) ⁻¹' (W₀ : Set P) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        show ((P.homOfLE h₀).base x).1 ∈ (W₀ : Set P)
        rw [Scheme.homOfLE_apply]
        exact x.2
      · intro hy
        refine ⟨⟨y.1, hy⟩, ?_⟩
        apply Subtype.ext
        rw [Scheme.homOfLE_apply]
    intro y
    rw [hrange]
    have hcl : (Subtype.val ⁻¹' closure (W₀ : Set P) : Set ↥(W₁ ⊓ W₂)) =
        closure (Subtype.val ⁻¹' (W₀ : Set P)) :=
      (IsOpen.isOpenMap_subtype_val (W₁ ⊓ W₂).2).preimage_closure_eq_closure_preimage continuous_subtype_val _
    have hy : y ∈ closure (Subtype.val ⁻¹' (W₀ : Set P) : Set ↥(W₁ ⊓ W₂)) := by
      rw [← hcl]; exact hdense y.2
    exact hy
  have hfg : (P.homOfLE (inf_le_left : W₁ ⊓ W₂ ≤ W₁) ≫ g₁) ≫ f =
      (P.homOfLE (inf_le_right : W₁ ⊓ W₂ ≤ W₂) ≫ g₂) ≫ f := by
    rw [Category.assoc, hg₁, Category.assoc, hg₂, ← Category.assoc, Scheme.homOfLE_ι, ← Category.assoc,
      Scheme.homOfLE_ι]
  refine ext_of_isDominant_of_isSeparated f hfg (P.homOfLE h₀) ?_
  rw [← Category.assoc, Scheme.homOfLE_homOfLE, ← Category.assoc, Scheme.homOfLE_homOfLE]
  exact hagree

theorem pullback_fst_comp_eq_of_eq_on_inf {P A : Scheme.{u}} (U U' Z : P.Opens) (eU : U ≤ Z) (eU' : U' ≤ Z)
    (gU : ↑U ⟶ A) (gU' : ↑U' ⟶ A)
    (hUU' : P.homOfLE (inf_le_left : U ⊓ U' ≤ U) ≫ gU = P.homOfLE (inf_le_right : U ⊓ U' ≤ U') ≫ gU') :
    pullback.fst (P.homOfLE eU) (P.homOfLE eU') ≫ gU = pullback.snd (P.homOfLE eU) (P.homOfLE eU') ≫ gU' := by
  set i := P.homOfLE eU
  set i' := P.homOfLE eU'
  have hcond : pullback.fst i i' ≫ U.ι = pullback.snd i i' ≫ U'.ι := by
    rw [← Scheme.homOfLE_ι P eU, ← Category.assoc, pullback.condition, Category.assoc, Scheme.homOfLE_ι]
  have hrange : Set.range (pullback.fst i i' ≫ U.ι).base ⊆ Set.range (U ⊓ U').ι.base := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨z, rfl⟩
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_inf]
    constructor
    · rw [Scheme.Hom.comp_apply]; exact ((pullback.fst i i').base z).2
    · rw [hcond, Scheme.Hom.comp_apply]; exact ((pullback.snd i i').base z).2
  let ℓ := IsOpenImmersion.lift (U ⊓ U').ι (pullback.fst i i' ≫ U.ι) hrange
  have hℓ : ℓ ≫ (U ⊓ U').ι = pullback.fst i i' ≫ U.ι := IsOpenImmersion.lift_fac _ _ _
  have h1 : ℓ ≫ P.homOfLE (inf_le_left : U ⊓ U' ≤ U) = pullback.fst i i' := by
    rw [← cancel_mono U.ι, Category.assoc, Scheme.homOfLE_ι, hℓ]
  have h2 : ℓ ≫ P.homOfLE (inf_le_right : U ⊓ U' ≤ U') = pullback.snd i i' := by
    rw [← cancel_mono U'.ι, Category.assoc, Scheme.homOfLE_ι, hℓ, hcond]
  rw [← h1, ← h2, Category.assoc, Category.assoc, hUU']

theorem exists_glue_of_eq_on_dense {P A B : Scheme.{u}} (sP : P ⟶ B) (f : A ⟶ B) [IsSeparated f] [IsReduced P]
    (W₁ W₂ : P.Opens) (g₁ : ↑W₁ ⟶ A) (g₂ : ↑W₂ ⟶ A)
    (hg₁ : g₁ ≫ f = W₁.ι ≫ sP) (hg₂ : g₂ ≫ f = W₂.ι ≫ sP)
    (W₀ : P.Opens) (h₀ : W₀ ≤ W₁ ⊓ W₂)
    (hdense : ((W₁ ⊓ W₂ : P.Opens) : Set P) ⊆ closure (W₀ : Set P))
    (hagree : P.homOfLE (h₀.trans inf_le_left) ≫ g₁ = P.homOfLE (h₀.trans inf_le_right) ≫ g₂) :
    ∃ g : ↑(W₁ ⊔ W₂) ⟶ A, P.homOfLE le_sup_left ≫ g = g₁ ∧ P.homOfLE le_sup_right ≫ g = g₂ := by
  have hinf := eq_on_inf_of_eq_on_dense sP f W₁ W₂ g₁ g₂ hg₁ hg₂ W₀ h₀ hdense hagree
  have h₀' : W₀ ≤ W₂ ⊓ W₁ := h₀.trans (le_of_eq (inf_comm W₁ W₂))
  have hdense' : ((W₂ ⊓ W₁ : P.Opens) : Set P) ⊆ closure (W₀ : Set P) := by
    rw [inf_comm]; exact hdense
  have hinf' := eq_on_inf_of_eq_on_dense sP f W₂ W₁ g₂ g₁ hg₂ hg₁ W₀ h₀' hdense' hagree.symm

  have hle : ∀ b : Bool, cond b W₁ W₂ ≤ W₁ ⊔ W₂ := by
    intro b; cases b
    · exact le_sup_right
    · exact le_sup_left
  let 𝒰 : (↑(W₁ ⊔ W₂) : Scheme.{u}).OpenCover :=
    Scheme.Cover.mkOfCovers (P := @IsOpenImmersion) Bool (fun b => (↑(cond b W₁ W₂) : Scheme.{u}))
      (fun b => P.homOfLE (hle b))
      (by
        rintro ⟨q, hq⟩
        rcases TopologicalSpace.Opens.mem_sup.mp hq with h | h
        · exact ⟨true, ⟨q, h⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩
        · exact ⟨false, ⟨q, h⟩, Subtype.ext (Scheme.homOfLE_apply _ _)⟩)
      (fun b => inferInstance)
  let fs : ∀ b : Bool, (↑(cond b W₁ W₂) : Scheme.{u}) ⟶ A := fun b =>
    match b with
    | true => g₁
    | false => g₂
  have key : ∀ (b b' : Bool),
      pullback.fst (P.homOfLE (hle b)) (P.homOfLE (hle b')) ≫ fs b =
        pullback.snd (P.homOfLE (hle b)) (P.homOfLE (hle b')) ≫ fs b' := by
    intro b b'
    cases b <;> cases b'
    · exact pullback_fst_comp_eq_of_eq_on_inf W₂ W₂ _ _ _ g₂ g₂ rfl
    · exact pullback_fst_comp_eq_of_eq_on_inf W₂ W₁ _ _ _ g₂ g₁ hinf'
    · exact pullback_fst_comp_eq_of_eq_on_inf W₁ W₂ _ _ _ g₁ g₂ hinf
    · exact pullback_fst_comp_eq_of_eq_on_inf W₁ W₁ _ _ _ g₁ g₁ rfl
  refine ⟨Scheme.Cover.glueMorphisms 𝒰 fs key, ?_, ?_⟩
  · exact Scheme.Cover.ι_glueMorphisms 𝒰 fs key true
  · exact Scheme.Cover.ι_glueMorphisms 𝒰 fs key false

end GoodReductionJacobian.RelativeGroupLaw.GLUE

end

noncomputable section
namespace FltWs29
namespace C1
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension.GoodReductionJacobian TopologicalSpace Topology"

theorem inv_natural {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (schemeHomOverComp ψ hψ x) := by
  set y := schemeHomOverComp ψ hψ x
  set z := schemeHomOverComp ψ hψ (G.inv t x)
  have h : G.mul t' z y = G.one t' := by
    simp only [y, z, ← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  calc z = G.mul t' z (G.one t') := (G.mul_one t' z).symm
    _ = G.mul t' z (G.mul t' y (G.inv t' y)) := by rw [G.mul_inv_cancel]
    _ = G.mul t' (G.mul t' z y) (G.inv t' y) := by rw [G.mul_assoc]
    _ = G.inv t' y := by rw [h, G.one_mul]

section Main
variable {R : Type u} [CommRing R] {T : Scheme.{u}}

def prodOpen (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) : (pullback t t).Opens :=
  (pullback.fst t t) ⁻¹ᵁ V ⊓ (pullback.snd t t) ⁻¹ᵁ V

theorem mem_prodOpen_iff (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) (p : ↑(pullback t t)) :
    p ∈ prodOpen t V ↔ (pullback.fst t t).base p ∈ V ∧ (pullback.snd t t).base p ∈ V := Iff.rfl

def prFst (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) : (prodOpen t V).toScheme ⟶ V.toScheme :=
  (pullback t t).homOfLE inf_le_left ≫ (pullback.fst t t ∣_ V)

def prSnd (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) : (prodOpen t V).toScheme ⟶ V.toScheme :=
  (pullback t t).homOfLE inf_le_right ≫ (pullback.snd t t ∣_ V)

theorem bD_ι (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) :
    prFst t V ≫ V.ι = (prodOpen t V).ι ≫ pullback.fst t t := by
  rw [prFst, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

theorem cD_ι (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) :
    prSnd t V ≫ V.ι = (prodOpen t V).ι ≫ pullback.snd t t := by
  rw [prSnd, Category.assoc, morphismRestrict_ι, ← Category.assoc, Scheme.homOfLE_ι]

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

def pt₁ (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f) :
    SchemeHomOver ((prodOpen t V).ι ≫ pullback.fst t t ≫ t) f :=
  ⟨prFst t V ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, bD_ι, Category.assoc]⟩

def pt₂ (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens) (v : SchemeHomOver (V.ι ≫ t) f) :
    SchemeHomOver ((prodOpen t V).ι ≫ pullback.fst t t ≫ t) f :=
  ⟨prSnd t V ≫ v.1, by
    rw [Category.assoc, v.2, ← Category.assoc, cD_ι, Category.assoc, ← pullback.condition]⟩

def diffMap (G : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens)
    (v : SchemeHomOver (V.ι ≫ t) f) : SchemeHomOver ((prodOpen t V).ι ≫ pullback.fst t t ≫ t) f :=
  G.mul _ (pt₁ t V v) (G.inv _ (pt₂ t V v))

theorem recovery_core (G : RelativeGroupLaw R f) (t : T ⟶ Spec (CommRingCat.of R)) (V : T.Opens)
    (v : SchemeHomOver (V.ι ≫ t) f)
    {S : Scheme.{u}} (g : S ⟶ Spec (CommRingCat.of R)) (x y z : SchemeHomOver g f)
    (a' : S ⟶ (prodOpen t V).toScheme) (b c : S ⟶ V.toScheme)
    (hg : g = a' ≫ (prodOpen t V).ι ≫ pullback.fst t t ≫ t)
    (hx : x.1 = a' ≫ (diffMap G t V v).1) (hy : y.1 = c ≫ v.1) (hz : z.1 = b ≫ v.1)
    (hb : a' ≫ prFst t V = b) (hc : a' ≫ prSnd t V = c) :
    G.mul g x y = z := by
  subst hg
  have ex : x = schemeHomOverComp a' rfl (diffMap G t V v) := Subtype.ext (by rw [schemeHomOverComp_coe, hx])
  have ey : y = schemeHomOverComp a' rfl (pt₂ t V v) := Subtype.ext (by
    rw [schemeHomOverComp_coe, hy]; show c ≫ v.1 = a' ≫ prSnd t V ≫ v.1; rw [← Category.assoc, hc])
  have ez : z = schemeHomOverComp a' rfl (pt₁ t V v) := Subtype.ext (by
    rw [schemeHomOverComp_coe, hz]; show b ≫ v.1 = a' ≫ prFst t V ≫ v.1; rw [← Category.assoc, hb])
  rw [ex, ey, ez]
  unfold diffMap
  rw [G.mul_natural, inv_natural, G.mul_assoc, G.inv_mul_cancel, G.mul_one]

end Main
end FltWs29.C1
end

noncomputable section
namespace FltWs29
namespace C1
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension.GoodReductionJacobian TopologicalSpace Topology"

section Main2
variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {T : Scheme.{u}}

theorem dense_of_generic_fibre_subset (t : T ⟶ Spec (CommRingCat.of R)) [Flat t] (V : T.Opens)
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) : Dense (V : Set T) := by
  intro x
  by_cases hx : t.base x ≠ IsLocalRing.closedPoint R
  · exact subset_closure (hVη x hx)
  · push_neg at hx
    let η : ↥(Spec (CommRingCat.of R)) := (⊥ : PrimeSpectrum R)
    have hη : η ⤳ t.base x := (PrimeSpectrum.le_iff_specializes η (t.base x)).mp bot_le
    obtain ⟨x', hx'x, hx'η⟩ := Flat.generalizingMap t hη
    have hne : t.base x' ≠ IsLocalRing.closedPoint R := by
      intro h
      apply IsDiscreteValuationRing.not_a_field R
      have h2 : (η : PrimeSpectrum R).asIdeal = (IsLocalRing.closedPoint R).asIdeal := by
        rw [← h]; exact congrArg PrimeSpectrum.asIdeal hx'η.symm
      exact h2.symm
    exact closure_mono (Set.singleton_subset_iff.mpr (hVη x' hne)) (specializes_iff_mem_closure.mp hx'x)

theorem dense_prodOpen (t : T ⟶ Spec (CommRingCat.of R)) [Flat t] [UniversallyOpen t] (V : T.Opens)
    (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V) :
    Dense ((prodOpen t V : (pullback t t).Opens) : Set ↑(pullback t t)) := by
  have hV := dense_of_generic_fibre_subset t V hVη
  have h1 : IsOpenMap (pullback.fst t t).base := Scheme.Hom.isOpenMap (pullback.fst t t)
  have h2 : IsOpenMap (pullback.snd t t).base := Scheme.Hom.isOpenMap (pullback.snd t t)
  exact (hV.preimage h1).inter_of_isOpen_left (hV.preimage h2) ((pullback.fst t t) ⁻¹ᵁ V).2

theorem isReduced_pullback (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] : IsReduced (pullback t t) := by
  haveI : ∀ x : ↑(pullback t t), _root_.IsReduced ((pullback t t).presheaf.stalk x) := fun x => by
    haveI := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing R
      (pullback.fst t t ≫ t) x).1
    infer_instance
  exact isReduced_of_isReduced_stalk _

variable {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem isSeparated_of_isSeparated_over (f : A ⟶ Spec (CommRingCat.of R)) [IsSeparated f] : A.IsSeparated := by
  constructor
  rw [← terminal.comp_from f]
  infer_instance

theorem mem_opens_of_base {X : Scheme.{u}} (U : X.Opens) (y : ↑U) : U.ι.base y ∈ U := by
  have h : U.ι.base y ∈ Set.range U.ι.base := ⟨y, rfl⟩
  rwa [Scheme.Opens.range_ι] at h

theorem main (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ p : ↑(pullback t t), (pullback.fst t t).base p ∈ V → (pullback.snd t t).base p ∈ V → p ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) ∧
      (∀ (W' : (pullback t t).Opens) (d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f)
        (W₀ : (pullback t t).Opens) (h₀ : W₀ ≤ W ⊓ W'),
        ((W' : Set ↑(pullback t t)) ⊆ closure (W₀ : Set ↑(pullback t t))) →
        (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 = (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ d'.1 →
        W' ≤ W ∧ ∀ (S : Scheme.{u}) (a' : S ⟶ ↑W') (a : S ⟶ ↑W), a' ≫ W'.ι = a ≫ W.ι → a' ≫ d'.1 = a ≫ d.1) := by
  haveI : IsReduced (pullback t t) := isReduced_pullback t
  haveI : A.IsSeparated := isSeparated_of_isSeparated_over f
  letI : (pullback t t).Over (Spec (CommRingCat.of R)) := ⟨pullback.fst t t ≫ t⟩
  letI : A.Over (Spec (CommRingCat.of R)) := ⟨f⟩
  have hDd : Dense ((prodOpen t V : (pullback t t).Opens) : Set ↑(pullback t t)) := dense_prodOpen t V hVη
  let pΦ : (pullback t t).PartialMap A := ⟨prodOpen t V, hDd, (diffMap G t V v).1⟩
  have hpΦ : pΦ.IsOver (Spec (CommRingCat.of R)) := by
    rw [Scheme.PartialMap.isOver_iff, Scheme.PartialMap.compHom_hom]
    exact (diffMap G t V v).2
  let u := pΦ.toRationalMap
  haveI hu : u.IsOver (Spec (CommRingCat.of R)) := ⟨⟨pΦ, hpΦ, rfl⟩⟩
  let dW := u.toPartialMap
  have hdWover : dW.IsOver (Spec (CommRingCat.of R)) :=
    Scheme.PartialMap.isOver_toRationalMap_iff_of_isSeparated.mp
      (by rw [Scheme.RationalMap.toRationalMap_toPartialMap]; exact hu)
  have hdW : dW.hom ≫ f = dW.domain.ι ≫ pullback.fst t t ≫ t := by
    have h := Scheme.PartialMap.isOver_iff.mp hdWover
    rwa [Scheme.PartialMap.compHom_hom] at h
  have hDW : prodOpen t V ≤ u.domain := pΦ.le_domain_toRationalMap
  have hres : (pullback t t).homOfLE hDW ≫ dW.hom = (diffMap G t V v).1 := by
    have h := Scheme.PartialMap.toPartialMap_toRationalMap_restrict pΦ
    rwa [Scheme.PartialMap.restrict_hom] at h
  refine ⟨u.domain, ⟨dW.hom, hdW⟩, ?_, ?_, ?_⟩
  ·
    intro p h1 h2
    exact hDW (show p ∈ prodOpen t V from ⟨h1, h2⟩)
  ·
    intro S a b c hb hc
    have hrange : Set.range (a ≫ u.domain.ι).base ⊆ Set.range (prodOpen t V).ι.base := by
      rintro _ ⟨s, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (a ≫ u.domain.ι).base s ∈ prodOpen t V
      rw [mem_prodOpen_iff]
      constructor
      · have e : (pullback.fst t t).base (u.domain.ι.base (a.base s)) = V.ι.base (b.base s) := by
          have e0 := congrArg (fun k => k.base s) hb
          simpa using e0
        show (pullback.fst t t).base (u.domain.ι.base (a.base s)) ∈ V
        rw [e]; exact mem_opens_of_base V _
      · have e : (pullback.snd t t).base (u.domain.ι.base (a.base s)) = V.ι.base (c.base s) := by
          have e0 := congrArg (fun k => k.base s) hc
          simpa using e0
        show (pullback.snd t t).base (u.domain.ι.base (a.base s)) ∈ V
        rw [e]; exact mem_opens_of_base V _
    let a' := IsOpenImmersion.lift (prodOpen t V).ι (a ≫ u.domain.ι) hrange
    have ha' : a' ≫ (prodOpen t V).ι = a ≫ u.domain.ι := IsOpenImmersion.lift_fac _ _ _
    have haa : a' ≫ (pullback t t).homOfLE hDW = a := by
      rw [← cancel_mono u.domain.ι, Category.assoc, Scheme.homOfLE_ι, ha']
    refine recovery_core G t V v _ _ _ _ a' b c ?_ ?_ rfl rfl ?_ ?_
    · rw [← Category.assoc a', ha', Category.assoc]
    · show a ≫ dW.hom = a' ≫ (diffMap G t V v).1
      rw [← hres, ← Category.assoc, haa]
    · rw [← cancel_mono V.ι, Category.assoc, bD_ι, ← Category.assoc, ha', Category.assoc]
      exact hb
    · rw [← cancel_mono V.ι, Category.assoc, cD_ι, ← Category.assoc, ha', Category.assoc]
      exact hc
  ·
    intro W' d' W₀ h₀ hcl hagree
    have hdense' : ((u.domain ⊓ W' : (pullback t t).Opens) : Set ↑(pullback t t)) ⊆ closure (W₀ : Set _) :=
      fun p hp => hcl hp.2
    obtain ⟨g, hg₁, hg₂⟩ := GoodReductionJacobian.RelativeGroupLaw.GLUE.exists_glue_of_eq_on_dense
      (pullback.fst t t ≫ t) f u.domain W' dW.hom d'.1 hdW d'.2 W₀ h₀ hdense' hagree

    have hDsup : prodOpen t V ≤ u.domain ⊔ W' := hDW.trans le_sup_left
    let q : (pullback t t).PartialMap A := ⟨u.domain ⊔ W', hDd.mono (fun p hp => hDsup hp), g⟩
    have hq : q.toRationalMap = u := by
      rw [show u = pΦ.toRationalMap from rfl, Scheme.PartialMap.toRationalMap_eq_iff]
      refine ⟨prodOpen t V, hDd, hDsup, le_rfl, ?_⟩
      rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]
      show (pullback t t).homOfLE hDsup ≫ g = (pullback t t).homOfLE le_rfl ≫ (diffMap G t V v).1
      rw [← hres, ← hg₁]
      simp only [← Category.assoc, Scheme.homOfLE_homOfLE]
    have hle : u.domain ⊔ W' ≤ u.domain := by
      have h := q.le_domain_toRationalMap
      rwa [hq] at h
    refine ⟨le_sup_right.trans hle, ?_⟩
    intro S a' a haa'
    have e : a' ≫ (pullback t t).homOfLE (le_sup_right : W' ≤ u.domain ⊔ W') =
        a ≫ (pullback t t).homOfLE (le_sup_left : u.domain ≤ u.domain ⊔ W') := by
      rw [← cancel_mono (u.domain ⊔ W').ι, Category.assoc, Scheme.homOfLE_ι, Category.assoc, Scheme.homOfLE_ι]
      exact haa'
    show a' ≫ d'.1 = a ≫ dW.hom
    rw [← hg₂, ← hg₁, ← Category.assoc, e, Category.assoc]

end Main2
end FltWs29.C1
end

theorem solution
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) [IsSeparated f]
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (V : T.Opens) (hVη : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ V)
    (hVs : ∀ Z ∈ irreducibleComponents {x : T // t.base x = IsLocalRing.closedPoint R}, ∃ x ∈ Z, x.1 ∈ V)
    (v : SchemeHomOver (V.ι ≫ t) f) :
    ∃ (W : (pullback t t).Opens) (d : SchemeHomOver (W.ι ≫ pullback.fst t t ≫ t) f),
      (∀ p : ↑(pullback t t), (pullback.fst t t).base p ∈ V → (pullback.snd t t).base p ∈ V → p ∈ W) ∧
      (∀ (S : Scheme.{u}) (a : S ⟶ ↑W) (b c : S ⟶ ↑V)
        (hb : a ≫ W.ι ≫ pullback.fst t t = b ≫ V.ι) (hc : a ≫ W.ι ≫ pullback.snd t t = c ≫ V.ι),
        G.mul (a ≫ W.ι ≫ pullback.fst t t ≫ t)
            ⟨a ≫ d.1, by rw [Category.assoc, d.2]⟩
            ⟨c ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hc, Category.assoc, Category.assoc,
              ← pullback.condition]⟩ =
          ⟨b ≫ v.1, by rw [Category.assoc, v.2, ← Category.assoc, ← hb, Category.assoc, Category.assoc]⟩) ∧
      (∀ (W' : (pullback t t).Opens) (d' : SchemeHomOver (W'.ι ≫ pullback.fst t t ≫ t) f)
        (W₀ : (pullback t t).Opens) (h₀ : W₀ ≤ W ⊓ W'),
        ((W' : Set ↑(pullback t t)) ⊆ closure (W₀ : Set ↑(pullback t t))) →
        (pullback t t).homOfLE (h₀.trans inf_le_left) ≫ d.1 = (pullback t t).homOfLE (h₀.trans inf_le_right) ≫ d'.1 →
        W' ≤ W ∧ ∀ (S : Scheme.{u}) (a' : S ⟶ ↑W') (a : S ⟶ ↑W), a' ≫ W'.ι = a ≫ W.ι → a' ≫ d'.1 = a ≫ d.1) :=
  FltWs29.C1.main G t V hVη v

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGreatest_opens_difference_extension (solution)
