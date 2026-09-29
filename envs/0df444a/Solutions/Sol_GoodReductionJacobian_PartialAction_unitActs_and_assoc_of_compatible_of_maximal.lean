-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.unitActs_and_assoc_of_compatible_of_maximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c8bd8e6a-58fa-5e53-b6fb-ac24d5169a6e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Theorems.Thm_AlgebraicGeometry_Smooth_isReduced_of_isReduced_of_isLocallyNoetherian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NeronModelInfra (SchemeHomOver)

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent"
p2m_open "GoodReductionJacobian"

namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "pair Defined liftDom liftDom_ι act act_coe UnitActs Assoc modelPoint modelPoint_coe Compatible Maximal hom_comp dom dense_dom hom"
p2m_open "GoodReductionJacobian.PartialAction"

namespace MilneL43

section Points

variable {B T'' T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {t'' : T'' ⟶ B} {g : A ⟶ B}

theorem comp_comp (ψ' : T'' ⟶ T') (hψ' : ψ' ≫ t' = t'') (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ' hψ' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp (ψ' ≫ ψ) (by rw [Category.assoc, hψ, hψ']) x :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem comp_id' (h : 𝟙 T ≫ t = t) (x : SchemeHomOver t g) :
    schemeHomOverComp (𝟙 T) h x = x :=
  Subtype.ext (Category.id_comp _)

theorem comp_congr {ψ₁ ψ₂ : T' ⟶ T} (e : ψ₁ = ψ₂) (h₁ : ψ₁ ≫ t = t') (h₂ : ψ₂ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ₁ h₁ x = schemeHomOverComp ψ₂ h₂ x := by
  subst e; rfl

end Points

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  {P : Scheme.{u}} {p : P ⟶ Spec (CommRingCat.of k)}

section Calculus

variable (a : PartialAction k f p)

theorem pair_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) :
    pair (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x) = ψ ≫ pair γ x := by
  apply pullback.hom_ext <;>
    simp only [pair, schemeHomOverComp_coe, pullback.lift_fst, pullback.lift_snd, Category.assoc]

theorem defined_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.Defined (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x) := by
  rintro _ ⟨τ, rfl⟩
  rw [pair_comp, Scheme.Hom.comp_apply]
  exact hd ⟨_, rfl⟩

theorem liftDom_eq {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x)
    (φ : T ⟶ (a.dom : Scheme.{u})) (h : φ ≫ a.dom.ι = pair γ x) : a.liftDom γ x hd = φ := by
  rw [← cancel_mono a.dom.ι, liftDom_ι, h]

theorem liftDom_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x)
    (hd' : a.Defined (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x)) :
    a.liftDom _ _ hd' = ψ ≫ a.liftDom γ x hd :=
  liftDom_eq a _ _ hd' _ (by rw [Category.assoc, liftDom_ι, pair_comp])

theorem act_comp {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x)
    (hd' : a.Defined (schemeHomOverComp ψ hψ γ) (schemeHomOverComp ψ hψ x)) :
    a.act _ _ hd' = schemeHomOverComp ψ hψ (a.act γ x hd) :=
  Subtype.ext (by simp only [act_coe, schemeHomOverComp_coe, liftDom_comp a ψ hψ γ x hd hd',
    Category.assoc])

theorem act_coe_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {γ γ' : SchemeHomOver t f} {x x' : SchemeHomOver t p} (eγ : γ = γ') (ex : x = x')
    (hd : a.Defined γ x) (hd' : a.Defined γ' x') : (a.act γ x hd).1 = (a.act γ' x' hd').1 := by
  subst eγ ex; rfl

theorem act_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {γ γ' : SchemeHomOver t f} {x x' : SchemeHomOver t p} (eγ : γ = γ') (ex : x = x')
    (hd : a.Defined γ x) (hd' : a.Defined γ' x') : a.act γ x hd = a.act γ' x' hd' := by
  subst eγ ex; rfl

abbrev q (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    pullback f p ⟶ Spec (CommRingCat.of k) :=
  pullback.fst f p ≫ f

def wGP (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    SchemeHomOver (q f p) f :=
  ⟨pullback.fst f p, rfl⟩

def zGP (f : G ⟶ Spec (CommRingCat.of k)) (p : P ⟶ Spec (CommRingCat.of k)) :
    SchemeHomOver (q f p) p :=
  ⟨pullback.snd f p, pullback.condition.symm⟩

@[scoped simp] theorem wGP_coe : (wGP f p).1 = pullback.fst f p := rfl
@[scoped simp] theorem zGP_coe : (zGP f p).1 = pullback.snd f p := rfl

theorem pair_wGP_zGP : pair (wGP f p) (zGP f p) = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [pair, wGP_coe, zGP_coe, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

abbrev tD : (a.dom : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := a.dom.ι ≫ q f p

def wD : SchemeHomOver (tD a) f := schemeHomOverComp a.dom.ι rfl (wGP f p)

def zD : SchemeHomOver (tD a) p := schemeHomOverComp a.dom.ι rfl (zGP f p)

@[scoped simp] theorem wD_coe : (wD a).1 = a.dom.ι ≫ pullback.fst f p := rfl
@[scoped simp] theorem zD_coe : (zD a).1 = a.dom.ι ≫ pullback.snd f p := rfl

theorem pair_wD_zD : pair (wD a) (zD a) = a.dom.ι := by
  rw [wD, zD, pair_comp, pair_wGP_zGP, Category.comp_id]

theorem defined_wD_zD : a.Defined (wD a) (zD a) := by
  rw [Defined, pair_wD_zD, Scheme.Opens.range_ι]

theorem liftDom_wD_zD : a.liftDom (wD a) (zD a) (defined_wD_zD a) = 𝟙 _ :=
  liftDom_eq a _ _ _ _ (by rw [Category.id_comp, pair_wD_zD])

def yD : SchemeHomOver (tD a) p := a.act (wD a) (zD a) (defined_wD_zD a)

@[scoped simp] theorem yD_coe : (yD a).1 = a.hom := by
  simp only [yD, act_coe, liftDom_wD_zD, Category.id_comp]

theorem liftDom_tD {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.liftDom γ x hd ≫ tD a = t := by
  rw [← Category.assoc, liftDom_ι, pair, pullback.lift_fst_assoc]
  exact γ.2

theorem eq_comp_liftDom {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    γ = schemeHomOverComp (a.liftDom γ x hd) (liftDom_tD a γ x hd) (wD a) ∧
      x = schemeHomOverComp (a.liftDom γ x hd) (liftDom_tD a γ x hd) (zD a) := by
  refine ⟨Subtype.ext ?_, Subtype.ext ?_⟩
  · simp only [schemeHomOverComp_coe, wD_coe, ← Category.assoc, liftDom_ι, pair,
      pullback.lift_fst]
  · simp only [schemeHomOverComp_coe, zD_coe, ← Category.assoc, liftDom_ι, pair,
      pullback.lift_snd]

theorem act_eq_comp_yD {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    (γ : SchemeHomOver t f) (x : SchemeHomOver t p) (hd : a.Defined γ x) :
    a.act γ x hd = schemeHomOverComp (a.liftDom γ x hd) (liftDom_tD a γ x hd) (yD a) :=
  Subtype.ext (by simp only [act_coe, schemeHomOverComp_coe, yD_coe])

end Calculus

section Unit

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

def unitSlice (L : RelativeGroupLaw k f) (p : P ⟶ Spec (CommRingCat.of k)) : P ⟶ pullback f p :=
  pair (L.one p) (⟨𝟙 P, Category.id_comp p⟩ : SchemeHomOver p p)

@[reassoc (attr := simp)] theorem unitSlice_snd : unitSlice L p ≫ pullback.snd f p = 𝟙 P := by
  simp only [unitSlice, pair, pullback.lift_snd]

theorem pair_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t p) :
    pair (L.one t) x = x.1 ≫ unitSlice L p := by
  apply pullback.hom_ext
  · simp only [pair, unitSlice, pullback.lift_fst, Category.assoc]
    exact congrArg Subtype.val (L.one_natural p t x.1 x.2).symm
  · simp only [pair, unitSlice, pullback.lift_snd, Category.assoc, Category.comp_id]

def unitOpen : P.Opens := unitSlice L p ⁻¹ᵁ a.dom

def unitLift : ((unitOpen L a : P.Opens) : Scheme.{u}) ⟶ (a.dom : Scheme.{u}) :=
  IsOpenImmersion.lift a.dom.ι ((unitOpen L a).ι ≫ unitSlice L p) (by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact y.2)

@[reassoc (attr := simp)] theorem unitLift_ι : unitLift L a ≫ a.dom.ι = (unitOpen L a).ι ≫ unitSlice L p :=
  IsOpenImmersion.lift_fac _ _ _

variable [IsIntegral P] [IsSeparated p] (V : G.Opens) [Nonempty (V : Scheme.{u})]
  (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι] (hι : ι ≫ p = V.ι ≫ f)

def idV (V : G.Opens) : SchemeHomOver (V.ι ≫ f) (V.ι ≫ f) := ⟨𝟙 _, Category.id_comp _⟩

include hι in

theorem unitLift_hom (hc : a.Compatible L V ι hι) :
    unitLift L a ≫ a.hom = (unitOpen L a).ι := by
  obtain ⟨hdV, hactV⟩ := hc (V.ι ≫ f) (L.one _) (idV V) (idV V) (by rw [L.one_mul])

  have hrange : Set.range ι ⊆ ((unitOpen L a : P.Opens) : Set P) := by
    rintro _ ⟨v, rfl⟩
    have := hdV ⟨v, rfl⟩
    rw [pair_one, modelPoint_coe, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at this
    exact this
  let ιe : (V : Scheme.{u}) ⟶ (unitOpen L a : P.Opens) :=
    IsOpenImmersion.lift (unitOpen L a).ι ι (by rwa [Scheme.Opens.range_ι])
  have hιe : ιe ≫ (unitOpen L a).ι = ι := IsOpenImmersion.lift_fac _ _ _
  haveI : IsOpenImmersion ιe := IsOpenImmersion.of_comp ιe (unitOpen L a).ι
  haveI : Nonempty ((unitOpen L a : P.Opens) : Scheme.{u}) := Nonempty.map ιe inferInstance
  haveI : IrreducibleSpace ((unitOpen L a : P.Opens) : Scheme.{u}) :=
    (unitOpen L a).ι.isOpenEmbedding.irreducibleSpace
  haveI : IsDominant ιe :=
    ⟨ιe.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  haveI : IsReduced ((unitOpen L a : P.Opens) : Scheme.{u}) := isReduced_of_isOpenImmersion (unitOpen L a).ι
  refine ext_of_isDominant_of_isSeparated p ?_ ιe ?_
  · rw [Category.assoc, a.hom_comp, unitLift_ι_assoc, unitSlice_snd_assoc]
  ·
    have hlift : a.liftDom (L.one _) (modelPoint ι hι (idV V)) hdV = ιe ≫ unitLift L a :=
      liftDom_eq a _ _ _ _ (by
        rw [Category.assoc, unitLift_ι, ← Category.assoc, hιe, pair_one, modelPoint_coe, idV,
          Category.id_comp])
    have := congrArg Subtype.val hactV
    rw [act_coe, hlift, modelPoint_coe, Category.assoc] at this
    rw [this, hιe, idV, Category.id_comp]

include hι in

theorem unitActs (hc : a.Compatible L V ι hι) : a.UnitActs L := by
  intro T t x hd
  have hrange : Set.range x.1 ⊆ ((unitOpen L a : P.Opens) : Set P) := by
    rintro _ ⟨τ, rfl⟩
    have := hd ⟨τ, rfl⟩
    rw [pair_one, Scheme.Hom.comp_apply] at this
    exact this
  let x' : T ⟶ (unitOpen L a : P.Opens) :=
    IsOpenImmersion.lift (unitOpen L a).ι x.1 (by rwa [Scheme.Opens.range_ι])
  have hx' : x' ≫ (unitOpen L a).ι = x.1 := IsOpenImmersion.lift_fac _ _ _
  have hlift : a.liftDom (L.one t) x hd = x' ≫ unitLift L a :=
    liftDom_eq a _ _ _ _ (by rw [Category.assoc, unitLift_ι, ← Category.assoc, hx', pair_one])
  apply Subtype.ext
  rw [act_coe, hlift, Category.assoc, unitLift_hom L a V ι hι hc, hx']

end Unit

section MoreCalculus

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

theorem comp_mul {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.mul t x y) =
      L.mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y) :=
  L.mul_natural t t' ψ hψ x y

theorem comp_one {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    schemeHomOverComp ψ hψ (L.one t) = L.one t' :=
  L.one_natural t t' ψ hψ

theorem comp_nmi {T' T : Scheme.{u}} {B C : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} {g' : B ⟶ Spec (CommRingCat.of k)}
    {g : C ⟶ Spec (CommRingCat.of k)}
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t g') (φ : SchemeHomOver g' g) :
    schemeHomOverComp ψ hψ (NeronModelInfra.schemeHomOverComp x φ) =
      NeronModelInfra.schemeHomOverComp (schemeHomOverComp ψ hψ x) φ :=
  Subtype.ext (Category.assoc _ _ _).symm

theorem comp_modelPoint {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (v : SchemeHomOver t (V.ι ≫ f)) :
    schemeHomOverComp ψ hψ (modelPoint ι hι v) = modelPoint ι hι (schemeHomOverComp ψ hψ v) :=
  Subtype.ext (Category.assoc _ _ _).symm

def const {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    SchemeHomOver t g :=
  schemeHomOverComp t (Category.comp_id t) x

@[scoped simp] theorem const_coe {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    (const t x).1 = t ≫ x.1 := rfl

theorem comp_const {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T' T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    schemeHomOverComp ψ hψ (const t x) = const t' x :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, const_coe, ← Category.assoc, hψ])

theorem const_id {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)}
    (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    const (𝟙 _) x = x :=
  Subtype.ext (Category.id_comp _)

theorem comp_kpt_eq {A : Scheme.{u}} {g : A ⟶ Spec (CommRingCat.of k)} {T : Scheme.{u}}
    {t : T ⟶ Spec (CommRingCat.of k)} (τ : Spec (CommRingCat.of k) ⟶ T) (hτ : τ ≫ t = 𝟙 _)
    (x : SchemeHomOver t g) : (schemeHomOverComp τ hτ x).1 = τ ≫ x.1 := rfl

end MoreCalculus

section Structure

variable (L : RelativeGroupLaw k f)

theorem exists_kPoint [IsAlgClosed k] {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX,
      x.1 (IsLocalRing.closedPoint k) ∈ Z := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace tX
  obtain ⟨x, hxZ, hxc⟩ := nonempty_inter_closedPoints hne hZ
  exact ⟨⟨pointOfClosedPoint tX x hxc, pointOfClosedPoint_comp _ _ _⟩,
    by rwa [pointOfClosedPoint_apply]⟩

theorem range_kPoint {X : Scheme.{u}} (x : Spec (CommRingCat.of k) ⟶ X) :
    Set.range x = {x (IsLocalRing.closedPoint k)} := by
  ext y
  constructor
  · rintro ⟨s, rfl⟩
    obtain rfl : s = IsLocalRing.closedPoint k := Subsingleton.elim _ _
    rfl
  · rintro rfl; exact ⟨_, rfl⟩

def kLift {X : Scheme.{u}} (U : X.Opens) (x : Spec (CommRingCat.of k) ⟶ X)
    (hx : x (IsLocalRing.closedPoint k) ∈ U) : Spec (CommRingCat.of k) ⟶ (U : Scheme.{u}) :=
  IsOpenImmersion.lift U.ι x (by
    rw [Scheme.Opens.range_ι, range_kPoint, Set.singleton_subset_iff]; exact hx)

@[reassoc (attr := simp)]
theorem kLift_ι {X : Scheme.{u}} (U : X.Opens) (x : Spec (CommRingCat.of k) ⟶ X)
    (hx : x (IsLocalRing.closedPoint k) ∈ U) : kLift U x hx ≫ U.ι = x :=
  IsOpenImmersion.lift_fac _ _ _

include L in
theorem geometricallyIrreducible [LocallyOfFiniteType f] [QuasiCompact f] [ConnectedSpace G] :
    GeometricallyIrreducible f := by
  obtain ⟨G₀, i, L₀, hoi, -, -, hgi, -, hrange, -⟩ :=
    RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent k L
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  haveI : IsIso i :=
    (isIso_iff_isOpenImmersion_and_epi_base i).mpr ⟨hoi, (TopCat.epi_iff_surjective _).mpr hsurj⟩
  exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIrreducible i f).mp hgi

theorem irreducibleSpace_G [GeometricallyIrreducible f] : IrreducibleSpace G :=
  GeometricallyIrreducible.irreducibleSpace_of_subsingleton f

theorem isReduced_pullback [Smooth f] {Y : Scheme.{u}} (g : Y ⟶ Spec (CommRingCat.of k))
    [IsReduced Y] [IsLocallyNoetherian Y] : IsReduced (pullback f g) :=
  AlgebraicGeometry.Smooth.isReduced_of_isReduced_of_isLocallyNoetherian (pullback.snd f g)

def ltrans (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f (const f g) ⟨𝟙 G, Category.id_comp f⟩).1

theorem kpt_ltrans (g x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x.1 ≫ ltrans L g = (L.mul (𝟙 _) g x).1 := by
  have h : schemeHomOverComp x.1 x.2 (L.mul f (const f g) ⟨𝟙 G, Category.id_comp f⟩) =
      L.mul (𝟙 _) g x := by
    rw [comp_mul, comp_const, const_id]
    congr 1
  exact congrArg Subtype.val h

def transl (p : P ⟶ Spec (CommRingCat.of k)) (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pullback f p ⟶ pullback f p :=
  pair (L.mul (q f p) (const (q f p) g) (wGP f p)) (zGP f p)

theorem transl_q (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    transl L p g ≫ q f p = q f p := by
  simp only [transl, pair, q, pullback.lift_fst_assoc]
  exact (L.mul (q f p) (const (q f p) g) (wGP f p)).2

theorem comp_transl_wGP (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    schemeHomOverComp (transl L p g) (transl_q L g) (wGP f p) =
      L.mul (q f p) (const (q f p) g) (wGP f p) :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, transl, pair, wGP_coe, pullback.lift_fst])

theorem comp_transl_zGP (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    schemeHomOverComp (transl L p g) (transl_q L g) (zGP f p) = zGP f p :=
  Subtype.ext (by simp only [schemeHomOverComp_coe, transl, pair, zGP_coe, pullback.lift_snd])

theorem transl_comp (g h : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    transl L p g ≫ transl L p h = transl L p (L.mul (𝟙 _) h g) := by
  rw [show transl L p h = pair (L.mul (q f p) (const (q f p) h) (wGP f p)) (zGP f p) from rfl,
    ← pair_comp (transl L p g) (transl_q L g), comp_mul, comp_const, comp_transl_wGP,
    comp_transl_zGP, ← L.mul_assoc, transl]
  congr 2
  rw [const, const, const, ← comp_mul]

theorem transl_one : transl L p (L.one _) = 𝟙 _ := by
  rw [transl, const, comp_one, L.one_mul, pair_wGP_zGP]

scoped instance isIso_transl (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    IsIso (transl L p g) :=
  ⟨⟨transl L p (L.inv _ g), by rw [transl_comp, L.inv_mul_cancel, transl_one],
    by rw [transl_comp, L.mul_inv_cancel, transl_one]⟩⟩

end Structure

section Triple

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

abbrev Ω₁ : Scheme.{u} := pullback f (tD a)

abbrev t₁ : Ω₁ a ⟶ Spec (CommRingCat.of k) := pullback.fst f (tD a) ≫ f

theorem snd_tD : pullback.snd f (tD a) ≫ tD a = t₁ a := pullback.condition.symm

def u₁ : SchemeHomOver (t₁ a) f := ⟨pullback.fst f (tD a), rfl⟩

def w₁ : SchemeHomOver (t₁ a) f := schemeHomOverComp (pullback.snd f (tD a)) (snd_tD a) (wD a)

def z₁ : SchemeHomOver (t₁ a) p := schemeHomOverComp (pullback.snd f (tD a)) (snd_tD a) (zD a)

def y₁ : SchemeHomOver (t₁ a) p := schemeHomOverComp (pullback.snd f (tD a)) (snd_tD a) (yD a)

theorem defined_w₁_z₁ : a.Defined (w₁ a) (z₁ a) := defined_comp a _ _ _ _ (defined_wD_zD a)

theorem act_w₁_z₁ : a.act (w₁ a) (z₁ a) (defined_w₁_z₁ a) = y₁ a :=
  act_comp a _ _ _ _ (defined_wD_zD a) _

def c₁ : Ω₁ a ⟶ pullback f p := pair (u₁ a) (y₁ a)

def Ω' : (Ω₁ a).Opens := c₁ a ⁻¹ᵁ a.dom

abbrev O : Scheme.{u} := (Ω' a : (Ω₁ a).Opens)

abbrev tO : O a ⟶ Spec (CommRingCat.of k) := (Ω' a).ι ≫ t₁ a

def uO : SchemeHomOver (tO a) f := schemeHomOverComp (Ω' a).ι rfl (u₁ a)

def wO : SchemeHomOver (tO a) f := schemeHomOverComp (Ω' a).ι rfl (w₁ a)

def zO : SchemeHomOver (tO a) p := schemeHomOverComp (Ω' a).ι rfl (z₁ a)

def yO : SchemeHomOver (tO a) p := schemeHomOverComp (Ω' a).ι rfl (y₁ a)

theorem defined_wO_zO : a.Defined (wO a) (zO a) := defined_comp a _ _ _ _ (defined_w₁_z₁ a)

theorem act_wO_zO : a.act (wO a) (zO a) (defined_wO_zO a) = yO a := by
  rw [yO, ← act_w₁_z₁]; exact act_comp a _ _ _ _ _ _

theorem defined_uO_yO : a.Defined (uO a) (yO a) := by
  rintro _ ⟨ω, rfl⟩
  rw [uO, yO, pair_comp, Scheme.Hom.comp_apply]
  exact ω.2

def φO : SchemeHomOver (tO a) p := a.act (uO a) (yO a) (defined_uO_yO a)

def μO : SchemeHomOver (tO a) f := L.mul (tO a) (uO a) (wO a)

theorem assoc_of_universal (hA : a.Defined (μO L a) (zO a))
    (hB : a.act (μO L a) (zO a) hA = φO a) : a.Assoc L := by
  intro T t γ δ x hd₁ hd₂
  obtain ⟨τD, hτD⟩ : ∃ τD, a.liftDom δ x hd₁ = τD := ⟨_, rfl⟩
  have hτDt : τD ≫ tD a = t := by rw [← hτD]; exact liftDom_tD a δ x hd₁
  have eδ : schemeHomOverComp τD hτDt (wD a) = δ := by
    subst hτD; exact ((eq_comp_liftDom a δ x hd₁).1).symm
  have ex : schemeHomOverComp τD hτDt (zD a) = x := by
    subst hτD; exact ((eq_comp_liftDom a δ x hd₁).2).symm
  have ey : schemeHomOverComp τD hτDt (yD a) = a.act δ x hd₁ := by
    subst hτD; exact (act_eq_comp_yD a δ x hd₁).symm
  obtain ⟨τ₁, hτ₁f, hτ₁s⟩ : ∃ τ₁ : T ⟶ Ω₁ a, τ₁ ≫ pullback.fst f (tD a) = γ.1 ∧
      τ₁ ≫ pullback.snd f (tD a) = τD :=
    ⟨pullback.lift γ.1 τD (by rw [γ.2, hτDt]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hτ₁t : τ₁ ≫ t₁ a = t := by rw [t₁, ← Category.assoc, hτ₁f]; exact γ.2
  have eu₁ : schemeHomOverComp τ₁ hτ₁t (u₁ a) = γ := Subtype.ext hτ₁f
  have ew₁ : schemeHomOverComp τ₁ hτ₁t (w₁ a) = δ := by
    rw [w₁, comp_comp, comp_congr hτ₁s _ hτDt, eδ]
  have ez₁ : schemeHomOverComp τ₁ hτ₁t (z₁ a) = x := by
    rw [z₁, comp_comp, comp_congr hτ₁s _ hτDt, ex]
  have ey₁ : schemeHomOverComp τ₁ hτ₁t (y₁ a) = a.act δ x hd₁ := by
    rw [y₁, comp_comp, comp_congr hτ₁s _ hτDt, ey]
  have hc₁ : τ₁ ≫ c₁ a = pair γ (a.act δ x hd₁) := by
    rw [c₁, ← pair_comp τ₁ hτ₁t, eu₁, ey₁]
  have hrange : Set.range τ₁ ⊆ ((Ω' a : (Ω₁ a).Opens) : Set (Ω₁ a)) := by
    rintro _ ⟨s, rfl⟩
    show (c₁ a) (τ₁ s) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, hc₁]
    exact hd₂ ⟨s, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : T ⟶ O a, τ ≫ (Ω' a).ι = τ₁ :=
    ⟨IsOpenImmersion.lift (Ω' a).ι τ₁ (by rwa [Scheme.Opens.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hτt : τ ≫ tO a = t := by rw [tO, ← Category.assoc, hτ, hτ₁t]
  have euO : schemeHomOverComp τ hτt (uO a) = γ := by
    rw [uO, comp_comp, comp_congr hτ _ hτ₁t, eu₁]
  have ewO : schemeHomOverComp τ hτt (wO a) = δ := by
    rw [wO, comp_comp, comp_congr hτ _ hτ₁t, ew₁]
  have ezO : schemeHomOverComp τ hτt (zO a) = x := by
    rw [zO, comp_comp, comp_congr hτ _ hτ₁t, ez₁]
  have eyO : schemeHomOverComp τ hτt (yO a) = a.act δ x hd₁ := by
    rw [yO, comp_comp, comp_congr hτ _ hτ₁t, ey₁]
  have eμ : schemeHomOverComp τ hτt (μO L a) = L.mul t γ δ := by
    rw [μO, comp_mul, euO, ewO]
  have hd₃' := defined_comp a τ hτt _ _ hA
  have hd₃ : a.Defined (L.mul t γ δ) x := by rwa [eμ, ezO] at hd₃'
  refine ⟨hd₃, Subtype.ext ?_⟩
  calc (a.act γ (a.act δ x hd₁) hd₂).1
      = (a.act _ _ (defined_comp a τ hτt _ _ (defined_uO_yO a))).1 :=
        act_coe_congr a euO.symm eyO.symm _ _
    _ = τ ≫ (φO a).1 := by rw [act_comp a τ hτt _ _ (defined_uO_yO a)]; rfl
    _ = τ ≫ (a.act (μO L a) (zO a) hA).1 := by rw [hB]
    _ = (a.act _ _ hd₃').1 := by rw [act_comp a τ hτt _ _ hA]; rfl
    _ = (a.act (L.mul t γ δ) x hd₃).1 := act_coe_congr a eμ ezO _ _

end Triple

section Equality

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

def Dset : (O a).Opens := pair (μO L a) (zO a) ⁻¹ᵁ a.dom

abbrev OD : Scheme.{u} := (Dset L a : (O a).Opens)

abbrev tOD : OD L a ⟶ Spec (CommRingCat.of k) := (Dset L a).ι ≫ tO a

def uOD : SchemeHomOver (tOD L a) f := schemeHomOverComp (Dset L a).ι rfl (uO a)

def wOD : SchemeHomOver (tOD L a) f := schemeHomOverComp (Dset L a).ι rfl (wO a)

def zOD : SchemeHomOver (tOD L a) p := schemeHomOverComp (Dset L a).ι rfl (zO a)

def yOD : SchemeHomOver (tOD L a) p := schemeHomOverComp (Dset L a).ι rfl (yO a)

def φOD : SchemeHomOver (tOD L a) p := schemeHomOverComp (Dset L a).ι rfl (φO a)

def μOD : SchemeHomOver (tOD L a) f := L.mul (tOD L a) (uOD L a) (wOD L a)

theorem comp_μO : schemeHomOverComp (Dset L a).ι rfl (μO L a) = μOD L a := by
  rw [μO, comp_mul]; rfl

theorem defined_wOD_zOD : a.Defined (wOD L a) (zOD L a) :=
  defined_comp a _ _ _ _ (defined_wO_zO a)

theorem act_wOD_zOD : a.act (wOD L a) (zOD L a) (defined_wOD_zOD L a) = yOD L a := by
  rw [yOD, ← act_wO_zO]; exact act_comp a _ _ _ _ _ _

theorem defined_uOD_yOD : a.Defined (uOD L a) (yOD L a) :=
  defined_comp a _ _ _ _ (defined_uO_yO a)

theorem act_uOD_yOD : a.act (uOD L a) (yOD L a) (defined_uOD_yOD L a) = φOD L a :=
  act_comp a _ _ _ _ _ _

theorem defined_μOD_zOD : a.Defined (μOD L a) (zOD L a) := by
  rintro _ ⟨ω, rfl⟩
  rw [← comp_μO, zOD, pair_comp, Scheme.Hom.comp_apply]
  exact ω.2

def ψOD : SchemeHomOver (tOD L a) p := a.act (μOD L a) (zOD L a) (defined_μOD_zOD L a)

theorem isReduced_OD [Smooth f] [IsIntegral P] [LocallyOfFiniteType p] : IsReduced (OD L a) := by
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsReduced (pullback f p) := isReduced_pullback p
  haveI : IsReduced (a.dom : Scheme.{u}) := isReduced_of_isOpenImmersion a.dom.ι
  haveI : IsReduced (Ω₁ a) := isReduced_pullback (tD a)
  haveI : IsReduced (O a) := isReduced_of_isOpenImmersion (Ω' a).ι
  exact isReduced_of_isOpenImmersion (Dset L a).ι

theorem irreducibleSpace_OD [GeometricallyIrreducible f] [UniversallyOpen f] [IsIntegral P]
    [Nonempty (OD L a)] : IrreducibleSpace (OD L a) := by
  haveI : Nonempty (O a) := Nonempty.map (Dset L a).ι inferInstance
  haveI : Nonempty (Ω₁ a) := Nonempty.map (Ω' a).ι inferInstance
  haveI : Nonempty (a.dom : Scheme.{u}) := Nonempty.map (pullback.snd f (tD a)) inferInstance
  haveI : IrreducibleSpace (a.dom : Scheme.{u}) := a.dom.ι.isOpenEmbedding.irreducibleSpace
  haveI : IrreducibleSpace (O a) := (Ω' a).ι.isOpenEmbedding.irreducibleSpace
  exact (Dset L a).ι.isOpenEmbedding.irreducibleSpace

theorem nonempty_kPoint_V [IsAlgClosed k] [LocallyOfFiniteType f] (V : G.Opens)
    [Nonempty (V : Scheme.{u})] :
    Nonempty (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (V.ι ≫ f)) := by
  have hne : (V : Set G).Nonempty :=
    ⟨(Classical.arbitrary V).1, (Classical.arbitrary V).2⟩
  obtain ⟨g, hg⟩ := exists_kPoint f V.2.isLocallyClosed hne
  exact ⟨⟨kLift V g.1 hg, by rw [← Category.assoc, kLift_ι]; exact g.2⟩⟩

variable {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)

include hι in

theorem exists_kPoint_OD (hc : a.Compatible L V ι hι)
    (v₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (V.ι ≫ f)) :
    ∃ (o : Spec (CommRingCat.of k) ⟶ OD L a) (ho : o ≫ tOD L a = 𝟙 _),
      schemeHomOverComp o ho (uOD L a) = L.one _ ∧
      schemeHomOverComp o ho (wOD L a) = L.one _ ∧
      schemeHomOverComp o ho (zOD L a) = modelPoint ι hι v₀ := by
  obtain ⟨hde, eact⟩ := hc (𝟙 _) (L.one _) v₀ v₀ (by rw [L.one_mul])

  obtain ⟨d, hd⟩ : ∃ d, a.liftDom (L.one _) (modelPoint ι hι v₀) hde = d := ⟨_, rfl⟩
  have hdt : d ≫ tD a = 𝟙 _ := by rw [← hd]; exact liftDom_tD a _ _ hde
  have edw : schemeHomOverComp d hdt (wD a) = L.one _ := by
    subst hd; exact ((eq_comp_liftDom a _ _ hde).1).symm
  have edz : schemeHomOverComp d hdt (zD a) = modelPoint ι hι v₀ := by
    subst hd; exact ((eq_comp_liftDom a _ _ hde).2).symm
  have edy : schemeHomOverComp d hdt (yD a) = modelPoint ι hι v₀ := by
    subst hd; rw [← act_eq_comp_yD a _ _ hde, eact]

  obtain ⟨o₁, ho₁f, ho₁s⟩ : ∃ o₁ : Spec (CommRingCat.of k) ⟶ Ω₁ a,
      o₁ ≫ pullback.fst f (tD a) = (L.one (𝟙 _)).1 ∧ o₁ ≫ pullback.snd f (tD a) = d :=
    ⟨pullback.lift (L.one (𝟙 _)).1 d (by rw [(L.one _).2, hdt]), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have ho₁t : o₁ ≫ t₁ a = 𝟙 _ := by rw [t₁, ← Category.assoc, ho₁f]; exact (L.one _).2
  have eu₁ : schemeHomOverComp o₁ ho₁t (u₁ a) = L.one _ := Subtype.ext ho₁f
  have ew₁ : schemeHomOverComp o₁ ho₁t (w₁ a) = L.one _ := by
    rw [w₁, comp_comp, comp_congr ho₁s _ hdt, edw]
  have ez₁ : schemeHomOverComp o₁ ho₁t (z₁ a) = modelPoint ι hι v₀ := by
    rw [z₁, comp_comp, comp_congr ho₁s _ hdt, edz]
  have ey₁ : schemeHomOverComp o₁ ho₁t (y₁ a) = modelPoint ι hι v₀ := by
    rw [y₁, comp_comp, comp_congr ho₁s _ hdt, edy]
  have hc₁ : o₁ ≫ c₁ a = pair (L.one _) (modelPoint ι hι v₀) := by
    rw [c₁, ← pair_comp o₁ ho₁t, eu₁, ey₁]
  have hoΩ' : o₁ (IsLocalRing.closedPoint k) ∈ Ω' a := by
    show c₁ a (o₁ _) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, hc₁]
    exact hde ⟨_, rfl⟩

  let oO := kLift (Ω' a) o₁ hoΩ'
  have hoO : oO ≫ (Ω' a).ι = o₁ := kLift_ι _ _ _
  have hoOt : oO ≫ tO a = 𝟙 _ := by rw [tO, ← Category.assoc, hoO, ho₁t]
  have euO : schemeHomOverComp oO hoOt (uO a) = L.one _ := by
    rw [uO, comp_comp, comp_congr hoO _ ho₁t, eu₁]
  have ewO : schemeHomOverComp oO hoOt (wO a) = L.one _ := by
    rw [wO, comp_comp, comp_congr hoO _ ho₁t, ew₁]
  have ezO : schemeHomOverComp oO hoOt (zO a) = modelPoint ι hι v₀ := by
    rw [zO, comp_comp, comp_congr hoO _ ho₁t, ez₁]
  have eμO : schemeHomOverComp oO hoOt (μO L a) = L.one _ := by
    rw [μO, comp_mul, euO, ewO, L.one_mul]
  have hoD : oO (IsLocalRing.closedPoint k) ∈ Dset L a := by
    show pair (μO L a) (zO a) (oO _) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, ← pair_comp oO hoOt, eμO, ezO]
    exact hde ⟨_, rfl⟩

  refine ⟨kLift (Dset L a) oO hoD, by rw [tOD, kLift_ι_assoc, hoOt], ?_, ?_, ?_⟩
  · rw [uOD, comp_comp, comp_congr (kLift_ι _ _ _) _ hoOt, euO]
  · rw [wOD, comp_comp, comp_congr (kLift_ι _ _ _) _ hoOt, ewO]
  · rw [zOD, comp_comp, comp_congr (kLift_ι _ _ _) _ hoOt, ezO]

include hι in

theorem ψOD_eq_φOD [IsAlgClosed k] [GeometricallyIrreducible f] [UniversallyOpen f] [Smooth f]
    [IsIntegral P] [LocallyOfFiniteType p] [IsSeparated p]
    [Nonempty (V : Scheme.{u})] [IsOpenImmersion ι] (hc : a.Compatible L V ι hι) :
    ψOD L a = φOD L a := by

  let W₁ : (OD L a).Opens := (zOD L a).1 ⁻¹ᵁ (Scheme.Hom.opensRange ι)
  let tW₁ : (W₁ : Scheme.{u}) ⟶ Spec (CommRingCat.of k) := W₁.ι ≫ tOD L a
  let u' : SchemeHomOver tW₁ f := schemeHomOverComp W₁.ι rfl (uOD L a)
  let w' : SchemeHomOver tW₁ f := schemeHomOverComp W₁.ι rfl (wOD L a)
  let z' : SchemeHomOver tW₁ p := schemeHomOverComp W₁.ι rfl (zOD L a)
  let x' : SchemeHomOver tW₁ (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift ι z'.1 (by rintro _ ⟨ω, rfl⟩; exact ω.2), by
      rw [← hι, ← Category.assoc, IsOpenImmersion.lift_fac]; exact z'.2⟩
  have hxz : modelPoint ι hι x' = z' := Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  let VG : SchemeHomOver (V.ι ≫ f) f := ⟨V.ι, rfl⟩
  let vx : SchemeHomOver tW₁ f := L.mul tW₁ w' (NeronModelInfra.schemeHomOverComp x' VG)
  let uvx : SchemeHomOver tW₁ f := L.mul tW₁ u' vx

  let W₂ : (W₁ : Scheme.{u}).Opens := vx.1 ⁻¹ᵁ V ⊓ uvx.1 ⁻¹ᵁ V
  let jW : (W₂ : Scheme.{u}) ⟶ OD L a := W₂.ι ≫ W₁.ι
  have hjt : jW ≫ tOD L a = W₂.ι ≫ tW₁ := Category.assoc _ _ _
  let t₂ := W₂.ι ≫ tW₁
  let u₂ : SchemeHomOver t₂ f := schemeHomOverComp jW hjt (uOD L a)
  let w₂ : SchemeHomOver t₂ f := schemeHomOverComp jW hjt (wOD L a)
  let x₂ : SchemeHomOver t₂ (V.ι ≫ f) := schemeHomOverComp W₂.ι rfl x'
  have eu₂ : schemeHomOverComp W₂.ι rfl u' = u₂ := comp_comp _ _ _ _ _
  have ew₂ : schemeHomOverComp W₂.ι rfl w' = w₂ := comp_comp _ _ _ _ _
  have ez₂ : schemeHomOverComp jW hjt (zOD L a) = modelPoint ι hι x₂ := by
    rw [show modelPoint ι hι x₂ = schemeHomOverComp W₂.ι rfl (modelPoint ι hι x') from
      (comp_modelPoint ι hι _ _ _).symm, hxz]
    exact (comp_comp _ _ _ _ _).symm
  have evx : schemeHomOverComp W₂.ι rfl vx =
      L.mul t₂ w₂ (NeronModelInfra.schemeHomOverComp x₂ VG) := by
    rw [comp_mul, comp_nmi, ew₂]
  have euvx : schemeHomOverComp W₂.ι rfl uvx =
      L.mul t₂ u₂ (L.mul t₂ w₂ (NeronModelInfra.schemeHomOverComp x₂ VG)) := by
    rw [comp_mul, evx, eu₂]

  let vxV : SchemeHomOver t₂ (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι (schemeHomOverComp W₂.ι rfl vx).1
      (by rw [Scheme.Opens.range_ι]; rintro _ ⟨ω, rfl⟩; exact ω.2.1), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (schemeHomOverComp W₂.ι rfl vx).2⟩
  have hvxV : NeronModelInfra.schemeHomOverComp vxV VG =
      L.mul t₂ w₂ (NeronModelInfra.schemeHomOverComp x₂ VG) := by
    rw [← evx]; exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  let uvxV : SchemeHomOver t₂ (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι (schemeHomOverComp W₂.ι rfl uvx).1
      (by rw [Scheme.Opens.range_ι]; rintro _ ⟨ω, rfl⟩; exact ω.2.2), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact (schemeHomOverComp W₂.ι rfl uvx).2⟩
  have huvxV : NeronModelInfra.schemeHomOverComp uvxV VG =
      L.mul t₂ u₂ (NeronModelInfra.schemeHomOverComp vxV VG) := by
    rw [hvxV, ← euvx]; exact Subtype.ext (IsOpenImmersion.lift_fac _ _ _)

  obtain ⟨hd1, e1⟩ := hc t₂ w₂ x₂ vxV hvxV
  obtain ⟨hd2, e2⟩ := hc t₂ u₂ vxV uvxV huvxV
  obtain ⟨hd3, e3⟩ := hc t₂ (L.mul t₂ u₂ w₂) x₂ uvxV (by rw [huvxV, hvxV, L.mul_assoc])

  have ey₂ : schemeHomOverComp jW hjt (yOD L a) = modelPoint ι hι vxV := by
    rw [← e1, ← act_wOD_zOD, ← act_comp a jW hjt _ _ (defined_wOD_zOD L a)
      (defined_comp a jW hjt _ _ (defined_wOD_zOD L a))]
    exact act_congr a rfl ez₂ _ _
  have hagree : jW ≫ (ψOD L a).1 = jW ≫ (φOD L a).1 := by
    have lhs : schemeHomOverComp jW hjt (ψOD L a) = modelPoint ι hι uvxV := by
      rw [← e3, ψOD, ← act_comp a jW hjt _ _ (defined_μOD_zOD L a)
        (defined_comp a jW hjt _ _ (defined_μOD_zOD L a))]
      exact act_congr a (by rw [μOD, comp_mul]) ez₂ _ _
    have rhs : schemeHomOverComp jW hjt (φOD L a) = modelPoint ι hι uvxV := by
      rw [← e2, ← act_uOD_yOD, ← act_comp a jW hjt _ _ (defined_uOD_yOD L a)
        (defined_comp a jW hjt _ _ (defined_uOD_yOD L a))]
      exact act_congr a rfl ey₂ _ _
    exact (congrArg Subtype.val lhs).trans (congrArg Subtype.val rhs).symm

  haveI : LocallyOfFiniteType f := inferInstance
  obtain ⟨v₀⟩ := nonempty_kPoint_V (f := f) V
  obtain ⟨o, ho, eou, eow, eoz⟩ := exists_kPoint_OD L a ι hι hc v₀
  have hoW₁ : o (IsLocalRing.closedPoint k) ∈ W₁ := by
    show (zOD L a).1 (o _) ∈ Scheme.Hom.opensRange ι
    rw [← Scheme.Hom.comp_apply, ← comp_kpt_eq o ho, eoz, modelPoint_coe, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let oW := kLift W₁ o hoW₁
  have hoWt : oW ≫ tW₁ = 𝟙 _ := by rw [kLift_ι_assoc, ho]
  have eox : schemeHomOverComp oW hoWt x' = v₀ := by
    apply Subtype.ext
    rw [← cancel_mono ι, schemeHomOverComp_coe, Category.assoc, IsOpenImmersion.lift_fac,
      ← modelPoint_coe ι hι, ← eoz]
    show oW ≫ W₁.ι ≫ (zOD L a).1 = _
    rw [kLift_ι_assoc]; rfl
  have eow' : schemeHomOverComp oW hoWt w' = L.one _ := by
    rw [comp_comp, comp_congr (kLift_ι _ _ _) _ ho, eow]
  have eou' : schemeHomOverComp oW hoWt u' = L.one _ := by
    rw [comp_comp, comp_congr (kLift_ι _ _ _) _ ho, eou]
  have eovx : schemeHomOverComp oW hoWt vx = NeronModelInfra.schemeHomOverComp v₀ VG := by
    rw [comp_mul, comp_nmi, eow', eox, L.one_mul]
  have eouvx : schemeHomOverComp oW hoWt uvx = NeronModelInfra.schemeHomOverComp v₀ VG := by
    rw [comp_mul, eovx, eou', L.one_mul]
  have hv₀V : (NeronModelInfra.schemeHomOverComp v₀ VG).1 (IsLocalRing.closedPoint k) ∈ V := by
    rw [NeronModelInfra.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact (v₀.1 _).2
  haveI : Nonempty (W₂ : Scheme.{u}) := ⟨⟨oW (IsLocalRing.closedPoint k), by
    constructor
    · show vx.1 (oW _) ∈ V
      rw [← Scheme.Hom.comp_apply, ← comp_kpt_eq oW hoWt, eovx]; exact hv₀V
    · show uvx.1 (oW _) ∈ V
      rw [← Scheme.Hom.comp_apply, ← comp_kpt_eq oW hoWt, eouvx]; exact hv₀V⟩⟩

  haveI : Nonempty (OD L a) := Nonempty.map jW inferInstance
  haveI : IsReduced (OD L a) := isReduced_OD L a
  haveI : IrreducibleSpace (OD L a) := irreducibleSpace_OD L a
  haveI : IsDominant jW := ⟨jW.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace _⟩
  apply Subtype.ext
  exact ext_of_isDominant_of_isSeparated p (by rw [(ψOD L a).2, (φOD L a).2]) jW hagree

end Equality

section Definedness

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)

theorem act_comp_μO {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    [IsAlgClosed k] [GeometricallyIrreducible f] [UniversallyOpen f] [Smooth f]
    [IsIntegral P] [LocallyOfFiniteType p] [IsSeparated p]
    [Nonempty (V : Scheme.{u})] [IsOpenImmersion ι] (hc : a.Compatible L V ι hι)
    {T : Scheme.{u}} (τ : T ⟶ O a) {t : T ⟶ Spec (CommRingCat.of k)} (hτ : τ ≫ tO a = t)
    (hdef : a.Defined (schemeHomOverComp τ hτ (μO L a)) (schemeHomOverComp τ hτ (zO a))) :
    a.act _ _ hdef = schemeHomOverComp τ hτ (φO a) := by
  have hr : Set.range τ ⊆ ((Dset L a : (O a).Opens) : Set (O a)) := by
    rintro _ ⟨s, rfl⟩
    show pair (μO L a) (zO a) (τ s) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, ← pair_comp τ hτ]
    exact hdef ⟨s, rfl⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : T ⟶ OD L a, τ' ≫ (Dset L a).ι = τ :=
    ⟨IsOpenImmersion.lift (Dset L a).ι τ (by rwa [Scheme.Opens.range_ι]),
      IsOpenImmersion.lift_fac _ _ _⟩
  have hτ't : τ' ≫ tOD L a = t := by rw [tOD, ← Category.assoc, hτ', hτ]
  have e1 : schemeHomOverComp τ hτ (μO L a) = schemeHomOverComp τ' hτ't (μOD L a) := by
    rw [← comp_μO, comp_comp]; exact comp_congr hτ'.symm _ _ _
  have e2 : schemeHomOverComp τ hτ (zO a) = schemeHomOverComp τ' hτ't (zOD L a) := by
    rw [zOD, comp_comp]; exact comp_congr hτ'.symm _ _ _
  have e3 : schemeHomOverComp τ hτ (φO a) = schemeHomOverComp τ' hτ't (φOD L a) := by
    rw [φOD, comp_comp]; exact comp_congr hτ'.symm _ _ _
  rw [act_congr a e1 e2 hdef (defined_comp a τ' hτ't _ _ (defined_μOD_zOD L a)),
    act_comp a τ' hτ't _ _ (defined_μOD_zOD L a), e3, ← ψOD_eq_φOD L a ι hι hc]
  rfl

private def _root_.GoodReductionJacobian.PartialAction.MilneL43.toPartialMap : (pullback f p).PartialMap P := ⟨a.dom, a.dense_dom, a.hom⟩

p2m_export "GoodReductionJacobian.PartialAction.MilneL43" "toPartialMap"

theorem le_dom_of_equiv [IsReduced (pullback f p)] [P.IsSeparated] (hm : a.Maximal)
    (π' : (pullback f p).PartialMap P) (h : π'.equiv (toPartialMap a)) : π'.domain ≤ a.dom := by
  have h1 : π'.toRationalMap = (toPartialMap a).toRationalMap :=
    Scheme.PartialMap.toRationalMap_eq_iff.mpr h
  have h2 : (toPartialMap a).toRationalMap.domain = a.dom := by
    refine hm (toPartialMap a).toRationalMap.domain (toPartialMap a).toRationalMap.toPartialMap.hom
      (toPartialMap a).le_domain_toRationalMap ?_
    have := (toPartialMap a).toPartialMap_toRationalMap_restrict
    rwa [Scheme.PartialMap.restrict_hom] at this
  calc π'.domain ≤ π'.toRationalMap.domain := π'.le_domain_toRationalMap
    _ = a.dom := by rw [h1, h2]

variable (u₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)

def slice : (a.dom : Scheme.{u}) ⟶ Ω₁ a :=
  pullback.lift (tD a ≫ u₀.1) (𝟙 _) (by rw [Category.assoc, u₀.2, Category.comp_id, Category.id_comp])

@[reassoc (attr := simp)]
theorem slice_fst : slice a u₀ ≫ pullback.fst f (tD a) = tD a ≫ u₀.1 := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem slice_snd : slice a u₀ ≫ pullback.snd f (tD a) = 𝟙 _ := pullback.lift_snd _ _ _

theorem slice_t₁ : slice a u₀ ≫ t₁ a = tD a := by
  rw [t₁, slice_fst_assoc, u₀.2, Category.comp_id]

theorem comp_slice_u₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (u₁ a) = const (tD a) u₀ :=
  Subtype.ext (slice_fst a u₀)

theorem comp_slice_w₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (w₁ a) = wD a := by
  rw [w₁, comp_comp, comp_congr (slice_snd a u₀) _ (Category.id_comp _), comp_id']

theorem comp_slice_z₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (z₁ a) = zD a := by
  rw [z₁, comp_comp, comp_congr (slice_snd a u₀) _ (Category.id_comp _), comp_id']

theorem comp_slice_y₁ : schemeHomOverComp (slice a u₀) (slice_t₁ a u₀) (y₁ a) = yD a := by
  rw [y₁, comp_comp, comp_congr (slice_snd a u₀) _ (Category.id_comp _), comp_id']

def E : (a.dom : Scheme.{u}).Opens := slice a u₀ ⁻¹ᵁ Ω' a

abbrev tE : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ Spec (CommRingCat.of k) :=
  (E a u₀).ι ≫ tD a

def sliceE : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ O a :=
  IsOpenImmersion.lift (Ω' a).ι ((E a u₀).ι ≫ slice a u₀) (by
    rintro _ ⟨e, rfl⟩
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_apply]
    exact e.2)

@[reassoc (attr := simp)]
theorem sliceE_ι : sliceE a u₀ ≫ (Ω' a).ι = (E a u₀).ι ≫ slice a u₀ := IsOpenImmersion.lift_fac _ _ _

theorem sliceE_tO : sliceE a u₀ ≫ tO a = tE a u₀ := by
  rw [tO, sliceE_ι_assoc, slice_t₁]

theorem comp_sliceE_uO :
    schemeHomOverComp (sliceE a u₀) (sliceE_tO a u₀) (uO a) = const (tE a u₀) u₀ := by
  rw [uO, comp_comp, comp_congr (sliceE_ι a u₀) _ (by rw [Category.assoc, slice_t₁]),
    ← comp_comp _ rfl _ (slice_t₁ a u₀), comp_slice_u₁, comp_const]

theorem comp_sliceE_wO : schemeHomOverComp (sliceE a u₀) (sliceE_tO a u₀) (wO a) =
    schemeHomOverComp (E a u₀).ι rfl (wD a) := by
  rw [wO, comp_comp, comp_congr (sliceE_ι a u₀) _ (by rw [Category.assoc, slice_t₁]),
    ← comp_comp _ rfl _ (slice_t₁ a u₀), comp_slice_w₁]

theorem comp_sliceE_zO : schemeHomOverComp (sliceE a u₀) (sliceE_tO a u₀) (zO a) =
    schemeHomOverComp (E a u₀).ι rfl (zD a) := by
  rw [zO, comp_comp, comp_congr (sliceE_ι a u₀) _ (by rw [Category.assoc, slice_t₁]),
    ← comp_comp _ rfl _ (slice_t₁ a u₀), comp_slice_z₁]

def ε : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}) ⟶ pullback f p :=
  (E a u₀).ι ≫ a.dom.ι ≫ transl L p u₀

scoped instance : IsOpenImmersion (ε L a u₀) := by
  unfold ε; infer_instance

theorem ε_eq : ε L a u₀ = sliceE a u₀ ≫ pair (μO L a) (zO a) := by
  rw [← pair_comp (sliceE a u₀) (sliceE_tO a u₀), μO, comp_mul, comp_sliceE_uO, comp_sliceE_wO,
    comp_sliceE_zO, ε, transl, ← pair_comp (a.dom.ι) rfl, comp_mul, comp_const, ← wD, ← zD,
    ← pair_comp (E a u₀).ι rfl, comp_mul, comp_const]

theorem defined_μO_zO {V : G.Opens} (ι : (V : Scheme.{u}) ⟶ P) (hι : ι ≫ p = V.ι ≫ f)
    [IsAlgClosed k] [GeometricallyIrreducible f] [UniversallyOpen f] [Smooth f]
    [LocallyOfFiniteType f] [IsIntegral P] [LocallyOfFiniteType p] [IsSeparated p]
    [Nonempty (V : Scheme.{u})] [IsOpenImmersion ι] (hc : a.Compatible L V ι hι)
    (hm : a.Maximal) : a.Defined (μO L a) (zO a) := by
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  haveI : IsReduced (pullback f p) := isReduced_pullback p
  haveI : P.IsSeparated := ⟨by rw [← terminal.comp_from p]; infer_instance⟩
  haveI : IrreducibleSpace G := irreducibleSpace_G (f := f)
  suffices h : ∀ ω : O a, ω ∈ Dset L a by rintro _ ⟨ω, rfl⟩; exact h ω
  intro ω
  by_contra hω

  obtain ⟨ωk, hωk⟩ := exists_kPoint (tO a) (Dset L a).2.isClosed_compl.isLocallyClosed ⟨ω, hω⟩
  let u₀ : SchemeHomOver (𝟙 _) f := schemeHomOverComp ωk.1 ωk.2 (uO a)
  let d₀ : Spec (CommRingCat.of k) ⟶ (a.dom : Scheme.{u}) :=
    ωk.1 ≫ (Ω' a).ι ≫ pullback.snd f (tD a)
  have hd₀t : d₀ ≫ tD a = 𝟙 _ := by
    show (ωk.1 ≫ (Ω' a).ι ≫ pullback.snd f (tD a)) ≫ tD a = 𝟙 _
    rw [Category.assoc, Category.assoc, snd_tD]; exact ωk.2
  have hd₀ : d₀ ≫ slice a u₀ = ωk.1 ≫ (Ω' a).ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, slice_fst, ← Category.assoc, hd₀t, Category.id_comp]; rfl
    · show (ωk.1 ≫ (Ω' a).ι ≫ pullback.snd f (tD a)) ≫ slice a u₀ ≫ pullback.snd f (tD a) = _
      rw [slice_snd, Category.comp_id, Category.assoc]
  have hd₀E : d₀ (IsLocalRing.closedPoint k) ∈ E a u₀ := by
    show slice a u₀ (d₀ _) ∈ Ω' a
    rw [← Scheme.Hom.comp_apply, hd₀, Scheme.Hom.comp_apply]
    exact (ωk.1 _).2

  obtain ⟨v₀⟩ := nonempty_kPoint_V (f := f) V
  let VG : SchemeHomOver (V.ι ≫ f) f := ⟨V.ι, rfl⟩
  have hopen : IsOpen ((ltrans L u₀) ⁻¹' (V : Set G)) := V.2.preimage (ltrans L u₀).continuous
  have hne : ((ltrans L u₀) ⁻¹' (V : Set G)).Nonempty := by
    refine ⟨(L.mul (𝟙 _) (L.inv _ u₀) (NeronModelInfra.schemeHomOverComp v₀ VG)).1
      (IsLocalRing.closedPoint k), ?_⟩
    show ltrans L u₀ _ ∈ V
    rw [← Scheme.Hom.comp_apply, kpt_ltrans, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul,
      NeronModelInfra.schemeHomOverComp_coe, Scheme.Hom.comp_apply]
    exact (v₀.1 _).2
  obtain ⟨g₁, hg₁V, hg₁⟩ := exists_kPoint f (V.2.inter hopen).isLocallyClosed
    (nonempty_preirreducible_inter V.2 hopen ⟨_, (Classical.arbitrary V).2⟩ hne)
  have hug₁ : (L.mul (𝟙 _) u₀ g₁).1 (IsLocalRing.closedPoint k) ∈ V := by
    rw [← kpt_ltrans, Scheme.Hom.comp_apply]; exact hg₁
  let g₁V : SchemeHomOver (𝟙 _) (V.ι ≫ f) :=
    ⟨kLift V g₁.1 hg₁V, by rw [← Category.assoc, kLift_ι]; exact g₁.2⟩
  let ug₁V : SchemeHomOver (𝟙 _) (V.ι ≫ f) :=
    ⟨kLift V (L.mul (𝟙 _) u₀ g₁).1 hug₁, by rw [← Category.assoc, kLift_ι]; exact (L.mul _ u₀ g₁).2⟩
  have hg₁G : NeronModelInfra.schemeHomOverComp g₁V VG = g₁ := Subtype.ext (kLift_ι V g₁.1 hg₁V)
  have hug₁G : NeronModelInfra.schemeHomOverComp ug₁V VG =
      L.mul (𝟙 _) u₀ (NeronModelInfra.schemeHomOverComp g₁V VG) := by
    rw [hg₁G]; exact Subtype.ext (kLift_ι V _ hug₁)
  obtain ⟨hde, eact⟩ := hc (𝟙 _) (L.one _) g₁V g₁V (by rw [L.one_mul])
  obtain ⟨hdu, -⟩ := hc (𝟙 _) u₀ g₁V ug₁V hug₁G

  obtain ⟨d₁, hd₁⟩ : ∃ d₁, a.liftDom (L.one _) (modelPoint ι hι g₁V) hde = d₁ := ⟨_, rfl⟩
  have hd₁t : d₁ ≫ tD a = 𝟙 _ := by rw [← hd₁]; exact liftDom_tD a _ _ hde
  have ed₁w : schemeHomOverComp d₁ hd₁t (wD a) = L.one _ := by
    subst hd₁; exact ((eq_comp_liftDom a _ _ hde).1).symm
  have ed₁z : schemeHomOverComp d₁ hd₁t (zD a) = modelPoint ι hι g₁V := by
    subst hd₁; exact ((eq_comp_liftDom a _ _ hde).2).symm
  have ed₁y : schemeHomOverComp d₁ hd₁t (yD a) = modelPoint ι hι g₁V := by
    subst hd₁; rw [← act_eq_comp_yD a _ _ hde, eact]
  have hd₁s : (d₁ ≫ slice a u₀) ≫ t₁ a = 𝟙 _ := by rw [Category.assoc, slice_t₁, hd₁t]
  have hd₁E : d₁ (IsLocalRing.closedPoint k) ∈ E a u₀ := by
    show c₁ a (slice a u₀ (d₁ _)) ∈ a.dom
    have : d₁ ≫ slice a u₀ ≫ c₁ a = pair u₀ (modelPoint ι hι g₁V) := by
      rw [← Category.assoc, c₁, ← pair_comp _ hd₁s, ← comp_comp d₁ hd₁t _ (slice_t₁ a u₀),
        ← comp_comp d₁ hd₁t _ (slice_t₁ a u₀), comp_slice_u₁, comp_slice_y₁, comp_const,
        const_id, ed₁y]
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, this]
    exact hdu ⟨_, rfl⟩
  obtain ⟨d₁E, hd₁Eι⟩ : ∃ d₁E : Spec (CommRingCat.of k) ⟶ (E a u₀ : (a.dom : Scheme.{u}).Opens),
      d₁E ≫ (E a u₀).ι = d₁ := ⟨kLift (E a u₀) d₁ hd₁E, kLift_ι _ _ hd₁E⟩
  have hd₁Et : d₁E ≫ tE a u₀ = 𝟙 _ := by rw [tE, ← Category.assoc, hd₁Eι, hd₁t]
  have hεd₁ : d₁E ≫ ε L a u₀ = pair u₀ (modelPoint ι hι g₁V) := by
    rw [ε_eq, ← Category.assoc, ← pair_comp _ (by rw [Category.assoc, sliceE_tO, hd₁Et]),
      ← comp_comp d₁E hd₁Et _ (sliceE_tO a u₀), ← comp_comp d₁E hd₁Et _ (sliceE_tO a u₀),
      μO, comp_mul, comp_sliceE_uO, comp_sliceE_wO, comp_sliceE_zO, comp_mul,
      comp_const, const_id, comp_comp, comp_comp, comp_congr hd₁Eι _ hd₁t,
      comp_congr hd₁Eι _ hd₁t, ed₁w, ed₁z, L.mul_one]

  let E₃ : ((E a u₀ : (a.dom : Scheme.{u}).Opens) : Scheme.{u}).Opens := sliceE a u₀ ⁻¹ᵁ Dset L a
  have hd₁E₃ : d₁E (IsLocalRing.closedPoint k) ∈ E₃ := by
    show pair (μO L a) (zO a) (sliceE a u₀ (d₁E _)) ∈ a.dom
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← ε_eq, hεd₁]
    exact hdu ⟨_, rfl⟩
  have hE₃ : E₃ ≤ ε L a u₀ ⁻¹ᵁ a.dom := by
    intro e he
    show ε L a u₀ e ∈ a.dom
    rw [ε_eq, Scheme.Hom.comp_apply]
    exact he

  let W : (pullback f p).Opens := ε L a u₀ ''ᵁ E₃
  have hWr : W ≤ Scheme.Hom.opensRange (ε L a u₀) := Scheme.Hom.image_le_opensRange _ _
  have hWd : W ≤ a.dom := by
    rintro _ ⟨e, he, rfl⟩; exact hE₃ he
  have hWdense : Dense (W : Set ↥(pullback f p)) :=
    W.2.dense ⟨_, ⟨_, hd₁E₃, rfl⟩⟩
  let π' : (pullback f p).PartialMap P :=
    ⟨Scheme.Hom.opensRange (ε L a u₀),
      (Scheme.Hom.opensRange (ε L a u₀)).2.dense ⟨_, ⟨d₁E (IsLocalRing.closedPoint k), rfl⟩⟩,
      (Scheme.Hom.isoOpensRange (ε L a u₀)).inv ≫ sliceE a u₀ ≫ (φO a).1⟩
  have hequiv : π'.equiv (toPartialMap a) := by
    refine ⟨W, hWdense, hWr, hWd, ?_⟩
    rw [Scheme.PartialMap.restrict_hom, Scheme.PartialMap.restrict_hom]
    show (pullback f p).homOfLE hWr ≫ (Scheme.Hom.isoOpensRange (ε L a u₀)).inv ≫ sliceE a u₀ ≫
        (φO a).1 = (pullback f p).homOfLE hWd ≫ a.hom
    have hiso : (Scheme.Hom.isoImage (ε L a u₀) E₃).hom ≫ (pullback f p).homOfLE hWr ≫
        (Scheme.Hom.isoOpensRange (ε L a u₀)).inv = E₃.ι := by
      rw [← cancel_mono (ε L a u₀), Category.assoc, Category.assoc,
        Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι]

    have hτ : (E₃.ι ≫ sliceE a u₀) ≫ tO a = E₃.ι ≫ tE a u₀ := by rw [Category.assoc, sliceE_tO]
    have hdef : a.Defined (schemeHomOverComp (E₃.ι ≫ sliceE a u₀) hτ (μO L a))
        (schemeHomOverComp (E₃.ι ≫ sliceE a u₀) hτ (zO a)) := by
      rintro _ ⟨e, rfl⟩
      rw [pair_comp, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
      exact e.2
    have hlift : a.liftDom _ _ hdef = (Scheme.Hom.isoImage (ε L a u₀) E₃).hom ≫
        (pullback f p).homOfLE hWd :=
      liftDom_eq a _ _ hdef _ (by
        rw [Category.assoc, Scheme.homOfLE_ι, Scheme.Hom.isoImage_hom_ι, pair_comp, ε_eq,
          Category.assoc])
    have key := congrArg Subtype.val (act_comp_μO L a ι hι hc (E₃.ι ≫ sliceE a u₀) hτ hdef)
    rw [act_coe, hlift, schemeHomOverComp_coe] at key
    simp only [Category.assoc] at key
    rw [← cancel_epi (Scheme.Hom.isoImage (ε L a u₀) E₃).hom, reassoc_of% hiso]
    exact key.symm

  have hle := le_dom_of_equiv a hm π' hequiv
  obtain ⟨d₀E, hd₀Eι⟩ : ∃ d₀E : Spec (CommRingCat.of k) ⟶ (E a u₀ : (a.dom : Scheme.{u}).Opens),
      d₀E ≫ (E a u₀).ι = d₀ := ⟨kLift (E a u₀) d₀ hd₀E, kLift_ι _ _ hd₀E⟩
  have hd₀ε : ε L a u₀ (d₀E (IsLocalRing.closedPoint k)) ∈ a.dom :=
    hle ⟨_, rfl⟩
  have hsl : d₀E ≫ sliceE a u₀ = ωk.1 := by
    rw [← cancel_mono (Ω' a).ι, Category.assoc, sliceE_ι, ← Category.assoc, hd₀Eι, hd₀]
  apply hωk
  show pair (μO L a) (zO a) (ωk.1 _) ∈ a.dom
  rw [← hsl, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply (sliceE a u₀), ← ε_eq]
  exact hd₀ε

end Definedness

section Assembly

theorem unitActs_and_assoc (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    [Smooth f] (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι) (hm : a.Maximal) :
    a.UnitActs L ∧ a.Assoc L := by
  haveI : GeometricallyIrreducible f := geometricallyIrreducible L
  have hA : a.Defined (μO L a) (zO a) := defined_μO_zO L a ι hι hc hm
  suffices hB : a.act (μO L a) (zO a) hA = φO a from
    ⟨fun {T} => unitActs L a V ι hι hc (T := T), fun {T} => assoc_of_universal L a hA hB (T := T)⟩
  have h1 : schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (μO L a) = μO L a := comp_id' _ _
  have h2 : schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (zO a) = zO a := comp_id' _ _
  have h3 : schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (φO a) = φO a := comp_id' _ _
  have hdef : a.Defined (schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (μO L a))
      (schemeHomOverComp (𝟙 (O a)) (Category.id_comp _) (zO a)) := by rwa [h1, h2]
  rw [← act_congr a h1 h2 hdef hA, act_comp_μO L a ι hι hc (𝟙 (O a)) (Category.id_comp _) hdef, h3]

end Assembly

end MilneL43
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction.MilneL43"

end PartialAction
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction.MilneL43 P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction"

end GoodReductionJacobian
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction.MilneL43 P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction.MilneL43 P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal.GoodReductionJacobian"

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι) (hm : a.Maximal) :
    a.UnitActs L ∧ a.Assoc L :=
  GoodReductionJacobian.PartialAction.MilneL43.unitActs_and_assoc k f L p V ι hι a hc hm

end S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_unitActs_and_assoc_of_compatible_of_maximal (solution)
