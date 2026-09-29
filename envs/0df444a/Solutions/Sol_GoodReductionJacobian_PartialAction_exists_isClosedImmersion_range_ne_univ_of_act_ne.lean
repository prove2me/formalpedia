-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.exists_isClosedImmersion_range_ne_univ_of_act_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ee3400af-fca4-55b5-9404-6929ef0eb4d0

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem
import Theorems.Thm_AlgebraicGeometry_exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open NeronModelInfra (SchemeHomOver)

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_geometricallyConnected_range_eq_connectedComponent RelativeGroupLaw.exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem"
p2m_open "GoodReductionJacobian"

namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "pair Defined liftDom liftDom_ι act act_coe UnitActs Assoc Stable dom"
p2m_open "GoodReductionJacobian.PartialAction"

namespace IsotropyB3

section Points

variable {B T'' T' T A : Scheme.{u}} {t : T ⟶ B} {t' : T' ⟶ B} {t'' : T'' ⟶ B} {g : A ⟶ B}

theorem comp_comp (ψ' : T'' ⟶ T') (hψ' : ψ' ≫ t' = t'') (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x : SchemeHomOver t g) :
    schemeHomOverComp ψ' hψ' (schemeHomOverComp ψ hψ x) =
      schemeHomOverComp (ψ' ≫ ψ) (by rw [Category.assoc, hψ, hψ']) x :=
  Subtype.ext (Category.assoc _ _ _).symm

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

theorem act_congr {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {γ γ' : SchemeHomOver t f} {x x' : SchemeHomOver t p} (eγ : γ = γ') (ex : x = x')
    (hd : a.Defined γ x) (hd' : a.Defined γ' x') : a.act γ x hd = a.act γ' x' hd' := by
  subst eγ ex; rfl

end Calculus

section Structure

variable (L : RelativeGroupLaw k f)

theorem comp_mul {T' T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of k)}
    {t' : T' ⟶ Spec (CommRingCat.of k)} (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (x y : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.mul t x y) =
      L.mul t' (schemeHomOverComp ψ hψ x) (schemeHomOverComp ψ hψ y) :=
  L.mul_natural t t' ψ hψ x y

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

theorem exists_kPoint [IsAlgClosed k] {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] {Z : Set X} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX,
      x.1 (IsLocalRing.closedPoint k) ∈ Z := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace tX
  obtain ⟨x, hxZ, hxc⟩ := nonempty_inter_closedPoints hne hZ
  exact ⟨⟨pointOfClosedPoint tX x hxc, pointOfClosedPoint_comp _ _ _⟩,
    by rwa [pointOfClosedPoint_apply]⟩

theorem exists_kPoint_eq [IsAlgClosed k] {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] {s : X} (hs : IsClosed ({s} : Set X)) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX, x.1 (IsLocalRing.closedPoint k) = s :=
  ⟨⟨pointOfClosedPoint tX s hs, pointOfClosedPoint_comp _ _ _⟩, pointOfClosedPoint_apply _ _ _ _⟩

theorem isClosed_kPoint [IsAlgClosed k] {X : Scheme.{u}} (tX : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType tX] (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) tX) :
    IsClosed ({x.1 (IsLocalRing.closedPoint k)} : Set X) :=
  (pointEquivClosedPoint tX ⟨x.1, x.2⟩).2

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

def ltrans (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f (const f g) ⟨𝟙 G, Category.id_comp f⟩).1

theorem kpt_ltrans (g x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x.1 ≫ ltrans L g = (L.mul (𝟙 _) g x).1 := by
  have h : schemeHomOverComp x.1 x.2 (L.mul f (const f g) ⟨𝟙 G, Category.id_comp f⟩) =
      L.mul (𝟙 _) g x := by
    rw [comp_mul, comp_const, const_id]
    congr 1
  exact congrArg Subtype.val h

def rtrans (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) : G ⟶ G :=
  (L.mul f ⟨𝟙 G, Category.id_comp f⟩ (const f g)).1

theorem kpt_rtrans (g x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    x.1 ≫ rtrans L g = (L.mul (𝟙 _) x g).1 := by
  have h : schemeHomOverComp x.1 x.2 (L.mul f ⟨𝟙 G, Category.id_comp f⟩ (const f g)) =
      L.mul (𝟙 _) x g := by
    rw [comp_mul, comp_const, const_id]
    congr 1
  exact congrArg Subtype.val h

end Structure

section Isotropy

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)
  (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)

def idG (f : G ⟶ Spec (CommRingCat.of k)) : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩

def sP : G ⟶ pullback f p := pair (idG f) (const f P₀)

theorem pair_kpt (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pair γ P₀ = γ.1 ≫ sP P₀ := by
  rw [sP, ← pair_comp γ.1 γ.2, comp_const, const_id]
  congr 1

def Ω : G.Opens := sP P₀ ⁻¹ᵁ a.dom

theorem defined_iff_mem (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    a.Defined γ P₀ ↔ γ.1 (IsLocalRing.closedPoint k) ∈ Ω a P₀ := by
  rw [Defined, pair_kpt, range_kPoint, Set.singleton_subset_iff, Scheme.Hom.comp_apply]
  rfl

def γΩ : SchemeHomOver ((Ω a P₀).ι ≫ f) f := ⟨(Ω a P₀).ι, rfl⟩

def PΩ : SchemeHomOver ((Ω a P₀).ι ≫ f) p := const _ P₀

theorem pair_Ω : pair (γΩ a P₀) (PΩ a P₀) = (Ω a P₀).ι ≫ sP P₀ := by
  rw [sP, PΩ, ← pair_comp (Ω a P₀).ι rfl, comp_const]
  rfl

theorem defined_Ω : a.Defined (γΩ a P₀) (PΩ a P₀) := by
  rintro _ ⟨ω, rfl⟩
  rw [pair_Ω, Scheme.Hom.comp_apply]
  exact ω.2

def orb : ((Ω a P₀ : G.Opens) : Scheme.{u}) ⟶ P := (a.act (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀)).1

theorem orb_p : orb a P₀ ≫ p = (Ω a P₀).ι ≫ f := (a.act (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀)).2

def kΩ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    Spec (CommRingCat.of k) ⟶ (Ω a P₀ : G.Opens) :=
  kLift (Ω a P₀) γ.1 ((defined_iff_mem a P₀ γ).mp hγ)

@[reassoc (attr := simp)]
theorem kΩ_ι (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    kΩ a P₀ γ hγ ≫ (Ω a P₀).ι = γ.1 :=
  kLift_ι _ _ _

theorem kΩ_t (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    kΩ a P₀ γ hγ ≫ (Ω a P₀).ι ≫ f = 𝟙 _ := by
  rw [kΩ_ι_assoc]; exact γ.2

theorem act_kpt (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    a.act γ P₀ hγ = schemeHomOverComp (kΩ a P₀ γ hγ) (kΩ_t a P₀ γ hγ)
      (a.act (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀)) := by
  rw [← act_comp a _ _ _ _ _ (defined_comp a _ _ _ _ (defined_Ω a P₀))]
  refine act_congr a (Subtype.ext ?_) ?_ _ _
  · exact (kΩ_ι a P₀ γ hγ).symm
  · rw [PΩ, comp_const, const_id]

theorem act_kpt_coe (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    (a.act γ P₀ hγ).1 = kΩ a P₀ γ hγ ≫ orb a P₀ :=
  congrArg Subtype.val (act_kpt a P₀ γ hγ)

def Hset : Set ↥((Ω a P₀ : G.Opens) : Scheme.{u}) := orb a P₀ ⁻¹' {P₀.1 (IsLocalRing.closedPoint k)}

theorem isClosed_Hset [IsAlgClosed k] [LocallyOfFiniteType p] : IsClosed (Hset a P₀) :=
  (isClosed_kPoint p P₀).preimage (orb a P₀).continuous

theorem mem_Hset_iff [IsAlgClosed k] [LocallyOfFiniteType p]
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ : a.Defined γ P₀) :
    kΩ a P₀ γ hγ (IsLocalRing.closedPoint k) ∈ Hset a P₀ ↔ a.act γ P₀ hγ = P₀ := by
  constructor
  · intro h
    apply Subtype.ext
    refine ext_of_apply_closedPoint_eq p (a.act γ P₀ hγ).2 P₀.2 ?_
    rw [act_kpt_coe, Scheme.Hom.comp_apply]
    exact h
  · intro h
    show orb a P₀ (kΩ a P₀ γ hγ _) = _
    rw [← Scheme.Hom.comp_apply, ← act_kpt_coe, h]

def Himg : Set ↥G := (Ω a P₀).ι '' Hset a P₀

theorem mem_Himg_iff [IsAlgClosed k] [LocallyOfFiniteType p]
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    γ.1 (IsLocalRing.closedPoint k) ∈ Himg a P₀ ↔ ∃ hγ : a.Defined γ P₀, a.act γ P₀ hγ = P₀ := by
  constructor
  · rintro ⟨ω, hω, hωγ⟩
    have hγ : a.Defined γ P₀ := by
      rw [defined_iff_mem, ← hωγ]; exact ω.2
    refine ⟨hγ, (mem_Hset_iff a P₀ γ hγ).mp ?_⟩
    have : kΩ a P₀ γ hγ (IsLocalRing.closedPoint k) = ω := by
      apply (Ω a P₀).ι.isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, kΩ_ι, hωγ]
    rw [this]; exact hω
  · rintro ⟨hγ, h⟩
    exact ⟨_, (mem_Hset_iff a P₀ γ hγ).mpr h, by rw [← Scheme.Hom.comp_apply, kΩ_ι]⟩

theorem one_mem_Himg [IsAlgClosed k] [LocallyOfFiniteType p] (hu : a.UnitActs L)
    (he : a.Defined (L.one (𝟙 _)) P₀) : (L.one (𝟙 _)).1 (IsLocalRing.closedPoint k) ∈ Himg a P₀ :=
  (mem_Himg_iff a P₀ _).mpr ⟨he, hu _ _ he⟩

theorem mul_mem_Himg [IsAlgClosed k] [LocallyOfFiniteType p] (ha : a.Assoc L)
    (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hx : x.1 (IsLocalRing.closedPoint k) ∈ Himg a P₀)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ Himg a P₀) :
    (L.mul (𝟙 _) x y).1 (IsLocalRing.closedPoint k) ∈ Himg a P₀ := by
  obtain ⟨hdx, ex⟩ := (mem_Himg_iff a P₀ x).mp hx
  obtain ⟨hdy, ey⟩ := (mem_Himg_iff a P₀ y).mp hy
  have hdx' : a.Defined x (a.act y P₀ hdy) := by rw [ey]; exact hdx
  obtain ⟨hd₃, e₃⟩ := ha _ x y P₀ hdy hdx'
  refine (mem_Himg_iff a P₀ _).mpr ⟨hd₃, ?_⟩
  rw [← e₃, act_congr a rfl ey hdx' hdx, ex]

theorem isLocallyClosed_Himg [IsAlgClosed k] [LocallyOfFiniteType p] :
    IsLocallyClosed (Himg a P₀) :=
  (isClosed_Hset a P₀).isLocallyClosed.image (Ω a P₀).ι.isOpenEmbedding.isInducing
    (by rw [Scheme.Opens.range_ι]; exact (Ω a P₀).2.isLocallyClosed)

def Zset : Set ↥G := closure (Himg a P₀)

theorem Zset_eq [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f] :
    Zset a P₀ = closure (Himg a P₀ ∩ closedPoints G) := by
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f
  exact (JacobsonSpace.closure_inter_closedPoints_eq_closure (isLocallyClosed_Himg a P₀)).symm

theorem ltrans_image_Zset [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (ha : a.Assoc L) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hx : x.1 (IsLocalRing.closedPoint k) ∈ Himg a P₀) :
    ltrans L x '' Zset a P₀ ⊆ Zset a P₀ := by
  rw [Zset_eq]
  refine (image_closure_subset_closure_image (ltrans L x).continuous).trans (closure_mono ?_)
  rintro _ ⟨s, ⟨hs, hsc⟩, rfl⟩
  obtain ⟨y, rfl⟩ := exists_kPoint_eq f hsc
  refine ⟨?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, kpt_ltrans]
    exact mul_mem_Himg L a P₀ ha x y hx hs
  · rw [← Scheme.Hom.comp_apply, kpt_ltrans]
    exact isClosed_kPoint f _

theorem rtrans_image_Zset [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (ha : a.Assoc L) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ Himg a P₀) :
    rtrans L y '' Zset a P₀ ⊆ Zset a P₀ := by
  rw [Zset_eq]
  refine (image_closure_subset_closure_image (rtrans L y).continuous).trans (closure_mono ?_)
  rintro _ ⟨s, ⟨hs, hsc⟩, rfl⟩
  obtain ⟨x, rfl⟩ := exists_kPoint_eq f hsc
  refine ⟨?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, kpt_rtrans]
    exact mul_mem_Himg L a P₀ ha x y hs hy
  · rw [← Scheme.Hom.comp_apply, kpt_rtrans]
    exact isClosed_kPoint f _

theorem mul_mem_Zset [IsAlgClosed k] [LocallyOfFiniteType p] [LocallyOfFiniteType f]
    (ha : a.Assoc L) (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f)
    (hx : x.1 (IsLocalRing.closedPoint k) ∈ Zset a P₀)
    (hy : y.1 (IsLocalRing.closedPoint k) ∈ Zset a P₀) :
    (L.mul (𝟙 _) x y).1 (IsLocalRing.closedPoint k) ∈ Zset a P₀ := by

  have hsub : closure (Himg a P₀ ∩ closedPoints G) ⊆ ltrans L x ⁻¹' Zset a P₀ := by
    refine closure_minimal ?_ (isClosed_closure.preimage (ltrans L x).continuous)
    rintro s ⟨hs, hsc⟩
    obtain ⟨y', rfl⟩ := exists_kPoint_eq f hsc
    show ltrans L x _ ∈ Zset a P₀
    rw [← Scheme.Hom.comp_apply, kpt_ltrans, ← kpt_rtrans, Scheme.Hom.comp_apply]
    exact rtrans_image_Zset L a P₀ ha y' hs ⟨_, hx, rfl⟩
  have := hsub (by rw [← Zset_eq]; exact hy)
  rwa [Set.mem_preimage, ← Scheme.Hom.comp_apply, kpt_ltrans] at this

theorem not_mem_Zset [IsAlgClosed k] [LocallyOfFiniteType p]
    (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀)
    (hne : a.act γ₀ P₀ hγ₀ ≠ P₀) : γ₀.1 (IsLocalRing.closedPoint k) ∉ Zset a P₀ := by
  intro h
  apply hne
  rw [← mem_Hset_iff, ← (isClosed_Hset a P₀).closure_eq,
    (Ω a P₀).ι.isOpenEmbedding.isEmbedding.closure_eq_preimage_closure_image, Set.mem_preimage,
    ← Scheme.Hom.comp_apply, kΩ_ι]
  exact h

end Isotropy

section Assembly

theorem one_le_of_bounds {g : ℕ} {dZ dcl dW : WithBot ℕ∞} (h0 : 0 ≤ dZ)
    (hWg : dW + 1 ≤ (g : WithBot ℕ∞)) (hcl : dcl ≤ dW) (hdim : (g : WithBot ℕ∞) ≤ dZ + dcl) :
    1 ≤ dZ := by
  induction dZ using WithBot.recBotCoe with
  | bot => exact absurd (le_bot_iff.mp h0) WithBot.coe_ne_bot
  | coe n =>
    induction dcl using WithBot.recBotCoe with
    | bot => rw [WithBot.add_bot] at hdim; exact absurd (le_bot_iff.mp hdim) WithBot.coe_ne_bot
    | coe c =>
      induction dW using WithBot.recBotCoe with
      | bot => exact absurd (le_bot_iff.mp hcl) WithBot.coe_ne_bot
      | coe d =>
        have hWg' : d + 1 ≤ (g : ℕ∞) := by exact_mod_cast hWg
        have hcl' : c ≤ d := by exact_mod_cast hcl
        have hdim' : (g : ℕ∞) ≤ n + c := by exact_mod_cast hdim
        suffices h : (1 : ℕ∞) ≤ n by exact_mod_cast h
        induction n using ENat.recTopCoe with
        | top => exact le_top
        | coe n =>
          induction d using ENat.recTopCoe with
          | top =>
            rw [top_add] at hWg'
            exact absurd hWg' (by simp)
          | coe d =>
            induction c using ENat.recTopCoe with
            | top => exact absurd hcl' (by simp)
            | coe c =>
              have h1 : d + 1 ≤ g := by exact_mod_cast hWg'
              have h2 : c ≤ d := by exact_mod_cast hcl'
              have h3 : g ≤ n + c := by exact_mod_cast hdim'
              have : 1 ≤ n := by omega
              exact_mod_cast this

variable (L : RelativeGroupLaw k f) (a : PartialAction k f p)
  (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)

theorem range_orb_subset (W : Set ↥P) (hst : a.Stable W)
    (hP₀ : P₀.1 (IsLocalRing.closedPoint k) ∈ W) : Set.range (orb a P₀) ⊆ W := by
  rintro _ ⟨ω, rfl⟩
  have h1 : a.liftDom (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀) ≫ a.dom.ι ≫ pullback.snd f p =
      ((Ω a P₀).ι ≫ f) ≫ P₀.1 := by
    rw [← Category.assoc, liftDom_ι, pair, pullback.lift_snd]; rfl
  have h2 : pullback.snd f p (a.dom.ι (a.liftDom (γΩ a P₀) (PΩ a P₀) (defined_Ω a P₀) ω)) ∈ W := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, h1, Scheme.Hom.comp_apply]
    convert hP₀ using 2
    exact Subsingleton.elim _ _
  have := hst _ h2
  rwa [← Scheme.Hom.comp_apply] at this

theorem apply_one_eq {H : Scheme.{u}} (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f))
    (hhom : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
      NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
        L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
          (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) :
    i ((LH.one (𝟙 _)).1 (IsLocalRing.closedPoint k)) = (L.one (𝟙 _)).1 (IsLocalRing.closedPoint k) := by
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  set j := NeronModelInfra.schemeHomOverComp (LH.one (𝟙 _)) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f)
  have h := hhom (𝟙 _) (LH.one (𝟙 _)) (LH.one (𝟙 _))
  rw [LH.one_mul] at h
  have hj : j = L.one (𝟙 _) := by
    have h' : j * 1 = j * j := (mul_one j).trans h
    exact (mul_left_cancel h').symm
  have := congrArg (fun z : SchemeHomOver (𝟙 _) f => z.1 (IsLocalRing.closedPoint k)) hj
  simpa [j, NeronModelInfra.schemeHomOverComp_coe, Scheme.Hom.comp_apply] using this

theorem main (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (W : Set ↥P) (hW : IsClosed W) (hWg : topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞))
    (hst : a.Stable W) (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hP₀ : P₀.1 (IsLocalRing.closedPoint k) ∈ W) (he : a.Defined (L.one (𝟙 _)) P₀)
    (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀)
    (hne : a.act γ₀ P₀ hγ₀ ≠ P₀) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      Set.range i ≠ Set.univ ∧
      1 ≤ topologicalKrullDim
        ↥(connectedComponent ((LH.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k))) := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth g f

  obtain ⟨H, i, LH, hci, -, hrange, hhom⟩ :=
    RelativeGroupLaw.exists_isClosedImmersion_isReduced_range_eq_of_isClosed_of_mul_mem k f L
      (Zset a P₀) isClosed_closure (subset_closure (one_mem_Himg L a P₀ hu he))
      (fun x y hx hy => mul_mem_Zset L a P₀ ha x y hx hy)
  refine ⟨H, i, LH, hci, hhom, ?_, ?_⟩
  ·
    intro huniv
    have hmem : γ₀.1 (IsLocalRing.closedPoint k) ∈ Set.range i := huniv ▸ Set.mem_univ _
    rw [hrange] at hmem
    exact not_mem_Zset a P₀ γ₀ hγ₀ hne hmem
  ·
    haveI : GeometricallyIrreducible f := geometricallyIrreducible L
    haveI : IrreducibleSpace G := GeometricallyIrreducible.irreducibleSpace_of_subsingleton f
    have heΩ : (L.one (𝟙 _)).1 (IsLocalRing.closedPoint k) ∈ Ω a P₀ := (defined_iff_mem a P₀ _).mp he
    haveI : Nonempty ((Ω a P₀ : G.Opens) : Scheme.{u}) := ⟨⟨_, heΩ⟩⟩
    haveI : IrreducibleSpace ((Ω a P₀ : G.Opens) : Scheme.{u}) :=
      (Ω a P₀).ι.isOpenEmbedding.irreducibleSpace

    have horb : orb a P₀ (kΩ a P₀ (L.one _) he (IsLocalRing.closedPoint k)) =
        P₀.1 (IsLocalRing.closedPoint k) := (mem_Hset_iff a P₀ _ he).mpr (hu _ _ he)
    obtain ⟨Z₁, heZ₁, hZ₁sub, hZ₁irr, -, hdim⟩ :=
      AlgebraicGeometry.exists_isIrreducible_topologicalKrullDim_le_add_of_apply_eq_of_isClosed_singleton
        ((Ω a P₀).ι ≫ f) p (orb a P₀) (orb_p a P₀) (isClosed_kPoint p P₀) horb

    haveI : SmoothOfRelativeDimension g ((Ω a P₀).ι ≫ f) := by
      have : SmoothOfRelativeDimension (0 + g) ((Ω a P₀).ι ≫ f) := inferInstance
      rwa [zero_add] at this
    have hΩ : topologicalKrullDim ↥((Ω a P₀ : G.Opens) : Scheme.{u}) = g :=
      le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le ((Ω a P₀).ι ≫ f) g)
        (SmoothOfRelativeDimension.le_topologicalKrullDim ((Ω a P₀).ι ≫ f) g)

    have hcl : topologicalKrullDim ↥(closure (Set.range (orb a P₀))) ≤ topologicalKrullDim ↥W :=
      Topology.IsInducing.topologicalKrullDim_le
        (IsEmbedding.inclusion (closure_minimal (range_orb_subset a P₀ W hst hP₀) hW)).isInducing
    have h0 : 0 ≤ topologicalKrullDim ↥Z₁ := by
      haveI : IrreducibleSpace ↥Z₁ := Subtype.irreducibleSpace hZ₁irr
      haveI : Nonempty (TopologicalSpace.IrreducibleCloseds ↥Z₁) :=
        ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩⟩
      exact Order.krullDim_nonneg
    have h1 : 1 ≤ topologicalKrullDim ↥Z₁ := one_le_of_bounds h0 hWg hcl (hΩ ▸ hdim)

    let T₁ : Set ↥G := (Ω a P₀).ι '' Z₁
    have hT₁ : T₁ ⊆ Set.range i := by
      rw [hrange]
      rintro _ ⟨z, hz, rfl⟩
      exact subset_closure ⟨z, hZ₁sub hz, rfl⟩
    have hT₁irr : IsIrreducible T₁ := hZ₁irr.image _ (Ω a P₀).ι.continuous.continuousOn
    let φ₁ : ↥Z₁ → ↥T₁ := Set.codRestrict ((Ω a P₀).ι ∘ Subtype.val) T₁ (fun z => ⟨z.1, z.2, rfl⟩)
    have hφ₁ : IsInducing φ₁ :=
      ((Ω a P₀).ι.isOpenEmbedding.isInducing.comp IsInducing.subtypeVal).codRestrict _
    have hi := i.isClosedEmbedding
    let φ₂ : ↥T₁ → ↥H := fun t => hi.isEmbedding.toHomeomorph.symm ⟨t.1, hT₁ t.2⟩
    have hφ₂ : IsInducing φ₂ :=
      hi.isEmbedding.toHomeomorph.symm.isInducing.comp (IsEmbedding.inclusion hT₁).isInducing
    have hu₁ : φ₂ ⟨(L.one (𝟙 _)).1 (IsLocalRing.closedPoint k),
        ⟨_, heZ₁, by rw [← Scheme.Hom.comp_apply, kΩ_ι]⟩⟩ =
        (LH.one (𝟙 _)).1 (IsLocalRing.closedPoint k) := by
      show hi.isEmbedding.toHomeomorph.symm _ = _
      convert hi.isEmbedding.toHomeomorph_symm_apply ((LH.one (𝟙 _)).1 (IsLocalRing.closedPoint k))
      exact (apply_one_eq L i LH hhom).symm
    haveI : ConnectedSpace ↥T₁ := isConnected_iff_connectedSpace.mp hT₁irr.isConnected
    have hsub : Set.range φ₂ ⊆
        connectedComponent ((LH.one (𝟙 _)).1 (IsLocalRing.closedPoint k)) :=
      (isPreconnected_range hφ₂.continuous).subset_connectedComponent (hu₁ ▸ ⟨_, rfl⟩)
    have hψ : IsInducing (Set.codRestrict φ₂ _ (fun t => hsub ⟨t, rfl⟩)) := hφ₂.codRestrict _
    exact h1.trans ((Topology.IsInducing.topologicalKrullDim_le hφ₁).trans
      (Topology.IsInducing.topologicalKrullDim_le hψ))

end Assembly

end IsotropyB3
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian.PartialAction.IsotropyB3"

end PartialAction
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian.PartialAction.IsotropyB3 P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian.PartialAction"

end GoodReductionJacobian
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian.PartialAction.IsotropyB3 P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian.PartialAction.IsotropyB3 P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian"

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne.GoodReductionJacobian"

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G]
    (L : RelativeGroupLaw k f) (g : ℕ) [SmoothOfRelativeDimension g f]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L)
    (W : Set ↥P) (hW : IsClosed W) (hWg : topologicalKrullDim ↥W + 1 ≤ (g : WithBot ℕ∞))
    (hst : a.Stable W)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (hP₀ : P₀.1 (IsLocalRing.closedPoint k) ∈ W)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (γ₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hγ₀ : a.Defined γ₀ P₀)
    (hne : a.act γ₀ P₀ hγ₀ ≠ P₀) :
    ∃ (H : Scheme.{u}) (i : H ⟶ G) (LH : RelativeGroupLaw k (i ≫ f)),
      IsClosedImmersion i ∧
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t (i ≫ f)),
        NeronModelInfra.schemeHomOverComp (LH.mul t x y) (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f) =
          L.mul t (NeronModelInfra.schemeHomOverComp x (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))
            (NeronModelInfra.schemeHomOverComp y (⟨i, rfl⟩ : SchemeHomOver (i ≫ f) f))) ∧
      Set.range i ≠ Set.univ ∧
      1 ≤ topologicalKrullDim
        ↥(connectedComponent ((LH.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k))) :=
  GoodReductionJacobian.PartialAction.IsotropyB3.main k f L g p a hu ha W hW hWg hst P₀ hP₀ he γ₀ hγ₀ hne

end S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_exists_isClosedImmersion_range_ne_univ_of_act_ne (solution)
