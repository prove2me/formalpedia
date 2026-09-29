-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e18d8e75-d2f8-5761-890d-ef2a59af2e66

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_hom_comp_eq_and_comp_hom_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian TopologicalSpace Topology"

universe u

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "pointGroup mul_inv_cancel mul_assoc mul_one one mul_natural inv one_mul inv_mul_cancel mul exists_iso_hom_comp_eq_and_comp_hom_eq_mul"
namespace ClosedImage
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

section Topology

variable {X : Type*} [TopologicalSpace X]

theorem denseOpen_union {s t U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUs : U ∩ closure s ⊆ s) (hs : closure s ⊆ closure (U ∩ closure s))
    (hVt : V ∩ closure t ⊆ t) (ht : closure t ⊆ closure (V ∩ closure t)) :
    ∃ W : Set X, IsOpen W ∧ W ∩ closure (s ∪ t) ⊆ s ∪ t ∧
      closure (s ∪ t) ⊆ closure (W ∩ closure (s ∪ t)) := by
  refine ⟨(U ∩ (closure t)ᶜ) ∪ (V ∩ (closure s)ᶜ) ∪ (U ∩ V),
    ((hU.inter isClosed_closure.isOpen_compl).union
      (hV.inter isClosed_closure.isOpen_compl)).union (hU.inter hV), ?_, ?_⟩
  · rintro p ⟨((⟨hpU, hpt⟩ | ⟨hpV, hps⟩) | ⟨hpU, hpV⟩), hpc⟩ <;>
      rw [closure_union] at hpc <;> rcases hpc with (hcs | hct)
    · exact Or.inl (hUs ⟨hpU, hcs⟩)
    · exact (hpt hct).elim
    · exact (hps hcs).elim
    · exact Or.inr (hVt ⟨hpV, hct⟩)
    · exact Or.inl (hUs ⟨hpU, hcs⟩)
    · exact Or.inr (hVt ⟨hpV, hct⟩)
  ·
    have aux : ∀ {s' t' U' V' : Set X} (W : Set X), IsOpen U' →
        closure s' ⊆ closure (U' ∩ closure s') → closure t' ⊆ closure (V' ∩ closure t') →
        U' ∩ (closure t')ᶜ ⊆ W → U' ∩ V' ⊆ W →
        closure s' ⊆ closure (W ∩ closure (s' ∪ t')) := by
      intro s' t' U' V' W hU' hs' ht' h1 h2
      refine hs'.trans (closure_minimal ?_ isClosed_closure)
      rintro q ⟨hqU, hqs⟩
      by_cases hqt : q ∈ closure t'
      · have hq : q ∈ closure (U' ∩ (V' ∩ closure t')) :=
          hU'.inter_closure ⟨hqU, ht' hqt⟩
        refine closure_mono ?_ hq
        rintro z ⟨hzU, hzV, hzt⟩
        exact ⟨h2 ⟨hzU, hzV⟩, closure_mono Set.subset_union_right hzt⟩
      · exact subset_closure ⟨h1 ⟨hqU, hqt⟩, closure_mono Set.subset_union_left hqs⟩
    rw [closure_union]
    refine Set.union_subset ?_ ?_
    · rw [← closure_union]
      exact aux _ hU hs ht (fun z hz => Or.inl (Or.inl hz)) (fun z hz => Or.inr hz)
    · rw [← closure_union, Set.union_comm s t]
      exact aux _ hV ht hs (fun z hz => Or.inl (Or.inr hz)) (fun z hz => Or.inr ⟨hz.2, hz.1⟩)

theorem exists_isOpen_inter_closure_subset_of_isConstructible [CompactSpace X]
    [QuasiSeparatedSpace X] {ι : Type*} [Nonempty ι] (b : ι → Set X)
    (hb : IsTopologicalBasis (Set.range b)) (hbc : ∀ i, IsCompact (b i))
    {s : Set X} (hs : IsConstructible s) :
    ∃ U : Set X, IsOpen U ∧ U ∩ closure s ⊆ s ∧ closure s ⊆ closure (U ∩ closure s) := by
  induction s, hs using IsConstructible.induction_of_isTopologicalBasis b hb hbc with
  | sdiff i t ht =>
    refine ⟨b i, hb.isOpen ⟨i, rfl⟩, ?_, ?_⟩
    · rintro p ⟨hpi, hpc⟩
      refine ⟨hpi, ?_⟩
      have hcl : IsClosed (⋃ j ∈ t, b j)ᶜ :=
        (isOpen_biUnion fun j _ => hb.isOpen ⟨j, rfl⟩).isClosed_compl
      have : closure (b i \ ⋃ j ∈ t, b j) ⊆ (⋃ j ∈ t, b j)ᶜ :=
        closure_minimal (fun z hz => hz.2) hcl
      exact this hpc
    · exact closure_mono fun z hz => ⟨hz.1, subset_closure hz⟩
  | union s hs t ht Hs Ht =>
    obtain ⟨U, hU, hUs, hs'⟩ := Hs
    obtain ⟨V, hV, hVt, ht'⟩ := Ht
    exact denseOpen_union hU hV hUs hs' hVt ht'

theorem image_eq_of_image_subset [NoetherianSpace X] (r : X ≃ₜ X) {Z : Set X}
    (hZ : IsClosed Z) (h : r '' Z ⊆ Z) : r '' Z = Z := by
  by_contra hne
  let 𝒞 : Set (Closeds X) := {C | r '' (C : Set X) ⊂ C}
  have hZ𝒞 : (⟨Z, hZ⟩ : Closeds X) ∈ 𝒞 := HasSubset.Subset.ssubset_of_ne h hne
  obtain ⟨C₀, hC₀, hmin⟩ := (wellFounded_lt (α := Closeds X)).has_min 𝒞 ⟨_, hZ𝒞⟩
  have hC₁ : (⟨r '' (C₀ : Set X), r.isClosedMap _ C₀.2⟩ : Closeds X) ∈ 𝒞 := by
    change r '' (r '' (C₀ : Set X)) ⊂ r '' (C₀ : Set X)
    refine ⟨Set.image_mono hC₀.1, fun hle => hC₀.2 ?_⟩
    exact (Set.image_subset_image_iff r.injective).mp hle
  refine hmin _ hC₁ ?_
  change (r '' (C₀ : Set X)) ⊂ (C₀ : Set X) at hC₀
  exact hC₀

end Topology

section Points

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
  (p : X ⟶ Spec (CommRingCat.of k))

abbrev pt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) : X :=
  x.1 (IsLocalRing.closedPoint k)

variable [LocallyOfFiniteType p]

include p in
omit [IsAlgClosed k] in
private theorem _root_.GoodReductionJacobian.RelativeGroupLaw.ClosedImage.jacobsonSpace : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace p

p2m_export "GoodReductionJacobian.RelativeGroupLaw.ClosedImage" "jacobsonSpace"
theorem isClosed_pt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) : IsClosed {pt p x} :=
  ((pointEquivClosedPoint p) ⟨x.1, x.2⟩).2

theorem exists_pt_eq_of_isClosed {c : X} (hc : IsClosed {c}) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p, pt p x = c := by
  refine ⟨⟨((pointEquivClosedPoint p).symm ⟨c, hc⟩).1,
    ((pointEquivClosedPoint p).symm ⟨c, hc⟩).2⟩, ?_⟩
  simp [pt]

theorem exists_pt_mem_of_isLocallyClosed {C : Set X} (hC : IsLocallyClosed C)
    (hne : C.Nonempty) :
    ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p, pt p x ∈ C := by
  haveI := jacobsonSpace p
  obtain ⟨c, hcC, hc⟩ := nonempty_inter_closedPoints hne hC
  obtain ⟨x, rfl⟩ := exists_pt_eq_of_isClosed p hc
  exact ⟨x, hcC⟩

theorem dense_range_pt :
    Dense (Set.range (pt p : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p → X)) := by
  haveI := jacobsonSpace p
  have h : closedPoints X ⊆ Set.range (pt p) := by
    intro c hc
    obtain ⟨x, rfl⟩ := exists_pt_eq_of_isClosed p hc
    exact ⟨x, rfl⟩
  exact Dense.mono h (dense_iff_closure_eq.mpr (closure_closedPoints (X := X)))

end Points

section Translations

variable {k : Type u} [Field k] {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)}

def opLaw (M : RelativeGroupLaw k g) : RelativeGroupLaw k g where
  mul t x y := M.mul t y x
  one t := M.one t
  inv t x := M.inv t x
  mul_assoc t x y z := (M.mul_assoc t z y x).symm
  one_mul t x := M.mul_one t x
  mul_one t x := M.one_mul t x
  inv_mul_cancel t x := M.mul_inv_cancel t x
  mul_natural t t' ψ hψ x y := M.mul_natural t t' ψ hψ y x

@[scoped simp] theorem opLaw_mul (M : RelativeGroupLaw k g) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t g) :
    (opLaw M).mul t x y = M.mul t y x := rfl

variable (M : RelativeGroupLaw k g) (d : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g)

def transIso : H ≅ H :=
  (RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul k M d).choose

theorem comp_transIso_hom {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k))
    (x : SchemeHomOver t g) :
    x.1 ≫ (transIso M d).hom =
      (M.mul t x (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) d)).1 :=
  (RelativeGroupLaw.exists_iso_hom_comp_eq_and_comp_hom_eq_mul k M d).choose_spec.2.2.1 t x

theorem schemeHomOverComp_id_eq :
    GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k)))
      (Category.comp_id _) d = d :=
  Subtype.ext (Category.id_comp _)

theorem transIso_hom_pt (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g) :
    (transIso M d).hom (pt g x) = pt g (M.mul (𝟙 _) x d) := by
  change (x.1 ≫ (transIso M d).hom) (IsLocalRing.closedPoint k) = _
  rw [comp_transIso_hom, schemeHomOverComp_id_eq]

theorem transIso_hom_eq :
    (transIso M d).hom =
      (M.mul g (⟨𝟙 H, Category.id_comp g⟩ : SchemeHomOver g g)
        (GoodReductionJacobian.schemeHomOverComp g (Category.comp_id g) d)).1 := by
  rw [← comp_transIso_hom M d g ⟨𝟙 H, Category.id_comp g⟩]
  exact (Category.id_comp _).symm

variable {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} (L : RelativeGroupLaw k f)
  (φ : SchemeHomOver f g)
  (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
      M.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))

include hφ in

theorem hom_opLaw {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f) :
    NeronModelInfra.schemeHomOverComp ((opLaw L).mul t x y) φ =
      (opLaw M).mul t (NeronModelInfra.schemeHomOverComp x φ)
        (NeronModelInfra.schemeHomOverComp y φ) :=
  hφ t y x

include hφ in

theorem transIso_hom_comp (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    (transIso L a).hom ≫ φ.1 = φ.1 ≫ (transIso M (NeronModelInfra.schemeHomOverComp a φ)).hom := by
  have h1 : (transIso L a).hom ≫ φ.1 =
      (NeronModelInfra.schemeHomOverComp
        (L.mul f (⟨𝟙 G, Category.id_comp f⟩ : SchemeHomOver f f)
          (GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) a)) φ).1 := by
    rw [transIso_hom_eq]; rfl
  have h2 : NeronModelInfra.schemeHomOverComp (⟨𝟙 G, Category.id_comp f⟩ : SchemeHomOver f f) φ
      = φ := Subtype.ext (Category.id_comp _)
  have h3 : NeronModelInfra.schemeHomOverComp
      (GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) a) φ =
      GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f)
        (NeronModelInfra.schemeHomOverComp a φ) := Subtype.ext (Category.assoc _ _ _)
  rw [h1, hφ, comp_transIso_hom M _ f φ, h2, h3]

include hφ in
theorem apply_transIso_hom (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (z : G) :
    φ.1 ((transIso L a).hom z) = (transIso M (NeronModelInfra.schemeHomOverComp a φ)).hom (φ.1 z) := by
  rw [← Scheme.Hom.comp_apply, transIso_hom_comp M L φ hφ a, Scheme.Hom.comp_apply]

include hφ in

theorem image_transIso_hom_range (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    (transIso M (NeronModelInfra.schemeHomOverComp a φ)).hom '' Set.range φ.1 = Set.range φ.1 := by
  apply subset_antisymm
  · rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    exact ⟨(transIso L a).hom z, apply_transIso_hom M L φ hφ a z⟩
  · rintro _ ⟨z, rfl⟩
    refine ⟨φ.1 ((transIso L a).inv z), ⟨_, rfl⟩, ?_⟩
    have hz : (transIso L a).hom ((transIso L a).inv z) = z := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    rw [← apply_transIso_hom M L φ hφ a, hz]

theorem pt_schemeHomOverComp (a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) :
    pt g (NeronModelInfra.schemeHomOverComp a φ) = φ.1 (pt f a) := rfl

end Translations

section Homogeneity

variable {k : Type u} [Field k] [IsAlgClosed k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] (L : RelativeGroupLaw k f)

theorem iUnion_image_transIso_hom_eq_univ {V : Set G} (hV : IsOpen V) (hne : V.Nonempty) :
    ⋃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, (transIso L a).hom '' V = Set.univ := by
  by_contra hne'
  set W : Set G := ⋃ a : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, (transIso L a).hom '' V
  have hW : IsOpen W :=
    isOpen_iUnion fun a => (Scheme.homeoOfIso (transIso L a)).isOpenMap V hV
  have hC : (Wᶜ).Nonempty := Set.nonempty_compl.mpr hne'
  obtain ⟨c₀, hc₀⟩ := exists_pt_mem_of_isLocallyClosed f hW.isClosed_compl.isLocallyClosed hC
  obtain ⟨v₀, hv₀⟩ := exists_pt_mem_of_isLocallyClosed f hV.isLocallyClosed hne
  apply hc₀
  letI := L.pointGroup (𝟙 (Spec (CommRingCat.of k)))
  refine Set.mem_iUnion.mpr ⟨v₀⁻¹ * c₀, pt f v₀, hv₀, ?_⟩
  rw [transIso_hom_pt]
  change pt f (v₀ * (v₀⁻¹ * c₀)) = pt f c₀
  rw [mul_inv_cancel_left]

end Homogeneity

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f]
  {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] [QuasiCompact g]

theorem isClosed_range (L : RelativeGroupLaw k f) (M : RelativeGroupLaw k g)
    (φ : SchemeHomOver f g)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    IsClosed (Set.range φ.1) := by
  classical

  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  haveI : IsNoetherian G := ⟨⟩
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian g
  haveI : CompactSpace H := QuasiCompact.compactSpace_of_compactSpace g
  haveI : IsNoetherian H := ⟨⟩
  haveI : LocallyOfFiniteType φ.1 := by
    have : LocallyOfFiniteType (φ.1 ≫ g) := by rw [φ.2]; infer_instance
    exact locallyOfFiniteType_of_comp φ.1 g

  set S : Set H := Set.range φ.1 with hS
  set Z : Set H := closure S with hZ
  let cφ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) g :=
    fun a => NeronModelInfra.schemeHomOverComp a φ

  have hSc : IsConstructible S := by
    have := φ.1.isConstructible_image IsConstructible.univ
    rwa [Set.image_univ] at this

  obtain ⟨U, hUo, hUS, hZU⟩ :
      ∃ U : Set H, IsOpen U ∧ U ∩ Z ⊆ S ∧ Z ⊆ closure (U ∩ Z) := by
    haveI : Nonempty H.affineOpens := ⟨⟨⊥, isAffineOpen_bot H⟩⟩
    refine exists_isOpen_inter_closure_subset_of_isConstructible
      (fun V : H.affineOpens => ((V : H.Opens) : Set H)) ?_ (fun V => V.2.isCompact) hSc
    have hb := H.isBasis_affineOpens
    rw [Opens.IsBasis, Set.image_eq_range] at hb
    convert hb using 2

  have hrS : ∀ a, (transIso M (cφ a)).hom '' S = S := image_transIso_hom_range M L φ hφ
  have hrZ : ∀ a, (transIso M (cφ a)).hom '' Z = Z := fun a => by
    change (Scheme.homeoOfIso (transIso M (cφ a))) '' closure S = closure S
    rw [Homeomorph.image_closure]
    exact congrArg closure (hrS a)

  let O : Set H := ⋃ a, (transIso M (cφ a)).hom '' U
  have hO : IsOpen O :=
    isOpen_iUnion fun a => (Scheme.homeoOfIso (transIso M (cφ a))).isOpenMap U hUo
  have hSO : S = O ∩ Z := by
    apply subset_antisymm
    · rintro _ ⟨x', rfl⟩
      refine ⟨?_, subset_closure ⟨x', rfl⟩⟩
      have hZne : (U ∩ Z).Nonempty := by
        by_contra h0
        rw [Set.not_nonempty_iff_eq_empty] at h0
        have := hZU (subset_closure ⟨x', rfl⟩)
        rw [h0, closure_empty] at this
        exact this
      obtain ⟨u, huU, huZ⟩ := hZne
      obtain ⟨x'', hx''⟩ := hUS ⟨huU, huZ⟩
      have hV : IsOpen (φ.1 ⁻¹' U) := hUo.preimage φ.1.continuous
      have hcov := iUnion_image_transIso_hom_eq_univ L hV ⟨x'', show φ.1 x'' ∈ U from hx'' ▸ huU⟩
      have hx' : x' ∈ ⋃ a, (transIso L a).hom '' (φ.1 ⁻¹' U) := by
        rw [hcov]; trivial
      obtain ⟨a, v, hv, rfl⟩ := Set.mem_iUnion.mp hx'
      refine Set.mem_iUnion.mpr ⟨a, φ.1 v, hv, ?_⟩
      rw [apply_transIso_hom M L φ hφ]
    · rintro p ⟨hpO, hpZ⟩
      obtain ⟨a, u', hu', rfl⟩ := Set.mem_iUnion.mp hpO
      have hu'Z : u' ∈ Z := by
        rw [← hrZ a] at hpZ
        obtain ⟨z, hz, hzu⟩ := hpZ
        rwa [← (Scheme.homeoOfIso (transIso M (cφ a))).injective hzu]
      rw [← hrS a]
      exact ⟨u', hUS ⟨hu', hu'Z⟩, rfl⟩

  suffices hZS : Z ⊆ S by
    have : S = Z := subset_antisymm subset_closure hZS
    rw [this]
    exact isClosed_closure
  by_contra hT
  obtain ⟨p₁, hp₁Z, hp₁S⟩ := Set.not_subset.mp hT
  have hTne : (Z \ S).Nonempty := ⟨p₁, hp₁Z, hp₁S⟩
  have hTc : IsClosed (Z \ S) := by
    have : Z \ S = Z \ O := by rw [hSO, Set.diff_inter_self_eq_diff]
    rw [this]
    exact isClosed_closure.sdiff hO
  obtain ⟨t₀, ht₀⟩ := exists_pt_mem_of_isLocallyClosed g hTc.isLocallyClosed hTne

  have hlS : ∀ a, (transIso (opLaw M) (cφ a)).hom '' S = S :=
    image_transIso_hom_range (opLaw M) (opLaw L) φ (fun t x y => hom_opLaw M L φ hφ t x y)
  have hlZ : ∀ a, (transIso (opLaw M) (cφ a)).hom '' Z = Z := fun a => by
    change (Scheme.homeoOfIso (transIso (opLaw M) (cφ a))) '' closure S = closure S
    rw [Homeomorph.image_closure]
    exact congrArg closure (hlS a)
  have hlT : ∀ a, (transIso (opLaw M) (cφ a)).hom '' (Z \ S) = Z \ S := fun a => by
    change (Scheme.homeoOfIso (transIso (opLaw M) (cφ a))) '' (Z \ S) = Z \ S
    rw [Set.image_diff (Scheme.homeoOfIso _).injective]
    exact congrArg₂ (· \ ·) (hlZ a) (hlS a)

  set r : H ≅ H := transIso M t₀ with hr
  have hkey : ∀ a, r.hom (pt g (cφ a)) ∈ Z \ S := fun a => by
    have h1 : r.hom (pt g (cφ a)) = (transIso (opLaw M) (cφ a)).hom (pt g t₀) := by
      rw [transIso_hom_pt, transIso_hom_pt]; rfl
    rw [h1, ← hlT a]
    exact ⟨_, ht₀, rfl⟩
  have hK : S ⊆ closure (Set.range fun a => pt g (cφ a)) := by
    rintro _ ⟨x', rfl⟩
    have hx' : x' ∈ closure (Set.range (pt f)) := by
      rw [(dense_range_pt f).closure_eq]; trivial
    have := image_closure_subset_closure_image φ.1.continuous ⟨x', hx', rfl⟩
    refine closure_mono ?_ this
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩
  have hrS' : r.hom '' S ⊆ Z \ S := by
    refine (Set.image_mono hK).trans ?_
    refine (image_closure_subset_closure_image r.hom.continuous).trans ?_
    refine closure_minimal ?_ hTc
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    exact hkey a
  have hrZ' : r.hom '' Z ⊆ Z := by
    change r.hom '' closure S ⊆ closure S
    refine (image_closure_subset_closure_image r.hom.continuous).trans ?_
    exact closure_minimal (hrS'.trans Set.diff_subset) isClosed_closure

  have hrZeq : r.hom '' Z = Z :=
    image_eq_of_image_subset (Scheme.homeoOfIso r) isClosed_closure hrZ'

  have hrSeq : r.hom '' S = r.hom '' O ∩ Z := by
    conv_lhs => rw [hSO]
    change (Scheme.homeoOfIso r) '' (O ∩ Z) = (Scheme.homeoOfIso r) '' O ∩ Z
    rw [Set.image_inter (Scheme.homeoOfIso r).injective]
    exact congrArg _ hrZeq
  have hne1 : (closure S ∩ r.hom '' O).Nonempty := by
    have hmem : r.hom (φ.1 (pt f (L.one _))) ∈ r.hom '' S := ⟨_, ⟨_, rfl⟩, rfl⟩
    rw [hrSeq] at hmem
    exact ⟨_, hmem.2, hmem.1⟩
  have hrO : IsOpen (r.hom '' O) := (Scheme.homeoOfIso r).isOpenMap O hO
  rw [closure_inter_open_nonempty_iff hrO] at hne1
  obtain ⟨q, hqS, hqO⟩ := hne1
  have hq : q ∈ Z \ S := hrS' (hrSeq ▸ ⟨hqO, subset_closure hqS⟩)
  exact hq.2 hqS

end Main

end GoodReductionJacobian.RelativeGroupLaw.ClosedImage
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian.RelativeGroupLaw.ClosedImage"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian.RelativeGroupLaw"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian.RelativeGroupLaw P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed.GoodReductionJacobian.RelativeGroupLaw.ClosedImage"

theorem solution
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f] [QuasiCompact f]
    (L : RelativeGroupLaw k f)
    {H : Scheme.{u}} {g : H ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType g] [QuasiCompact g]
    (M : RelativeGroupLaw k g)
    (φ : SchemeHomOver f g)
    (hφ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      NeronModelInfra.schemeHomOverComp (L.mul t x y) φ =
        M.mul t (NeronModelInfra.schemeHomOverComp x φ)
          (NeronModelInfra.schemeHomOverComp y φ)) :
    IsClosed (Set.range φ.1) :=
  GoodReductionJacobian.RelativeGroupLaw.ClosedImage.isClosed_range L M φ hφ

end S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClosed_range_of_forall_schemeHomOverComp_mul_eq_of_isAlgClosed (solution)
