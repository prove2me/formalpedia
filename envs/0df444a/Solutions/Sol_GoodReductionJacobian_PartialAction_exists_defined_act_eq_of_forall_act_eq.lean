-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/118913f3-91fb-5131-8627-a100439a09a4

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
import Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.GoodReductionJacobian"
open Topology

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex"
namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "pair Defined liftDom liftDom_ι act act_coe Assoc hom_comp dom hom"
namespace EverythingActs
p2m_open "GoodReductionJacobian.PartialAction GoodReductionJacobian"

section Law

variable {k : Type u} [Field k] {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}

theorem inv_natural (L : RelativeGroupLaw k f) {T T' : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (t' : T' ⟶ Spec (CommRingCat.of k)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) =
      L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  set y := GoodReductionJacobian.schemeHomOverComp ψ hψ x with hy
  set z := GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) with hz
  have h : L.mul t' z y = L.one t' := by
    rw [hz, hy, ← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  calc z = L.mul t' z (L.one t') := (L.mul_one t' z).symm
    _ = L.mul t' z (L.mul t' y (L.inv t' y)) := by rw [L.mul_inv_cancel]
    _ = L.mul t' (L.mul t' z y) (L.inv t' y) := by rw [L.mul_assoc]
    _ = L.inv t' y := by rw [h, L.one_mul]

end Law

section Group

variable {k : Type u} [Field k]

theorem irreducibleSpace_of_connectedSpace [IsAlgClosed k] {G : Scheme.{u}}
    (f : G ⟶ Spec (CommRingCat.of k)) [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f) : IrreducibleSpace G := by
  obtain ⟨G₀, i, L₀, hoi, -, hirr, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      k L
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  exact hsurj.irreducibleSpace i.continuous

theorem isField_sections (k : Type u) [Field k] :
    IsField (Γ(Spec (CommRingCat.of k), ⊤) : Type u) :=
  MulEquiv.isField (Field.toIsField k)
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.toMulEquiv

scoped instance isDomain_sections (k : Type u) [Field k] :
    IsDomain (Γ(Spec (CommRingCat.of k), ⊤) : Type u) :=
  (isField_sections k).isDomain

scoped instance isIntegrallyClosed_sections (k : Type u) [Field k] :
    IsIntegrallyClosed (Γ(Spec (CommRingCat.of k), ⊤) : Type u) := by
  letI : Field (Γ(Spec (CommRingCat.of k), ⊤) : Type u) := (isField_sections k).toField
  infer_instance

theorem isReduced_of_smooth {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k)) [Smooth f] :
    IsReduced G := by
  haveI : ∀ x : G, _root_.IsReduced (G.presheaf.stalk x) := fun x => by
    haveI := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk f x).1
    infer_instance
  exact isReduced_of_isReduced_stalk G

end Group

section Main

variable {k : Type u} [Field k]

theorem main [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f) :
    ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
      a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
        GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀ := by

  haveI : IrreducibleSpace G := irreducibleSpace_of_connectedSpace f L
  haveI : IsReduced G := isReduced_of_smooth f
  haveI : JacobsonSpace G := LocallyOfFiniteType.jacobsonSpace f

  obtain ⟨s, hs_fst, hs_snd⟩ : ∃ s : G ⟶ pullback f p,
      s ≫ pullback.fst f p = 𝟙 G ∧ s ≫ pullback.snd f p = f ≫ P₀.1 :=
    ⟨pullback.lift (𝟙 G) (f ≫ P₀.1)
        (by rw [Category.id_comp, Category.assoc, P₀.2, Category.comp_id]),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hpair : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      pair γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) = γ.1 ≫ s := by
    intro T t γ
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, hs_fst, Category.comp_id]
    · rw [pullback.lift_snd, Category.assoc, hs_snd, ← Category.assoc, γ.2]
      rfl
  set Ω : G.Opens := s ⁻¹ᵁ a.dom with hΩ_def
  have hDef : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) ↔
        ∀ z : T, γ.1 z ∈ Ω := by
    intro T t γ
    unfold Defined
    rw [hpair, Set.range_subset_iff]
    exact Iff.rfl
  have hP₀1 : GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _) P₀ = P₀ :=
    Subtype.ext (Category.id_comp _)
  have hDefk : ∀ γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, a.Defined γ P₀ ↔ γ.1 (IsLocalRing.closedPoint k) ∈ Ω := by
    intro γ
    rw [← hP₀1, hDef]
    constructor
    · intro h; exact h (IsLocalRing.closedPoint k)
    · intro h z; rwa [Subsingleton.elim z (IsLocalRing.closedPoint k)]
  have heΩ : (L.one (𝟙 (Spec (CommRingCat.of k)))).1 (IsLocalRing.closedPoint k) ∈ Ω := (hDefk _).mp he

  have hkdef : ∀ γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, a.Defined γ P₀ := by
    intro γ
    let γG : SchemeHomOver f f := GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) γ
    let uG : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩
    let ψ : G ⟶ G := (L.mul f γG (L.inv f uG)).1

    have hψ : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        GoodReductionJacobian.schemeHomOverComp x.1 x.2 (L.mul f γG (L.inv f uG)) =
          L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x) := by
      intro x
      have h1 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 γG = γ := by
        apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe, γG]
        rw [← Category.assoc, x.2, Category.id_comp]
      have h2 : GoodReductionJacobian.schemeHomOverComp x.1 x.2 uG = x :=
        Subtype.ext (Category.comp_id _)
      rw [L.mul_natural, inv_natural, h1, h2]
    have hψpt : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f,
        ψ (x.1 (IsLocalRing.closedPoint k)) = (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x)).1 (IsLocalRing.closedPoint k) := by
      intro x
      have h := congrArg (fun φ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f => φ.1 (IsLocalRing.closedPoint k)) (hψ x)
      simpa only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply] using h

    have hγe : L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) γ) = L.one (𝟙 (Spec (CommRingCat.of k))) := L.mul_inv_cancel _ _
    have hU : ((Ω ⊓ ψ ⁻¹ᵁ Ω : G.Opens) : Set G).Nonempty := by
      have h1 : (Ω : Set G).Nonempty := ⟨_, heΩ⟩
      have h2 : ((ψ ⁻¹ᵁ Ω : G.Opens) : Set G).Nonempty := by
        refine ⟨γ.1 (IsLocalRing.closedPoint k), ?_⟩
        show ψ (γ.1 (IsLocalRing.closedPoint k)) ∈ Ω
        rw [hψpt γ, hγe]
        exact heΩ
      exact nonempty_preirreducible_inter Ω.isOpen (ψ ⁻¹ᵁ Ω).isOpen h1 h2
    obtain ⟨x₀, hx₀U, hx₀c⟩ :=
      nonempty_inter_closedPoints hU (Ω ⊓ ψ ⁻¹ᵁ Ω).isOpen.isLocallyClosed

    let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
      ⟨pointOfClosedPoint f x₀ hx₀c, pointOfClosedPoint_comp f x₀ hx₀c⟩
    have hxpt : x.1 (IsLocalRing.closedPoint k) = x₀ := pointOfClosedPoint_apply f x₀ hx₀c (IsLocalRing.closedPoint k)
    have hxΩ : x.1 (IsLocalRing.closedPoint k) ∈ Ω := by rw [hxpt]; exact hx₀U.1
    have hδΩ : (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x)).1 (IsLocalRing.closedPoint k) ∈ Ω := by
      rw [← hψpt x]
      have h : x₀ ∈ (ψ ⁻¹ᵁ Ω : G.Opens) := hx₀U.2
      rw [hxpt]
      exact h
    have hdx : a.Defined x P₀ := (hDefk x).mpr hxΩ
    have hdδ : a.Defined (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x)) P₀ := (hDefk _).mpr hδΩ
    have hfx : a.act x P₀ hdx = P₀ := hfix x hdx
    have hdδ' : a.Defined (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x)) (a.act x P₀ hdx) := by
      rw [hfx]; exact hdδ
    obtain ⟨hd3, -⟩ := ha (𝟙 (Spec (CommRingCat.of k))) (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x)) x P₀ hdx hdδ'
    have hγeq : L.mul (𝟙 (Spec (CommRingCat.of k))) (L.mul (𝟙 (Spec (CommRingCat.of k))) γ (L.inv (𝟙 (Spec (CommRingCat.of k))) x)) x = γ := by
      rw [L.mul_assoc, L.inv_mul_cancel, L.mul_one]
    rwa [hγeq] at hd3

  have hΩ : ∀ g : G, g ∈ Ω := by
    intro g
    by_contra hg
    have hne : ((Ω : Set G)ᶜ).Nonempty := ⟨g, hg⟩
    obtain ⟨x₀, hx₀, hx₀c⟩ :=
      nonempty_inter_closedPoints hne Ω.isOpen.isClosed_compl.isLocallyClosed
    apply hx₀
    have h := (hDefk ⟨pointOfClosedPoint f x₀ hx₀c, pointOfClosedPoint_comp f x₀ hx₀c⟩).mp
      (hkdef _)
    rwa [pointOfClosedPoint_apply] at h

  have hdT : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) :=
    (hDef t γ).mpr (fun z => hΩ _)
  refine ⟨hdT, ?_⟩

  have hsr : Set.range s ⊆ Set.range a.dom.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨g, rfl⟩
    exact hΩ g
  let s' : G ⟶ (a.dom : Scheme.{u}) := IsOpenImmersion.lift a.dom.ι s hsr
  have hs' : s' ≫ a.dom.ι = s := IsOpenImmersion.lift_fac _ _ _
  let o : G ⟶ P := s' ≫ a.hom
  have ho_p : o ≫ p = f := by
    show (s' ≫ a.hom) ≫ p = f
    rw [Category.assoc, a.hom_comp, ← Category.assoc s', hs', ← Category.assoc, hs_snd,
      Category.assoc, P₀.2, Category.comp_id]
  have hc_p : (f ≫ P₀.1) ≫ p = f := by rw [Category.assoc, P₀.2, Category.comp_id]
  have hact : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f)
      (hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀)),
      (a.act γ _ hd).1 = γ.1 ≫ o := by
    intro T t γ hd
    have hl : a.liftDom γ _ hd = γ.1 ≫ s' := by
      rw [← cancel_mono a.dom.ι, liftDom_ι, Category.assoc, hs', hpair]
    rw [act_coe, hl, Category.assoc]
  have hoc : o = f ≫ P₀.1 := by
    haveI : LocallyOfFiniteType (o ≫ p) := by rw [ho_p]; infer_instance
    refine ext_of_apply_eq p Set.univ isOpen_univ.isLocallyClosed dense_univ ?_ (by rw [ho_p, hc_p])
    intro g _ hgc
    let gk : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f :=
      ⟨pointOfClosedPoint f g hgc, pointOfClosedPoint_comp f g hgc⟩
    have hdg : a.Defined gk
        (GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _) P₀) := by
      rw [hP₀1]; exact hkdef gk
    have hfixg : a.act gk _ hdg =
        GoodReductionJacobian.schemeHomOverComp (𝟙 (Spec (CommRingCat.of k))) (Category.comp_id _) P₀ := by
      have key : ∀ (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p) (hQ : Q = P₀) (hd : a.Defined gk Q),
          a.act gk Q hd = Q := by
        intro Q hQ hd; subst hQ; exact hfix gk hd
      exact key _ hP₀1 hdg
    have h1 : gk.1 ≫ o = gk.1 ≫ f ≫ P₀.1 := by
      rw [← hact (𝟙 (Spec (CommRingCat.of k))) gk hdg, hfixg, GoodReductionJacobian.schemeHomOverComp_coe,
        ← Category.assoc, gk.2]
    have h2 := congrArg (fun φ : Spec (CommRingCat.of k) ⟶ P => φ (IsLocalRing.closedPoint k)) h1
    simp only [Scheme.Hom.comp_apply] at h2
    rwa [pointOfClosedPoint_apply] at h2
  apply Subtype.ext
  rw [hact t γ hdT, hoc, ← Category.assoc, γ.2]
  rfl

end Main

end GoodReductionJacobian.PartialAction.EverythingActs
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.GoodReductionJacobian.PartialAction P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.GoodReductionJacobian.PartialAction.EverythingActs"
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.GoodReductionJacobian.PartialAction"
p2m_reactivate "P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq.GoodReductionJacobian"

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [IsSeparated p] [LocallyOfFiniteType p]
    (a : PartialAction k f p) (ha : a.Assoc L)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f) :
    ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
      a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
        GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀ :=
  GoodReductionJacobian.PartialAction.EverythingActs.main f L p a ha P₀ he hfix t γ

end S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq (solution)
