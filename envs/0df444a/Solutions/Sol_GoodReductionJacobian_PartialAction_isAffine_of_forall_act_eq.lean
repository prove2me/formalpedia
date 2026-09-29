-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.isAffine_of_forall_act_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/0728ae65-265f-5390-86ab-66edb6eb1b29

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_GoodReductionJacobian_PartialAction_exists_defined_act_eq_of_forall_act_eq
import Theorems.Thm_GoodReductionJacobian_PartialAction_exists_generalLinearGroup_jet_of_forall_defined_act_eq
import Theorems.Thm_AlgebraicGeometry_exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian
import Theorems.Thm_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton
import Theorems.Thm_AlgebraicGeometry_eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_isAffine_of_forall_act_eq
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_isAffine_of_forall_act_eq.GoodReductionJacobian"
open Topology

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw PartialAction PartialAction.exists_defined_act_eq_of_forall_act_eq PartialAction.exists_generalLinearGroup_jet_of_forall_defined_act_eq PartialAction.eq_one_of_forall_act_jet_eq_of_subsingleton RelativeGroupLaw.isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one"
namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "Defined act UnitActs Assoc Compatible hom exists_defined_act_eq_of_forall_act_eq exists_generalLinearGroup_jet_of_forall_defined_act_eq eq_one_of_forall_act_jet_eq_of_subsingleton"
namespace FixedPointCriterion
p2m_open "GoodReductionJacobian.PartialAction GoodReductionJacobian"

section General

variable {k : Type u} [Field k]

theorem isNoetherian_of_locallyOfFiniteType {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [QuasiCompact f] [LocallyOfFiniteType f] : IsNoetherian G := by
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian f
  haveI : CompactSpace G := QuasiCompact.compactSpace_of_compactSpace f
  exact {}

theorem tower_down {d : ℕ → ℕ} {G : Scheme.{u}} {f : G ⟶ Spec (CommRingCat.of k)}
    (ρ : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      SchemeHomOver t f → GL (Fin (d n)) Γ(T, ⊤))
    (hmono : ∀ (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ (n + 1) t x = 1 → ρ n t x = 1)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f)
    (N : ℕ) (hN : ρ N t x = 1) : ∀ n ≤ N, ρ n t x = 1 := by
  induction N with
  | zero => intro n hn; obtain rfl : n = 0 := Nat.le_zero.mp hn; exact hN
  | succ N ih =>
    intro n hn
    rcases Nat.lt_or_eq_of_le hn with h | rfl
    · exact ih (hmono N t x hN) n (Nat.lt_succ_iff.mp h)
    · exact hN

theorem map_eq_one_iff {R S : Type u} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S)
    (c : GL (Fin n) R) :
    Matrix.GeneralLinearGroup.map φ c = 1 ↔
      ∀ i j : Fin n, φ (((c : Matrix (Fin n) (Fin n) R) - 1) i j) = 0 := by
  constructor
  · intro h i j
    have hij := congrArg (fun m : GL (Fin n) S => (m : Matrix (Fin n) (Fin n) S) i j) h
    simp only [Matrix.GeneralLinearGroup.map_apply, Units.val_one] at hij
    rw [Matrix.sub_apply, map_sub, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · intro h
    apply Units.ext
    ext i j
    have hij := h i j
    rw [Matrix.sub_apply, map_sub, sub_eq_zero] at hij
    rw [Units.val_one, Matrix.GeneralLinearGroup.map_apply, hij, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

end General

section Assembly

theorem isAffine
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀) :
    IsAffine G := by

  have hall : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (γ : SchemeHomOver t f),
      ∃ hd : a.Defined γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀),
        a.act γ (GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀) hd =
          GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀ :=
    fun t γ =>
      GoodReductionJacobian.PartialAction.exists_defined_act_eq_of_forall_act_eq
        k f L p a ha P₀ he hfix t γ

  obtain ⟨d, ρ, hmul, hnat, hmono, hfaith⟩ :=
    GoodReductionJacobian.PartialAction.exists_generalLinearGroup_jet_of_forall_defined_act_eq
      k f L p a hu ha P₀ hall

  haveI : IsNoetherian G := isNoetherian_of_locallyOfFiniteType f
  obtain ⟨N, hN⟩ :=
    AlgebraicGeometry.exists_forall_generalLinearGroup_eq_one_of_forall_le_of_isNoetherian
      (G := G) d (fun n {T} (x : T ⟶ G) => ρ n (x ≫ f) ⟨x, rfl⟩)
      (fun n {T} {T'} ψ x => by
        have h := hnat n (x ≫ f) ((ψ ≫ x) ≫ f) ψ (Category.assoc ψ x f).symm ⟨x, rfl⟩
        exact h)

  have hallone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ N t x = 1 → ∀ n, ρ n t x = 1 := by
    intro T t x h n
    obtain ⟨x, rfl⟩ := x
    exact hN x (fun m hm => tower_down ρ hmono (x ≫ f) ⟨x, rfl⟩ N h m hm) n

  obtain ⟨u, hu_def⟩ : ∃ u : SchemeHomOver f f, u = ⟨𝟙 G, Category.id_comp f⟩ := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : GL (Fin (d N)) Γ(G, ⊤), c = ρ N f u := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S : Set Γ(G, ⊤), S =
      Set.range (fun ij : Fin (d N) × Fin (d N) =>
        (((c : Matrix (Fin (d N)) (Fin (d N)) Γ(G, ⊤)) - 1) ij.1 ij.2)) := ⟨_, rfl⟩
  have hρc : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ N t x = Matrix.GeneralLinearGroup.map x.1.appTop.hom c := by
    intro T t x
    have h := hnat N f t x.1 x.2 u
    have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 u = x := by
      subst hu_def
      exact Subtype.ext (Category.comp_id x.1)
    rw [hx, ← hc_def] at h
    exact h
  have hker : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x : SchemeHomOver t f),
      ρ N t x = 1 ↔ ∀ s ∈ S, x.1.appTop.hom s = 0 := by
    intro T t x
    rw [hρc, map_eq_one_iff, hS_def]
    constructor
    · rintro h s ⟨⟨i, j⟩, rfl⟩
      exact h i j
    · intro h i j
      exact h _ ⟨⟨i, j⟩, rfl⟩

  obtain ⟨e, he_def⟩ : ∃ e : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f, e = L.one (𝟙 _) :=
    ⟨_, rfl⟩
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)),
      (L.one t).1 = t ≫ e.1 := by
    intro T t
    have h := L.one_natural (𝟙 (Spec (CommRingCat.of k))) t t (Category.comp_id t)
    rw [he_def]
    exact (congrArg Subtype.val h).symm

  have hart : ∀ {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k))
      [LocallyOfFiniteType t] (x : T ⟶ G), x ≫ f = t → (∀ s ∈ S, x.appTop.hom s = 0) →
      x = t ≫ e.1 := by
    intro T _ t _ x hx hs
    have h1 : ρ N t ⟨x, hx⟩ = 1 := (hker t ⟨x, hx⟩).mpr hs
    have hn : ∀ n, ρ n t ⟨x, hx⟩ = 1 := hallone t ⟨x, hx⟩ h1
    have hxe :=
      GoodReductionJacobian.PartialAction.eq_one_of_forall_act_jet_eq_of_subsingleton
        k f L p V ι hι a hc P₀ t ⟨x, hx⟩ (fun n jn hjn => hfaith n t ⟨x, hx⟩ jn hjn (hn n))
    rw [← hone t]
    exact congrArg Subtype.val hxe

  refine
    GoodReductionJacobian.RelativeGroupLaw.isAffine_of_smooth_of_forall_generalLinearGroup_eq_one_imp_eq_one
      L (d N) (fun t x => ρ N t x) (fun t x y => hmul N t x y)
      (fun t t' ψ hψ x => hnat N t t' ψ hψ x) ?_
  intro T t x h1
  have hs : ∀ s ∈ S, x.1.appTop.hom s = 0 := (hker t x).mp h1
  have hx :=
    AlgebraicGeometry.eq_comp_of_forall_appTop_eq_zero_of_forall_subsingleton
      k f S e.1 (fun {T} _ t _ x hx hs => hart t x hx hs) t x.1 x.2 hs
  apply Subtype.ext
  rw [hx, hone t]

end Assembly

end GoodReductionJacobian.PartialAction.FixedPointCriterion

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hu : a.UnitActs L) (ha : a.Assoc L) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    (he : a.Defined (L.one (𝟙 (Spec (CommRingCat.of k)))) P₀)
    (hfix : ∀ (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) f) (hd : a.Defined γ P₀),
      a.act γ P₀ hd = P₀) :
    IsAffine G :=
  GoodReductionJacobian.PartialAction.FixedPointCriterion.isAffine k f L p V ι hι a hu ha hc P₀ he hfix

end S_GoodReductionJacobian_PartialAction_isAffine_of_forall_act_eq
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_isAffine_of_forall_act_eq (solution)
