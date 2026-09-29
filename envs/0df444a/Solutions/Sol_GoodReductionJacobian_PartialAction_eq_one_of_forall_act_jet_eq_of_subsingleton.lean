-- Prove2me | solution 1 for GoodReductionJacobian.PartialAction.eq_one_of_forall_act_jet_eq_of_subsingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a7ec7b76-d9b5-54c5-be3b-07b88680dbe9

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GoodReductionJacobian_PartialAction
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton.GoodReductionJacobian"
open Topology

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw PartialAction RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex"
namespace PartialAction
p2m_export "GoodReductionJacobian.PartialAction" "pair Defined liftDom liftDom_ι act act_coe modelPoint modelPoint_coe Compatible hom_comp mk dom hom"
namespace JetFaithfulB5c
p2m_open "GoodReductionJacobian.PartialAction GoodReductionJacobian"

section OnePoint

variable {k : Type u} [Field k]

theorem fst_injective_of_section {X S : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of k))
    (s : S ⟶ Spec (CommRingCat.of k)) (σ : Spec (CommRingCat.of k) ⟶ S) (hσ : σ ≫ s = 𝟙 _)
    [Subsingleton ↥S] : Function.Injective (pullback.fst x s) := by
  haveI : Surjective σ := ⟨Function.surjective_to_subsingleton _⟩
  haveI : IsIso (σ ≫ s) := by rw [hσ]; infer_instance
  let π : pullback (pullback.snd x s) σ ⟶ pullback x s := pullback.fst (pullback.snd x s) σ
  have key : π ≫ pullback.fst x s =
      (pullbackLeftPullbackSndIso x s σ).hom ≫ pullback.fst x (σ ≫ s) :=
    (pullbackLeftPullbackSndIso_hom_fst x s σ).symm
  have hinj : Function.Injective (π ≫ pullback.fst x s) := by
    rw [key]
    exact (pullback.fst x (σ ≫ s)).injective.comp (pullbackLeftPullbackSndIso x s σ).hom.injective
  intro z₁ z₂ h
  obtain ⟨w₁, rfl⟩ := π.surjective z₁
  obtain ⟨w₂, rfl⟩ := π.surjective z₂
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply] at h
  rw [hinj h]

theorem isSchemeTheoreticallyDominant_ι {P S Y : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [IsIntegral P]
    (s : S ⟶ Spec (CommRingCat.of k)) (σ : Spec (CommRingCat.of k) ⟶ S) (hσ : σ ≫ s = 𝟙 _)
    [Subsingleton ↥S] (g : Y ⟶ pullback p s) [IsOpenImmersion g]
    (U : Y.Opens) (hU : (U : Set ↥Y).Nonempty) : IsSchemeTheoreticallyDominant U.ι := by
  haveI : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  let q : Y ⟶ P := g ≫ pullback.fst p s
  have hqinj : Function.Injective q :=
    (fst_injective_of_section p s σ hσ).comp g.injective
  have hqopen : IsOpenMap q := q.isOpenMap
  let U₀ : P.Opens := ⟨q '' (U : Set ↥Y), hqopen _ U.isOpen⟩
  have hU₀ : ((U₀ : P.Opens) : Set ↥P).Nonempty := hU.image _
  haveI : IsDominant U₀.ι := by
    rw [isDominant_iff]
    rw [show ⇑U₀.ι = fun z => (U₀.ι : _) z from rfl]
    have : Set.range U₀.ι = (U₀ : Set ↥P) := Scheme.Opens.range_ι U₀
    rw [DenseRange, this]
    exact U₀.isOpen.dense hU₀
  haveI : IsSchemeTheoreticallyDominant U₀.ι := IsSchemeTheoreticallyDominant.of_isDominant _
  have H : IsSchemeTheoreticallyDominant (q ⁻¹ᵁ U₀).ι :=
    IsSchemeTheoreticallyDominant.of_isPullback (isPullback_morphismRestrict q U₀)
  have hUeq : q ⁻¹ᵁ U₀ = U := by
    ext z
    constructor
    · rintro ⟨z', hz', e⟩
      rwa [← hqinj e]
    · intro hz
      exact ⟨z, hz, rfl⟩
  rwa [hUeq] at H

end OnePoint

section Jets

theorem exists_jet_factor {X P : Scheme.{u}} (π : X ⟶ P) (ξ : ↥X) (y : ↥P) (hy : π ξ = y)
    (n : ℕ) :
    ∃ g : Spec (CommRingCat.of (X.presheaf.stalk ξ ⧸
          IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n)) ⟶
        Spec (CommRingCat.of (P.presheaf.stalk y ⧸ IsLocalRing.maximalIdeal (P.presheaf.stalk y) ^ n)),
      g ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (P.presheaf.stalk y) ^ n))) ≫ P.fromSpecStalk y =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ X.fromSpecStalk ξ ≫ π := by
  subst hy
  have hle : IsLocalRing.maximalIdeal (P.presheaf.stalk (π ξ)) ^ n ≤
      (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n).comap (π.stalkMap ξ).hom := by
    refine le_trans (Ideal.pow_right_mono ?_ n) (Ideal.le_comap_pow _ n)
    intro a ha
    exact map_nonunit (π.stalkMap ξ).hom a ha
  refine ⟨Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (π.stalkMap ξ).hom hle)), ?_⟩
  have e1 : Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (π.stalkMap ξ).hom hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (P.presheaf.stalk (π ξ)) ^ n))) =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ Spec.map (π.stalkMap ξ) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
  have e2 : Spec.map (π.stalkMap ξ) ≫ P.fromSpecStalk (π ξ) = X.fromSpecStalk ξ ≫ π :=
    Scheme.SpecMap_stalkMap_fromSpecStalk π
  calc _ = (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (π.stalkMap ξ).hom hle)) ≫
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (P.presheaf.stalk (π ξ)) ^ n)))) ≫ P.fromSpecStalk (π ξ) :=
        (Category.assoc _ _ _).symm
    _ = (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ Spec.map (π.stalkMap ξ)) ≫
          P.fromSpecStalk (π ξ) := e1 =≫ _
    _ = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫ (Spec.map (π.stalkMap ξ) ≫
          P.fromSpecStalk (π ξ)) := Category.assoc _ _ _
    _ = _ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ^ n))) ≫= e2

end Jets

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

theorem eq_one_of_mul_eq (L : RelativeGroupLaw k f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of k)) (x g : SchemeHomOver t f) (h : L.mul t x g = g) :
    x = L.one t := by
  calc x = L.mul t x (L.one t) := (L.mul_one t x).symm
    _ = L.mul t x (L.mul t g (L.inv t g)) := by rw [L.mul_inv_cancel]
    _ = L.mul t (L.mul t x g) (L.inv t g) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h, L.mul_inv_cancel]

theorem irreducibleSpace_of_connectedSpace [IsAlgClosed k]
    (f : G ⟶ Spec (CommRingCat.of k)) [QuasiCompact f] [ConnectedSpace ↥G] [Smooth f]
    (L : RelativeGroupLaw k f) : IrreducibleSpace ↥G := by
  obtain ⟨G₀, i, L₀, hoi, -, hirr, hrange, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_isOpenImmersion_irreducibleSpace_range_eq_connectedComponent_finiteIndex
      k L
  have hsurj : Function.Surjective i := by
    rw [← Set.range_eq_univ, hrange]
    exact PreconnectedSpace.connectedComponent_eq_univ _
  exact hsurj.irreducibleSpace i.continuous

end Law

section Main

variable {k : Type u} [Field k]

theorem main [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace ↥G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (x : SchemeHomOver t f)
    (hx : ∀ (n : ℕ)
      (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
          IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ n))
          ⟶ P),
      jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
      ∃ hd : a.Defined
          (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
          (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
        (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) :
    x = L.one t := by

  rcases isEmpty_or_nonempty ↥T with hT | ⟨⟨τ₀⟩⟩
  · exact Subtype.ext ((isInitialOfIsEmpty (X := T)).hom_ext _ _)

  haveI : IrreducibleSpace ↥G := irreducibleSpace_of_connectedSpace f L
  haveI : JacobsonSpace ↥G := LocallyOfFiniteType.jacobsonSpace f

  have hτ₀c : IsClosed ({τ₀} : Set ↥T) := by
    have : ({τ₀} : Set ↥T) = Set.univ := Set.eq_univ_of_forall fun z => Subsingleton.elim z τ₀
    rw [this]; exact isClosed_univ
  let τ : Spec (CommRingCat.of k) ⟶ T := pointOfClosedPoint t τ₀ hτ₀c
  have hτt : τ ≫ t = 𝟙 _ := pointOfClosedPoint_comp t τ₀ hτ₀c
  have hτpt : ∀ z : ↥(Spec (CommRingCat.of k)), τ z = τ₀ := pointOfClosedPoint_apply t τ₀ hτ₀c
  have hpt : ∀ z : ↥T, z = τ (IsLocalRing.closedPoint k) := fun z =>
    (Subsingleton.elim _ _)

  set y : ↥P := P₀.1.base (IsLocalRing.closedPoint k) with hy_def
  set O := P.presheaf.stalk y with hO_def

  let X' : Scheme.{u} := pullback p t
  let Φ : X' ⟶ pullback f p :=
    pullback.lift (pullback.snd p t ≫ x.1) (pullback.fst p t)
      (by rw [Category.assoc, x.2]; exact pullback.condition.symm)
  have hΦ_fst : Φ ≫ pullback.fst f p = pullback.snd p t ≫ x.1 := pullback.lift_fst _ _ _
  have hΦ_snd : Φ ≫ pullback.snd f p = pullback.fst p t := pullback.lift_snd _ _ _
  let D : X'.Opens := Φ ⁻¹ᵁ a.dom
  let Xd : Scheme.{u} := D
  let Φ' : Xd ⟶ (a.dom : Scheme.{u}) := Φ ∣_ a.dom
  have hΦ' : Φ' ≫ a.dom.ι = D.ι ≫ Φ := morphismRestrict_ι Φ a.dom
  obtain ⟨actx, hactx⟩ : ∃ m : Xd ⟶ P, m = Φ' ≫ a.hom := ⟨_, rfl⟩
  obtain ⟨prx, hprx⟩ : ∃ m : Xd ⟶ P, m = D.ι ≫ pullback.fst p t := ⟨_, rfl⟩
  have hover : actx ≫ p = prx ≫ p := by
    rw [hactx, hprx, Category.assoc, a.hom_comp, ← Category.assoc Φ', hΦ', Category.assoc,
      Category.assoc, ← Category.assoc Φ, hΦ_snd]

  have hread : ∀ {T' : Scheme.{u}} {t' : T' ⟶ Spec (CommRingCat.of k)}
      (γ : SchemeHomOver t' f) (z : SchemeHomOver t' p) (ζ : T' ⟶ X')
      (hζ : ζ ≫ Φ = pair γ z) (hd : a.Defined γ z),
      ∃ ζ' : T' ⟶ Xd, ζ' ≫ D.ι = ζ ∧ (a.act γ z hd).1 = ζ' ≫ actx := by
    intro T' t' γ z ζ hζ hd
    have hr : Set.range ζ ⊆ (D : Set ↥X') := by
      rintro _ ⟨w, rfl⟩
      show Φ (ζ w) ∈ (a.dom : Set ↥(pullback f p))
      rw [← Scheme.Hom.comp_apply, hζ]
      exact hd ⟨w, rfl⟩
    let ζ' : T' ⟶ Xd := IsOpenImmersion.lift D.ι ζ (by rw [Scheme.Opens.range_ι]; exact hr)
    have hζ' : ζ' ≫ D.ι = ζ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨ζ', hζ', ?_⟩
    have hl : a.liftDom γ z hd = ζ' ≫ Φ' := by
      rw [← cancel_mono a.dom.ι, liftDom_ι, Category.assoc, hΦ', ← Category.assoc, hζ', hζ]
    rw [act_coe, hl, Category.assoc, hactx]

  haveI : IsLocallyNoetherian X' :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd p t ≫ t)
  haveI : IsLocallyNoetherian Xd := inferInstance
  have hdense : ∀ U : Xd.Opens, (U : Set ↥Xd).Nonempty → IsSchemeTheoreticallyDominant U.ι :=
    fun U hU => isSchemeTheoreticallyDominant_ι p t τ hτt D.ι U hU

  let e₀ : O ⟶ CommRingCat.of k := Scheme.stalkClosedPointTo P₀.1
  have he₀ : ∀ b ∈ IsLocalRing.maximalIdeal O, e₀.hom b = 0 := by
    intro b hb
    have h := map_nonunit e₀.hom b hb
    rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_ne_zero, not_not] at h
  have hq : ∀ b ∈ IsLocalRing.maximalIdeal O ^ 1, e₀.hom b = 0 := by
    intro b hb
    exact he₀ b (Ideal.pow_le_self one_ne_zero hb)
  let q₁ : (O ⧸ IsLocalRing.maximalIdeal O ^ 1) →+* k := Ideal.Quotient.lift _ e₀.hom hq
  obtain ⟨j1, hj1⟩ : ∃ j : Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O ^ 1)) ⟶ P,
      j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1))) ≫
        P.fromSpecStalk y := ⟨_, rfl⟩
  have hq₁ : Spec.map (CommRingCat.ofHom q₁) ≫ j1 = P₀.1 := by
    have e1 : Spec.map (CommRingCat.ofHom q₁) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1))) =
        Spec.map e₀ := by
      rw [← Spec.map_comp]
      congr 1
    calc Spec.map (CommRingCat.ofHom q₁) ≫ j1
        = Spec.map (CommRingCat.ofHom q₁) ≫ (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1))) ≫ P.fromSpecStalk y) := _ ≫= hj1
      _ = (Spec.map (CommRingCat.ofHom q₁) ≫ Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ 1)))) ≫ P.fromSpecStalk y :=
          (Category.assoc _ _ _).symm
      _ = Spec.map e₀ ≫ P.fromSpecStalk y := e1 =≫ _
      _ = P₀.1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk P₀.1

  have hw₁ : 𝟙 T ≫ t = (t ≫ Spec.map (CommRingCat.ofHom q₁)) ≫ (j1 ≫ p) := by
    rw [Category.id_comp, Category.assoc, ← Category.assoc (Spec.map _), hq₁, P₀.2,
      Category.comp_id]
  let lam1 : T ⟶ pullback t (j1 ≫ p) := pullback.lift (𝟙 T) (t ≫ Spec.map (CommRingCat.ofHom q₁)) hw₁
  obtain ⟨hd₁, -⟩ := hx 1 j1 hj1

  let P₀T : SchemeHomOver t p := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) P₀
  have hP₀T : P₀T.1 = t ≫ P₀.1 := rfl
  have hdef₀ : a.Defined x P₀T := by
    have hpair : pair x P₀T = lam1 ≫ pair
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (j1 ≫ p)) rfl x :
          SchemeHomOver (pullback.fst t (j1 ≫ p) ≫ t) f)
        (⟨pullback.snd t (j1 ≫ p) ≫ j1, by rw [Category.assoc, pullback.condition]⟩ :
          SchemeHomOver (pullback.fst t (j1 ≫ p) ≫ t) p) := by
      apply pullback.hom_ext
      · simp only [pair, pullback.lift_fst, Category.assoc, GoodReductionJacobian.schemeHomOverComp_coe]
        rw [← Category.assoc, pullback.lift_fst, Category.id_comp]
      · simp only [pair, pullback.lift_snd, Category.assoc]
        rw [← Category.assoc lam1, pullback.lift_snd, Category.assoc, hq₁, hP₀T]
    intro w hw
    rw [hpair, Scheme.Hom.comp_base] at hw
    obtain ⟨w', rfl⟩ := hw
    exact hd₁ ⟨lam1 w', rfl⟩

  let ζ₀ : T ⟶ X' := pullback.lift (t ≫ P₀.1) (𝟙 T)
    (by rw [Category.assoc, P₀.2, Category.comp_id, Category.id_comp])
  have hζ₀Φ : ζ₀ ≫ Φ = pair x P₀T := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦ_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        pullback.lift_fst]
    · rw [Category.assoc, hΦ_snd, pullback.lift_fst, pullback.lift_snd, hP₀T]
  obtain ⟨ζ₀', hζ₀', -⟩ := hread x P₀T ζ₀ hζ₀Φ hdef₀
  let ξ : ↥Xd := ζ₀' τ₀
  have hξ : prx ξ = y := by
    show prx (ζ₀' τ₀) = y
    rw [← Scheme.Hom.comp_apply, hprx, ← Category.assoc, hζ₀', pullback.lift_fst,
      Scheme.Hom.comp_apply, hy_def]
    congr 1
    exact Subsingleton.elim _ _

  have hjets : ∀ n : ℕ,
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n))) ≫ Xd.fromSpecStalk ξ ≫ actx =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n))) ≫ Xd.fromSpecStalk ξ ≫ prx := by
    intro n
    obtain ⟨g, hg⟩ := exists_jet_factor prx ξ y hξ n
    obtain ⟨jn, hjn⟩ : ∃ j : Spec (CommRingCat.of (O ⧸ IsLocalRing.maximalIdeal O ^ n)) ⟶ P,
        j = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O ^ n))) ≫
          P.fromSpecStalk y := ⟨_, rfl⟩
    obtain ⟨sn, hsn⟩ : ∃ s : Spec (CommRingCat.of (Xd.presheaf.stalk ξ ⧸
        IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n)) ⟶ Xd,
        s = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (Xd.presheaf.stalk ξ) ^ n))) ≫ Xd.fromSpecStalk ξ := ⟨_, rfl⟩
    have hg' : g ≫ jn = sn ≫ prx := by rw [hjn, hsn, Category.assoc]; exact hg

    have hwσ : (sn ≫ D.ι ≫ pullback.snd p t) ≫ t = g ≫ (jn ≫ p) := by
      rw [← Category.assoc g, hg', hprx]
      simp only [Category.assoc]
      rw [pullback.condition]
    let σ : _ ⟶ pullback t (jn ≫ p) := pullback.lift (sn ≫ D.ι ≫ pullback.snd p t) g hwσ
    obtain ⟨hd, hact⟩ := hx n jn hjn
    have hpair : σ ≫ pair
        (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
          SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
        (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
          SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p) = sn ≫ D.ι ≫ Φ := by
      apply pullback.hom_ext
      · simp only [pair, Category.assoc, pullback.lift_fst, GoodReductionJacobian.schemeHomOverComp_coe]
        rw [← Category.assoc σ, pullback.lift_fst, hΦ_fst]
        simp only [Category.assoc]
      · simp only [pair, Category.assoc, pullback.lift_snd]
        rw [← Category.assoc σ, pullback.lift_snd, hg', hΦ_snd, hprx]
    have hl : σ ≫ a.liftDom _ _ hd = sn ≫ Φ' := by
      rw [← cancel_mono a.dom.ι, Category.assoc, liftDom_ι, hpair, Category.assoc, hΦ']
    have key : sn ≫ actx = sn ≫ prx := by
      calc sn ≫ actx = (sn ≫ Φ') ≫ a.hom := by rw [hactx, Category.assoc]
        _ = σ ≫ (a.act _ _ hd).1 := by rw [← hl, act_coe, Category.assoc]
        _ = σ ≫ pullback.snd t (jn ≫ p) ≫ jn := by rw [hact]
        _ = g ≫ jn := by rw [← Category.assoc, pullback.lift_snd]
        _ = sn ≫ prx := hg'
    rw [hsn, Category.assoc, Category.assoc] at key
    exact key

  have hagree : actx = prx :=
    AlgebraicGeometry.eq_of_forall_specMap_quotient_maximalIdeal_pow_comp_eq_of_isSchemeTheoreticallyDominant
      hdense actx prx p hover ξ hjets

  let ek : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := 𝟙 _
  let x₀ : SchemeHomOver ek f := ⟨τ ≫ x.1, by rw [Category.assoc, x.2, hτt]⟩
  let x₀G : SchemeHomOver f f := GoodReductionJacobian.schemeHomOverComp f (Category.comp_id f) x₀
  let uG : SchemeHomOver f f := ⟨𝟙 G, Category.id_comp f⟩
  let ψ : G ⟶ G := (L.mul f x₀G uG).1
  have hψ : ∀ z : SchemeHomOver ek f,
      GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.mul f x₀G uG) = L.mul ek x₀ z := by
    intro z
    have h1 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 x₀G = x₀ := by
      apply Subtype.ext
      simp only [GoodReductionJacobian.schemeHomOverComp_coe, x₀G]
      rw [← Category.assoc, z.2, Category.id_comp]
    have h2 : GoodReductionJacobian.schemeHomOverComp z.1 z.2 uG = z :=
      Subtype.ext (Category.comp_id _)
    rw [L.mul_natural, h1, h2]
  have hψpt : ∀ z : SchemeHomOver ek f,
      ψ (z.1 (IsLocalRing.closedPoint k)) = (L.mul ek x₀ z).1 (IsLocalRing.closedPoint k) := by
    intro z
    have h := congrArg (fun φ : SchemeHomOver ek f => φ.1 (IsLocalRing.closedPoint k)) (hψ z)
    simpa only [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply] using h

  have hVne : ((V : G.Opens) : Set ↥G).Nonempty := by
    rw [← Scheme.Opens.range_ι V]
    exact Set.range_nonempty _
  obtain ⟨g₁, hg₁V, hg₁c⟩ := nonempty_inter_closedPoints hVne V.isOpen.isLocallyClosed
  let v₁ : SchemeHomOver ek f := ⟨pointOfClosedPoint f g₁ hg₁c, pointOfClosedPoint_comp f g₁ hg₁c⟩
  have hv₁pt : v₁.1 (IsLocalRing.closedPoint k) = g₁ := pointOfClosedPoint_apply f g₁ hg₁c _

  have hU : ((V ⊓ ψ ⁻¹ᵁ V : G.Opens) : Set ↥G).Nonempty := by
    have h2 : ((ψ ⁻¹ᵁ V : G.Opens) : Set ↥G).Nonempty := by
      refine ⟨(L.mul ek (L.inv ek x₀) v₁).1 (IsLocalRing.closedPoint k), ?_⟩
      show ψ _ ∈ V
      rw [hψpt, ← L.mul_assoc, L.mul_inv_cancel, L.one_mul, hv₁pt]
      exact hg₁V
    exact nonempty_preirreducible_inter V.isOpen (ψ ⁻¹ᵁ V).isOpen hVne h2
  obtain ⟨g₀, hg₀U, hg₀c⟩ := nonempty_inter_closedPoints hU (V ⊓ ψ ⁻¹ᵁ V).isOpen.isLocallyClosed
  let v₀ : SchemeHomOver ek f := ⟨pointOfClosedPoint f g₀ hg₀c, pointOfClosedPoint_comp f g₀ hg₀c⟩
  have hv₀pt : v₀.1 (IsLocalRing.closedPoint k) = g₀ := pointOfClosedPoint_apply f g₀ hg₀c _
  have hv₀V : v₀.1 (IsLocalRing.closedPoint k) ∈ V := by rw [hv₀pt]; exact hg₀U.1
  have hxv₀V : (L.mul ek x₀ v₀).1 (IsLocalRing.closedPoint k) ∈ V := by
    rw [← hψpt, hv₀pt]
    exact hg₀U.2

  let vT : SchemeHomOver t f := GoodReductionJacobian.schemeHomOverComp t (Category.comp_id t) v₀
  let wT : SchemeHomOver t f := L.mul t x vT
  have hτx : GoodReductionJacobian.schemeHomOverComp τ hτt x = x₀ := Subtype.ext rfl
  have hτv : GoodReductionJacobian.schemeHomOverComp τ hτt vT = v₀ := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe, vT]
    rw [← Category.assoc, hτt, Category.id_comp]
  have hτw : GoodReductionJacobian.schemeHomOverComp τ hτt wT = L.mul ek x₀ v₀ := by
    simp only [wT]
    rw [L.mul_natural, hτx, hτv]
  have hval : ∀ (g : SchemeHomOver t f) (z : ↥T),
      g.1 z = (GoodReductionJacobian.schemeHomOverComp τ hτt g).1 (IsLocalRing.closedPoint k) := by
    intro g z
    rw [GoodReductionJacobian.schemeHomOverComp_coe, Scheme.Hom.comp_apply, hτpt, hpt z, hτpt]
  have hvT : Set.range vT.1 ⊆ (V : Set ↥G) := by
    rintro _ ⟨z, rfl⟩
    rw [hval, hτv]; exact hv₀V
  have hwT : Set.range wT.1 ⊆ (V : Set ↥G) := by
    rintro _ ⟨z, rfl⟩
    rw [hval, hτw]; exact hxv₀V
  let v : SchemeHomOver t (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι vT.1 (by rw [Scheme.Opens.range_ι]; exact hvT), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact vT.2⟩
  let w : SchemeHomOver t (V.ι ≫ f) :=
    ⟨IsOpenImmersion.lift V.ι wT.1 (by rw [Scheme.Opens.range_ι]; exact hwT), by
      rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact wT.2⟩
  have hvι : NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) = vT :=
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hwι : NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) = wT :=
    Subtype.ext (IsOpenImmersion.lift_fac _ _ _)
  have hvw : NeronModelInfra.schemeHomOverComp w (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f) =
      L.mul t x (NeronModelInfra.schemeHomOverComp v (⟨V.ι, rfl⟩ : SchemeHomOver (V.ι ≫ f) f)) := by
    rw [hwι, hvι]

  obtain ⟨hd, hcomp⟩ := hc t x v w hvw
  let ζv : T ⟶ X' := pullback.lift (v.1 ≫ ι) (𝟙 T)
    (by rw [Category.assoc, hι, ← Category.assoc, IsOpenImmersion.lift_fac, Category.id_comp]
        exact vT.2)
  have hζvΦ : ζv ≫ Φ = pair x (modelPoint ι hι v) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hΦ_fst, ← Category.assoc, pullback.lift_snd, Category.id_comp,
        pullback.lift_fst]
    · rw [Category.assoc, hΦ_snd, pullback.lift_fst, pullback.lift_snd, modelPoint_coe]
  obtain ⟨ζv', hζv', hactv⟩ := hread x (modelPoint ι hι v) ζv hζvΦ hd
  have htriv : (a.act x (modelPoint ι hι v) hd).1 = v.1 ≫ ι := by
    rw [hactv, hagree, hprx, ← Category.assoc, hζv', pullback.lift_fst]
  have hwv : w.1 = v.1 := by
    rw [← cancel_mono ι, ← htriv, hcomp, modelPoint_coe]
  have hwTvT : L.mul t x vT = vT := by
    show wT = vT
    rw [← hwι, ← hvι, show w = v from Subtype.ext hwv]
  exact eq_one_of_mul_eq L t x vT hwTvT

end Main

end GoodReductionJacobian.PartialAction.JetFaithfulB5c

theorem solution
    (k : Type u) [Field k] [IsAlgClosed k] {G : Scheme.{u}} (f : G ⟶ Spec (CommRingCat.of k))
    [IsSeparated f] [QuasiCompact f] [ConnectedSpace G] [Smooth f]
    (L : RelativeGroupLaw k f)
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k))
    [IsSeparated p] [LocallyOfFiniteType p] [IsIntegral P]
    (V : G.Opens) [Nonempty (V : Scheme.{u})] (ι : (V : Scheme.{u}) ⟶ P) [IsOpenImmersion ι]
    (hι : ι ≫ p = V.ι ≫ f)
    (a : PartialAction k f p) (hc : a.Compatible L V ι hι)
    (P₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) p)
    {T : Scheme.{u}} [Subsingleton ↥T] (t : T ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType t]
    (x : SchemeHomOver t f)
    (hx : ∀ (n : ℕ)
      (jn : Spec (CommRingCat.of (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k)) ⧸
          IsLocalRing.maximalIdeal (P.presheaf.stalk (P₀.1.base (IsLocalRing.closedPoint k))) ^ n))
          ⟶ P),
      jn = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk _)) ≫ P.fromSpecStalk _ →
      ∃ hd : a.Defined
          (GoodReductionJacobian.schemeHomOverComp (pullback.fst t (jn ≫ p)) rfl x :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) f)
          (⟨pullback.snd t (jn ≫ p) ≫ jn, by rw [Category.assoc, pullback.condition]⟩ :
            SchemeHomOver (pullback.fst t (jn ≫ p) ≫ t) p),
        (a.act _ _ hd).1 = pullback.snd t (jn ≫ p) ≫ jn) :
    x = L.one t :=
  GoodReductionJacobian.PartialAction.JetFaithfulB5c.main f L p V ι hι a hc P₀ t x hx

end S_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton
end P2MW
export P2MW.S_GoodReductionJacobian_PartialAction_eq_one_of_forall_act_jet_eq_of_subsingleton (solution)
