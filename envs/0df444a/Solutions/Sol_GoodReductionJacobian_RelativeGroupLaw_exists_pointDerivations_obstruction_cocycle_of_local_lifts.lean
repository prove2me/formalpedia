-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_pointDerivations_obstruction_cocycle_of_local_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e20c5c11-2227-55dd-9e46-eb7a7aca2a39

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Theorems.Thm_AlgebraicGeometry_IsPullback_exists_iso_Spec_quotient_comp_morphismRestrict_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_flat_sections_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_d_comap_slice_eq_of_obstruction_cocycle
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing TensorProduct AlgebraicGeometry.SmallExtension AlgebraicGeometry.Scheme.TwoAffineOpenCover"

universe u v w x y z

namespace K2alphaO1

section Generic

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (q : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := algebraOfHom q U
    hU.fromSpec ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom q U
  have h1 : CommRingCat.ofHom (algebraMap R Γ(X, U)) = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ q.appLE ⊤ U le_top := rfl
  rw [h1, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec q (isAffineOpen_top (Spec (CommRingCat.of R))) hU le_top]

theorem specMap_mk_comp_isoSpec_inv_comp_eq {T' T : Type u} [CommRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {X X₀ Y : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of T')) (p₀ : X₀ ⟶ Spec (CommRingCat.of T))
    (G : X₀ ⟶ X) (hG : IsPullback G p₀ p (Spec.map (CommRingCat.ofHom π)))
    {U : X.Opens} (hU : IsAffineOpen U) (w w' : (↑U : Scheme.{u}) ⟶ Y) (h : (G ∣_ U) ≫ w = (G ∣_ U) ≫ w') :
    letI := algebraOfHom p U
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(X, U))))) ≫ hU.isoSpec.inv ≫ w
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(X, U))))) ≫
        hU.isoSpec.inv ≫ w' := by
  letI := algebraOfHom p U
  obtain ⟨-, ε, hε⟩ := AlgebraicGeometry.IsPullback.exists_iso_Spec_quotient_comp_morphismRestrict_eq π hπ hker p p₀ G hG U hU
  have hε' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(X, U))))) ≫ hU.isoSpec.inv
      = ε.hom ≫ (G ∣_ U) := by
    rw [← hε, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, hε', Category.assoc, h, ← Category.assoc, ← hε', Category.assoc]

end Generic

section Charts

variable {T' : Type u} [CommRing T'] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
  [IsSeparated (pullback.fst f f ≫ f)] (𝒲 : (pullback f f).OrderedAffineCover)

theorem flat_sections (hs : Smooth f) {n : ℕ} (s : 𝒲.Idx n) :
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    Module.Flat T' Γ(pullback f f, 𝒲.inter s) := by
  haveI : Smooth f := hs
  haveI : Flat (pullback.fst f f) := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : Flat (pullback.fst f f ≫ f) := inferInstance
  exact Scheme.TwoAffineOpenCover.flat_sections_of_flat (pullback.fst f f ≫ f) (𝒲.inter s)
    (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s)

omit [IsSeparated (pullback.fst f f ≫ f)] in

theorem specMap_isoSpec_inv_homOfLE {X : Scheme.{u}} {U V W : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (h : V ≤ U) (hUW : U ≤ W) (hVW : V ≤ W) :
    Spec.map (X.presheaf.map (homOfLE h).op) ≫ hU.isoSpec.inv ≫ X.homOfLE hUW = hV.isoSpec.inv ≫ X.homOfLE hVW := by
  rw [← cancel_mono W.ι]
  simp only [Category.assoc, Scheme.homOfLE_ι, IsAffineOpen.isoSpec_inv_ι]
  exact IsAffineOpen.map_fromSpec _ _ _

theorem specMap_restrict_isoSpec_inv_homOfLE {n : ℕ} (t : 𝒲.Idx (n + 1)) (j : Fin (n + 2)) (i : Fin (n + 1)) :
    Spec.map (CommRingCat.ofHom
        (letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter t)
         letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t j))
         (restrictAlgHom (pullback.fst f f ≫ f) (𝒲.inter_le_inter_face t j)).toRingHom)) ≫
      (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 (𝒲.face t j)).isoSpec.inv ≫
        (pullback f f).homOfLE (𝒲.inter_le (𝒲.face t j) i)
    = (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 t).isoSpec.inv ≫
        (pullback f f).homOfLE (𝒲.inter_le t (j.succAbove i)) := by
  exact specMap_isoSpec_inv_homOfLE _ _ (𝒲.inter_le_inter_face t j) _ _

variable (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)

theorem chart_comp_eq (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f) {n : ℕ} (s : 𝒲.Idx n) (j : Fin (n + 1)) :
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
        (pullback f f).homOfLE (𝒲.inter_le s j) ≫ m (s.1 j)) ≫ f
      = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(pullback f f, 𝒲.inter s))) := by
  rw [Category.assoc, Category.assoc, hmf, Scheme.homOfLE_ι_assoc,
    ← fromSpec_comp_eq (pullback.fst f f ≫ f) (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s),
    IsAffineOpen.isoSpec_inv_ι_assoc]

variable {T : Type u} [CommRing T] (π : T' →+* T)
  {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (g : A₀ ⟶ A)

omit [IsSeparated (pullback.fst f f ≫ f)] in

theorem isPullback_productLift (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π))) :
    IsPullback
      (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]))
      (pullback.fst f₀ f₀ ≫ f₀) (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom π)) := by

  have hO : IsPullback (pullback.snd f₀ f₀ ≫ g) (pullback.fst f₀ f₀) f (g ≫ f) := by
    rw [hg.w]
    exact IsPullback.paste_horiz (IsPullback.of_hasPullback f₀ f₀).flip hg
  have hA : IsPullback
      (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
        (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]))
      (pullback.fst f₀ f₀) (pullback.fst f f) g := by
    refine (IsPullback.paste_horiz_iff (IsPullback.of_hasPullback f f).flip (pullback.lift_fst _ _ _)).mp ?_
    rw [pullback.lift_snd]
    exact hO
  exact IsPullback.paste_vert hA hg

theorem chart_comp_eq_mod (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (hmμ : ∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g)
    {n : ℕ} (s : 𝒲.Idx n) (j j' : Fin (n + 1)) :
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(pullback f f, 𝒲.inter s))))) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le s j) ≫ m (s.1 j))
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(pullback f f, 𝒲.inter s))))) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le s j') ≫ m (s.1 j')) := by
  set μ := pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
    (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) with hμdef

  have key : ∀ j : Fin (n + 1), (μ ∣_ 𝒲.inter s) ≫ (pullback f f).homOfLE (𝒲.inter_le s j) ≫ m (s.1 j)
      = (μ ⁻¹ᵁ 𝒲.inter s).ι ≫
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by
    intro j
    have hres : (μ ∣_ 𝒲.inter s) ≫ (pullback f f).homOfLE (𝒲.inter_le s j)
        = (pullback f₀ f₀).homOfLE (μ.preimage_mono (𝒲.inter_le s j)) ≫ (μ ∣_ 𝒲.U (s.1 j)) := by
      rw [← cancel_mono (𝒲.U (s.1 j)).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc,
        morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    rw [← Category.assoc, hres, Category.assoc, hmμ (s.1 j), Scheme.homOfLE_ι_assoc]
  exact specMap_mk_comp_isoSpec_inv_comp_eq π hπ hker (pullback.fst f f ≫ f) (pullback.fst f₀ f₀ ≫ f₀) μ
    (isPullback_productLift f π f₀ g hg) (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s)
    _ _ ((key j).trans (key j').symm)

omit [IsSeparated (pullback.fst f f ≫ f)] in

theorem isPullback_specialFibre [IsLocalRing T'] (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (i₀ : Ak ⟶ A₀)
    (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    IsPullback (i₀ ≫ g) fk f (Spec.map (CommRingCat.ofHom (residue T'))) := by
  have h := IsPullback.paste_horiz hi₀ hg
  rwa [← Spec.map_comp, show CommRingCat.ofHom π ≫ CommRingCat.ofHom ρ = CommRingCat.ofHom (residue T') from by
    rw [← CommRingCat.ofHom_comp, hρ]] at h

end Charts
section Sigma

variable {T' : Type u} [CommRing T'] [IsLocalRing T'] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
  [IsSeparated (pullback.fst f f ≫ f)] (𝒲 : (pullback f f).OrderedAffineCover)
  {Pk : Scheme.{u}} (bk : Pk ⟶ pullback f f) [IsAffineHom bk]
  (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))

theorem sigma_restrict (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(pullback f f, 𝒲.inter s)),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(pullback f f, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)
    {n : ℕ} (t : 𝒲.Idx (n + 1)) (j : Fin (n + 2))
    (x : letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t j))
         (ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter (𝒲.face t j))) :
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter t)
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t j))
    σ t (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom (pullback.fst f f ≫ f) (𝒲.inter_le_inter_face t j)) x)
      = (Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face t j :
            (𝒲.comap bk).inter t ≤ (𝒲.comap bk).inter (𝒲.face t j))).op).hom (σ (𝒲.face t j) x) := by
  letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter t)
  letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t j))
  letI := algebraOfHom yk ((𝒲.comap bk).inter t)
  letI := algebraOfHom yk ((𝒲.comap bk).inter (𝒲.face t j))
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]; exact (map_zero _).symm
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]; exact (map_add _ _ _).symm
  | tmul a c =>
    have hsplit : ∀ (B : Type u) [CommRing B] [Algebra T' B] (a : ResidueField T') (b : B),
        a ⊗ₜ[T'] b = (a ⊗ₜ[T'] (1 : B)) * ((1 : ResidueField T') ⊗ₜ[T'] b) := by
      intro B _ _ a b
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, hsplit, map_mul, hσ₂, hσ₁, hsplit, map_mul, hσ₂, hσ₁]
    refine Eq.trans ?_ (map_mul _ _ _).symm
    congr 1
    ·
      change (yk.appLE ⊤ ((𝒲.comap bk).inter t) le_top).hom _
        = (yk.appLE ⊤ ((𝒲.comap bk).inter (𝒲.face t j)) le_top ≫ Pk.presheaf.map (homOfLE _).op).hom _
      rw [Scheme.Hom.appLE_map]
    ·
      change (bk.app (𝒲.inter t) ≫ Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk t)).op).hom
          (((pullback f f).presheaf.map (homOfLE (𝒲.inter_le_inter_face t j)).op).hom c)
        = (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk (𝒲.face t j))).op ≫
            Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face t j :
              (𝒲.comap bk).inter t ≤ (𝒲.comap bk).inter (𝒲.face t j))).op).hom ((bk.app (𝒲.inter (𝒲.face t j))).hom c)
      change ((pullback f f).presheaf.map (homOfLE (𝒲.inter_le_inter_face t j)).op ≫ bk.app (𝒲.inter t) ≫
          Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk t)).op).hom c = _
      rw [← Category.assoc, Scheme.Hom.naturality, Category.assoc, ← Functor.map_comp, ← Functor.map_comp]
      rfl

end Sigma

section ChartsGen

variable {T' : Type u} [CommRing T'] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
  [IsSeparated (pullback.fst f f ≫ f)] (𝒲 : (pullback f f).OrderedAffineCover)
  (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)

theorem chart_comp_eq' (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f) {n : ℕ} (s : 𝒲.Idx n)
    (x : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x) :
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
        (pullback f f).homOfLE hx ≫ m x) ≫ f
      = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(pullback f f, 𝒲.inter s))) := by
  rw [Category.assoc, Category.assoc, hmf, Scheme.homOfLE_ι_assoc,
    ← fromSpec_comp_eq (pullback.fst f f ≫ f) (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s),
    IsAffineOpen.isoSpec_inv_ι_assoc]

variable {T : Type u} [CommRing T] (π : T' →+* T)
  {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (g : A₀ ⟶ A)

theorem chart_comp_eq_mod' (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (hmμ : ∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g)
    {n : ℕ} (s : 𝒲.Idx n) (x y : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x) (hy : 𝒲.inter s ≤ 𝒲.U y) :
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(pullback f f, 𝒲.inter s))))) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫ (pullback f f).homOfLE hx ≫ m x)
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(pullback f f, 𝒲.inter s))))) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫ (pullback f f).homOfLE hy ≫ m y) := by
  set μ := pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
    (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition]) with hμdef
  have key : ∀ (x : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x), (μ ∣_ 𝒲.inter s) ≫ (pullback f f).homOfLE hx ≫ m x
      = (μ ⁻¹ᵁ 𝒲.inter s).ι ≫
        (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g := by
    intro x hx
    have hres : (μ ∣_ 𝒲.inter s) ≫ (pullback f f).homOfLE hx
        = (pullback f₀ f₀).homOfLE (μ.preimage_mono hx) ≫ (μ ∣_ 𝒲.U x) := by
      rw [← cancel_mono (𝒲.U x).ι, Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι, Category.assoc,
        morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
    rw [← Category.assoc, hres, Category.assoc, hmμ x, Scheme.homOfLE_ι_assoc]
  exact specMap_mk_comp_isoSpec_inv_comp_eq π hπ hker (pullback.fst f f ≫ f) (pullback.fst f₀ f₀ ≫ f₀) μ
    (isPullback_productLift f π f₀ g hg) (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s)
    _ _ ((key x hx).trans (key y hy).symm)

end ChartsGen

end K2alphaO1

namespace K2alphaBody

theorem exists_pointDerivations_pi {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R] (ev : R →+* k)
    {W : Type w} [AddCommGroup W] [Module k W]
    {S : Type x} (M : S → Type y) (N : S → Type z)
    [∀ s, AddCommGroup (M s)] [∀ s, Module k (M s)] [∀ s, AddCommGroup (N s)] [∀ s, Module k (N s)]
    (L : ∀ s, M s →ₗ[k] N s) (δ : ∀ s, ↥(Algebra.PointDerivations k R ev (W →ₗ[k] M s))) :
    ∃ c : ↥(Algebra.PointDerivations k R ev (W →ₗ[k] (∀ s, N s))),
      ∀ (a : R) (ω : W) (s : S), (c : R →ₗ[k] (W →ₗ[k] (∀ s, N s))) a ω s = L s ((δ s : R →ₗ[k] (W →ₗ[k] M s)) a ω) := by
  let cξ : R → (W →ₗ[k] (∀ s, N s)) := fun a => LinearMap.pi (fun s => (L s).comp ((δ s : R →ₗ[k] (W →ₗ[k] M s)) a))
  have cξ_apply : ∀ a ω s, cξ a ω s = L s ((δ s : R →ₗ[k] (W →ₗ[k] M s)) a ω) := fun a ω s => rfl
  let clin : R →ₗ[k] (W →ₗ[k] (∀ s, N s)) :=
    { toFun := cξ
      map_add' := fun a a' => by
        ext ω s
        rw [LinearMap.add_apply, Pi.add_apply, cξ_apply, cξ_apply, cξ_apply, map_add, LinearMap.add_apply, map_add]
      map_smul' := fun r a => by
        ext ω s
        rw [LinearMap.smul_apply, Pi.smul_apply, cξ_apply, cξ_apply, map_smul, LinearMap.smul_apply, RingHom.id_apply, map_smul] }
  have hcder : clin ∈ Algebra.PointDerivations k R ev (W →ₗ[k] (∀ s, N s)) := by
    intro a a'
    ext ω s
    show cξ (a * a') ω s = _
    rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    show cξ (a * a') ω s = _ • cξ a' ω s + _ • cξ a ω s
    rw [cξ_apply, cξ_apply, cξ_apply, (δ s).2 a a', LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply,
      map_add, map_smul, map_smul]
  exact ⟨⟨clin, hcder⟩, fun a ω s => cξ_apply a ω s⟩

theorem sum_three_coords_eq_zero
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type u) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{u}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    (w : Fin (1 + 2) → (Spec (CommRingCat.of C) ⟶ Y))
    (hw : ∀ i, w i ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hagree : ∀ i j, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w i
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w j)
    {Ak : Scheme.{u}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)
    (D : Fin (1 + 2) → Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (hD : ∀ r : Fin (1 + 2), IsTangentCoordsOfPairAt I V ι C (w (r.succAbove 0)) (w (r.succAbove 1)) xk Lk ak Ue (D r))
    (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V) :
    ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0 := by
  have hD0 : IsTangentCoordsOfPairAt I V ι C (w 1) (w 2) xk Lk ak Ue (D 0) := hD 0
  have hD1 : IsTangentCoordsOfPairAt I V ι C (w 0) (w 2) xk Lk ak Ue (D 1) := hD 1
  have hD2 : IsTangentCoordsOfPairAt I V ι C (w 0) (w 1) xk Lk ak Ue (D 2) := hD 2
  have hadd := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI C qY (w 0) (w 1) (w 2)
    (hw 0) (hw 1) (hw 2) (hagree 0 1) (hagree 1 2) xk Lk ak hak Ue hUe e₁ he₁ (D 2) (D 0) (D 1) hD2 hD0 hD1
  have h3 : D 1 a ξ = D 2 a ξ + D 0 a ξ := by rw [hadd]; rfl
  show ∑ r : Fin 3, ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0
  rw [Fin.sum_univ_three]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, one_zsmul, neg_one_zsmul, h3]
  rw [show ((-1 : ℤ) ^ 2) = 1 by norm_num, one_zsmul]
  abel

theorem coords_restrict_face
    {T' : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T'))
    [IsSeparated (pullback.fst f f ≫ f)] (𝒲 : (pullback f f).OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (ak : Ak ⟶ A) (Ue : Ak.Opens)
    (t : 𝒲.Idx (1 + 1)) (r : Fin (1 + 2))
    (hflat : letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter t); Module.Flat T' Γ(pullback f f, 𝒲.inter t))
    (δr : letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t r))
      Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(pullback f f, 𝒲.inter (𝒲.face t r)))))
    (hδr : letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t r))
      IsTangentCoordsOfPairAt I V ι Γ(pullback f f, 𝒲.inter (𝒲.face t r))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le (𝒲.face t r) 0) ≫ m ((𝒲.face t r).1 0))
        ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le (𝒲.face t r) 1) ≫ m ((𝒲.face t r).1 1))
        fk Lk ak Ue δr) :
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter t)
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t r))
    IsTangentCoordsOfPairAt I V ι Γ(pullback f f, 𝒲.inter t)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 t).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le t (r.succAbove 0)) ≫ m (t.1 (r.succAbove 0)))
      ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 t).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le t (r.succAbove 1)) ≫ m (t.1 (r.succAbove 1)))
      fk Lk ak Ue
      (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom (pullback.fst f f ≫ f) (𝒲.inter_le_inter_face t r))).toLinearMap ∘ₗ δr a) := by
  letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter t)
  letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t r))
  haveI := hflat
  have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat I hI hsmall V ι hι hιI
    Γ(pullback f f, 𝒲.inter (𝒲.face t r)) Γ(pullback f f, 𝒲.inter t)
    (restrictAlgHom (pullback.fst f f ≫ f) (𝒲.inter_le_inter_face t r)) _ _ fk Lk ak Ue _ hδr
  have hw : ∀ i : Fin (0 + 1 + 1),
      Spec.map (CommRingCat.ofHom (restrictAlgHom (pullback.fst f f ≫ f) (𝒲.inter_le_inter_face t r)).toRingHom) ≫
        ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 (𝒲.face t r)).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le (𝒲.face t r) i) ≫ m ((𝒲.face t r).1 i))
        = (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 t).isoSpec.inv ≫
          (pullback f f).homOfLE (𝒲.inter_le t (r.succAbove i)) ≫ m (t.1 (r.succAbove i)) := by
    intro i
    rw [← Category.assoc ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 t).isoSpec.inv),
      ← K2alphaO1.specMap_restrict_isoSpec_inv_homOfLE f 𝒲 t r i]
    try simp only [Category.assoc]
    rfl
  rw [hw 0, hw 1] at h
  exact h

theorem main
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated (pullback.fst f f ≫ f)]
    (𝒲 : (pullback f f).OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f)
    (hmμ : ∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g)

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    {Pk : Scheme.{u}} (bk : Pk ⟶ pullback f f) [IsAffineHom bk] (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(pullback f f, 𝒲.inter s)),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(pullback f f, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)

    (p₁ p₂ : Pk ⟶ Ak)
    (hp₁ : p₁ ≫ i₀ ≫ g = bk ≫ pullback.fst f f) (hp₁k : p₁ ≫ fk = yk)
    (hp₂ : p₂ ≫ i₀ ≫ g = bk ≫ pullback.snd f f) (hp₂k : p₂ ≫ fk = yk)
    (hPk : IsPullback p₁ p₂ fk fk)
    (ek : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak)
    (hek : ek ≫ i₀ ≫ g = Spec.map (CommRingCat.ofHom (residue T')) ≫ e.1) (hekk : ek ≫ fk = 𝟙 _)
    (iX : Ak ⟶ Pk) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 Ak) (hiX₂ : iX ≫ p₂ = fk ≫ ek)
    (hiXP : iX ≫ bk = (i₀ ≫ g) ≫ pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (iY : Ak ⟶ Pk) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fk ≫ ek) (hiY₂ : iY ≫ p₂ = 𝟙 Ak)
    (hiYP : iY ≫ bk = (i₀ ≫ g) ≫ pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
 :
    letI := algebraOfHom fk Ue
    ∃ c : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 1)),
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
        ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk Lk (i₀ ≫ g) Ue cs ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 1 (c.1 a ξ) = 0) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iX) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iX) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iX t)).op).hom
              ((iX.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iY) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iY) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iY t)).op).hom
              ((iY.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) := by
  classical

  have slot_flat : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      Module.Flat T' Γ(pullback f f, 𝒲.inter s) := fun s => K2alphaO1.flat_sections f 𝒲 hs s
  have slot_over : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
          (pullback f f).homOfLE hx ≫ m x) ≫ f
        = Spec.map (CommRingCat.ofHom (algebraMap T' Γ(pullback f f, 𝒲.inter s))) :=
    fun s x hx => K2alphaO1.chart_comp_eq' f 𝒲 m hmf s x hx
  have slot_agree : ∀ {n : ℕ} (s : 𝒲.Idx n) (x y : 𝒲.ι) (hx : 𝒲.inter s ≤ 𝒲.U x) (hy : 𝒲.inter s ≤ 𝒲.U y),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(pullback f f, 𝒲.inter s))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫ (pullback f f).homOfLE hx ≫ m x)
        = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker π).map (algebraMap T' Γ(pullback f f, 𝒲.inter s))))) ≫
          ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫ (pullback f f).homOfLE hy ≫ m y) :=
    fun s x y hx hy => K2alphaO1.chart_comp_eq_mod' f 𝒲 m π f₀ L₀ g hπ hker hg hmμ s x y hx hy

  have hak : IsPullback (i₀ ≫ g) fk f (Spec.map (CommRingCat.ofHom (residue T'))) := by
    have := hi₀.paste_horiz hg
    rwa [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ] at this

  have hδ : ∀ s : 𝒲.Idx 1,
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom fk Ue
      ∃ δ : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] Γ(pullback f f, 𝒲.inter s)))),
        IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
          ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
            (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
          ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
            (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
          fk Lk (i₀ ≫ g) Ue (fun a => δ.1 a) := by
    intro s
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    haveI := slot_flat s
    exact AlgebraicGeometry.SmallExtension.exists_pointDerivations_isTangentCoordsOfPairAt_of_flat
      (RingHom.ker π) hI hsmall V ι hι hιI Γ(pullback f f, 𝒲.inter s) f
      _ (slot_over s (s.1 0) (𝒲.inter_le s 0)) _ (slot_over s (s.1 1) (𝒲.inter_le s 1))
      (slot_agree s (s.1 0) (s.1 1) (𝒲.inter_le s 0) (𝒲.inter_le s 1))
      fk Lk (i₀ ≫ g) hak Ue hUe e₁ he₁
  choose δ hδ using hδ

  subst hp₁k

  have σlin : ∀ (n : ℕ) (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      ∃ L : ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) →ₗ[ResidueField T']
          (OModulePresheaf.unit (p₁ ≫ fk)).obj ((𝒲.comap bk).inter s), ∀ x, L x = σ s x := by
    intro n s
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
    letI := algebraOfHom (p₁ ≫ fk) ((𝒲.comap bk).inter s)
    refine ⟨{ toFun := fun x => σ s x, map_add' := fun x y => map_add (σ s) x y, map_smul' := fun r x => ?_ }, fun x => rfl⟩
    show σ s (r • x) = r • σ s x
    rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_mul,
      hσ₂ s r, ← Algebra.smul_def]
  choose σL hσL using σlin
  have hσsmul : ∀ (n : ℕ) (s : 𝒲.Idx n) (r : ResidueField T')
      (x : letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s); (ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      σ s (r • x) = (r • (show (OModulePresheaf.unit (p₁ ≫ fk)).obj ((𝒲.comap bk).inter s) from σ s x)) := by
    intro n s r x
    rw [← hσL, ← hσL, map_smul]

  letI := algebraOfHom fk Ue
  obtain ⟨c, hc0⟩ := exists_pointDerivations_pi
    ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
    (fun s : 𝒲.Idx 1 => letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      (ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))
    (fun s : 𝒲.Idx 1 => (OModulePresheaf.unit (p₁ ≫ fk)).obj ((𝒲.comap bk).inter s))
    (fun s => σL 1 s) (fun s => δ s)
  have hc1 : ∀ a ξ s, c.1 a ξ s = σ s ((δ s).1 a ξ) := fun a ξ s => (hc0 a ξ s).trans (hσL 1 s _)

  have hO1 : (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
        ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk Lk (i₀ ≫ g) Ue cs ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s) := by
    intro s
    exact ⟨fun a => (δ s).1 a, hδ s, fun a ξ => (hc1 a ξ s).symm⟩

  have hO2 : ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
      (OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 1 (c.1 a ξ) = 0 := by
    intro a ξ
    funext t
    rw [OModulePresheaf.d_apply, Pi.zero_apply]
    letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter t)

    let w : Fin (1 + 2) → (Spec (CommRingCat.of Γ(pullback f f, 𝒲.inter t)) ⟶ A) := fun x =>
      (Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 t).isoSpec.inv ≫
        (pullback f f).homOfLE (𝒲.inter_le t x) ≫ m (t.1 x)

    let D : ∀ r : Fin (1 + 2), Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T']
        ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter t))) := fun r a' =>
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter (𝒲.face t r))
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField T') (ResidueField T'))
          (restrictAlgHom (pullback.fst f f ≫ f) (𝒲.inter_le_inter_face t r))).toLinearMap ∘ₗ (δ (𝒲.face t r)).1 a'
    have hD : ∀ r : Fin (1 + 2), IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter t)
        (w (r.succAbove 0)) (w (r.succAbove 1)) fk Lk (i₀ ≫ g) Ue (D r) := fun r =>
      coords_restrict_face (RingHom.ker π) hI hsmall V ι hι hιI f 𝒲 m fk Lk (i₀ ≫ g) Ue t r (slot_flat t)
        (fun a' => (δ (𝒲.face t r)).1 a') (hδ (𝒲.face t r))
    have hsum : ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ = 0 :=
      sum_three_coords_eq_zero (RingHom.ker π) hI hsmall V ι hι hιI Γ(pullback f f, 𝒲.inter t) f w
        (fun i => slot_over t (t.1 i) (𝒲.inter_le t i)) (fun i j => slot_agree t (t.1 i) (t.1 j) (𝒲.inter_le t i) (𝒲.inter_le t j))
        fk Lk (i₀ ≫ g) hak Ue hUe e₁ he₁ D hD a ξ

    have hterm : ∀ r : Fin (1 + 2),
        (OModulePresheaf.unit (p₁ ≫ fk)).res ((𝒲.comap bk).inter_le_inter_face t r) (c.1 a ξ ((𝒲.comap bk).face t r))
          = σ t (D r a ξ) := by
      intro r
      show (Pk.presheaf.map (homOfLE ((𝒲.comap bk).inter_le_inter_face t r)).op).hom (c.1 a ξ (𝒲.face t r)) = _
      rw [hc1]
      exact (K2alphaO1.sigma_restrict f 𝒲 bk σ (p₁ ≫ fk) hσ₁ hσ₂ t r _).symm
    calc ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) •
            (OModulePresheaf.unit (p₁ ≫ fk)).res ((𝒲.comap bk).inter_le_inter_face t r) (c.1 a ξ ((𝒲.comap bk).face t r))
        = ∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • σ t (D r a ξ) := Finset.sum_congr rfl (fun r _ => by rw [hterm]; rfl)
      _ = σ t (∑ r : Fin (1 + 2), ((-1 : ℤ) ^ (r : ℕ)) • D r a ξ) := by
            rw [map_sum]; refine Finset.sum_congr rfl (fun r _ => ?_); rw [map_zsmul]
      _ = 0 := by rw [hsum, map_zero]

  have hO3 := GoodReductionJacobian.RelativeGroupLaw.exists_d_comap_slice_eq_of_obstruction_cocycle
    T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg e he hI ρ hρ V ι hι hιI 𝒲 m hmf hmμ fk Lk i₀ hi₀ Ue hUe e₁ he₁
    bk (p₁ ≫ fk) hbk σ hσ₁ hσ₂ p₁ p₂ hp₁ rfl hp₂ hp₂k hPk ek hek hekk iX hiX₁ hiX₂ hiXP iY hiY₁ hiY₂ hiYP c hO1
  exact ⟨c, hO1, hO2, hO3.1, hO3.2⟩

end K2alphaBody

theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [IsAlgClosed (ResidueField T')]
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    (hsmall : RingHom.ker π * maximalIdeal T' = ⊥)
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (L₀ : RelativeGroupLaw T f₀) (hc₀ : L₀.IsCommutative)
    (h₀ : AbelianSchemePropertyBundle T f₀)
    {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of T')) (hs : Smooth f) (hp : IsProper f)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom π)))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of T'))) f)
    (he : Spec.map (CommRingCat.ofHom π) ≫ e.1 = (L₀.one (𝟙 (Spec (CommRingCat.of T)))).1 ≫ g)

    (hI : RingHom.ker π ≤ maximalIdeal T')
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    (V : Type u) [AddCommGroup V] [Module (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    [Module (ResidueField T')ᵐᵒᵖ V] [IsCentralScalar (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars T' (RingHom.ker π))

    [IsSeparated (pullback.fst f f ≫ f)]
    (𝒲 : (pullback f f).OrderedAffineCover)
    (m : ∀ i : 𝒲.ι, (↑(𝒲.U i) : Scheme.{u}) ⟶ A)
    (hmf : ∀ i, m i ≫ f = (𝒲.U i).ι ≫ pullback.fst f f ≫ f)
    (hmμ : ∀ i, morphismRestrict (pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) (𝒲.U i) ≫ m i
        = ((pullback.lift (pullback.fst f₀ f₀ ≫ g) (pullback.snd f₀ f₀ ≫ g)
              (by rw [Category.assoc, Category.assoc, hg.w, ← Category.assoc, ← Category.assoc, pullback.condition])) ⁻¹ᵁ (𝒲.U i)).ι ≫
          (L₀.mul (pullback.fst f₀ f₀ ≫ f₀) ⟨pullback.fst f₀ f₀, rfl⟩ ⟨pullback.snd f₀ f₀, pullback.condition.symm⟩).1 ≫ g)

    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') fk)
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ)))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{u})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

    {Pk : Scheme.{u}} (bk : Pk ⟶ pullback f f) [IsAffineHom bk] (yk : Pk ⟶ Spec (CommRingCat.of (ResidueField T')))
    (hbk : IsPullback bk yk (pullback.fst f f ≫ f) (Spec.map (CommRingCat.ofHom (residue T'))))
    (σ : ∀ {n : ℕ} (s : 𝒲.Idx n),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s)) ≃+* Γ(Pk, (𝒲.comap bk).inter s))
    (hσ₁ : ∀ {n : ℕ} (s : 𝒲.Idx n) (x : Γ(pullback f f, 𝒲.inter s)),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      σ s ((1 : ResidueField T') ⊗ₜ[T'] x) =
        (Pk.presheaf.map (homOfLE (𝒲.comap_inter_le bk s)).op).hom ((bk.app (𝒲.inter s)).hom x))
    (hσ₂ : ∀ {n : ℕ} (s : 𝒲.Idx n) (a : ResidueField T'),
      letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
      letI := algebraOfHom yk ((𝒲.comap bk).inter s)
      σ s (a ⊗ₜ[T'] (1 : Γ(pullback f f, 𝒲.inter s))) = algebraMap (ResidueField T') Γ(Pk, (𝒲.comap bk).inter s) a)

    (p₁ p₂ : Pk ⟶ Ak)
    (hp₁ : p₁ ≫ i₀ ≫ g = bk ≫ pullback.fst f f) (hp₁k : p₁ ≫ fk = yk)
    (hp₂ : p₂ ≫ i₀ ≫ g = bk ≫ pullback.snd f f) (hp₂k : p₂ ≫ fk = yk)
    (hPk : IsPullback p₁ p₂ fk fk)
    (ek : Spec (CommRingCat.of (ResidueField T')) ⟶ Ak)
    (hek : ek ≫ i₀ ≫ g = Spec.map (CommRingCat.ofHom (residue T')) ≫ e.1) (hekk : ek ≫ fk = 𝟙 _)
    (iX : Ak ⟶ Pk) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 Ak) (hiX₂ : iX ≫ p₂ = fk ≫ ek)
    (hiXP : iX ≫ bk = (i₀ ≫ g) ≫ pullback.lift (𝟙 A) (f ≫ e.1) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id]))
    (iY : Ak ⟶ Pk) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fk ≫ ek) (hiY₂ : iY ≫ p₂ = 𝟙 Ak)
    (hiYP : iY ≫ bk = (i₀ ≫ g) ≫ pullback.lift (f ≫ e.1) (𝟙 A) (by rw [Category.id_comp, Category.assoc, e.2, Category.comp_id])) :
    letI := algebraOfHom fk Ue
    ∃ c : ↥(Algebra.PointDerivations (ResidueField T') Γ(Ak, Ue)
          ((Ue.topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField T'))).hom).hom)
          (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (OModulePresheaf.unit (p₁ ≫ fk)).cochain (𝒲.comap bk) 1)),
      (∀ s : 𝒲.Idx 1,
        letI := algebraOfHom (pullback.fst f f ≫ f) (𝒲.inter s)
        ∃ cs : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] ((ResidueField T') ⊗[T'] Γ(pullback f f, 𝒲.inter s))),
          IsTangentCoordsOfPairAt (RingHom.ker π) V ι Γ(pullback f f, 𝒲.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter (pullback.fst f f ≫ f) 𝒲 s).isoSpec.inv ≫
              (pullback f f).homOfLE (𝒲.inter_le s 1) ≫ m (s.1 1))
            fk Lk (i₀ ≫ g) Ue cs ∧
          ∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V), σ s (cs a ξ) = c.1 a ξ s) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        (OModulePresheaf.unit (p₁ ≫ fk)).d (𝒲.comap bk) 1 (c.1 a ξ) = 0) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iX) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iX) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iX t)).op).hom
              ((iX.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) ∧
      (∀ (a : Γ(Ak, Ue)) (ξ : Module.Dual (ResidueField T') V),
        ∃ b : (OModulePresheaf.unit fk).cochain ((𝒲.comap bk).comap iY) 0,
          (OModulePresheaf.unit fk).d ((𝒲.comap bk).comap iY) 0 b = fun t =>
            (Ak.presheaf.map (homOfLE ((𝒲.comap bk).comap_inter_le iY t)).op).hom
              ((iY.app ((𝒲.comap bk).inter t)).hom (c.1 a ξ t))) :=
  K2alphaBody.main T' T π hπ hker hsmall f₀ L₀ hc₀ h₀ f hs hp g hg e he hI ρ hρ V ι hι hιI 𝒲 m hmf hmμ fk Lk i₀ hi₀ Ue hUe e₁ he₁
    bk yk hbk σ hσ₁ hσ₂ p₁ p₂ hp₁ hp₁k hp₂ hp₂k hPk ek hek hekk iX hiX₁ hiX₂ hiXP iY hiY₁ hiY₂ hiYP

end S_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_pointDerivations_obstruction_cocycle_of_local_lifts (solution)
