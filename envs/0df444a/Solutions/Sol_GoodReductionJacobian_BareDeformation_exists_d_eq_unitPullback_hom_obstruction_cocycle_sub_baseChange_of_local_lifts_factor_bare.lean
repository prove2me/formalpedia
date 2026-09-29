-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e4e0db37-2b40-5812-a273-ee24cacf1675

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_SquareZeroDeformation
import Definitions.Def_AlgebraicGeometry_SquareZeroRelTangent
import Definitions.Def_AlgebraicGeometry_SmallExtensionPairTangent
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPair
import Definitions.Def_AlgebraicGeometry_SmallExtensionTangentCoords
import Definitions.Def_AlgebraicGeometry_TangentCoordsOfPairAt
import Definitions.Def_Algebra_PointDerivations
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_factor_bare
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_add
import Theorems.Thm_AlgebraicGeometry_SmallExtension_isTangentCoordsOfPairAt_comp_of_flat
import Theorems.Thm_AlgebraicGeometry_SmallExtension_exists_isTangentCoordsOfPairAt
import Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_exists_ringEquiv_tensor_sections_baseChange_inter
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_factor_inf_of_local_lifts_factor_bare
import Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_map_restrictAlgHom_eq_presheaf_map_of_tmul_eq

import Theorems.Thm_GoodReductionJacobian_BareDeformation_map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
import Theorems.Thm_GoodReductionJacobian_BareDeformation_isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped Quaternion TensorProduct NumberField

namespace PVBK1b

p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover AlgebraicGeometry.SmallExtension"

theorem spec_map_comp_isoSpec_inv {Y : Scheme.{0}} {U V : Y.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ U) :
    Spec.map (Y.presheaf.map (homOfLE e).op) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ Y.homOfLE e := by
  rw [← cancel_mono U.ι, Category.assoc, Category.assoc, IsAffineOpen.isoSpec_inv_ι, Scheme.homOfLE_ι,
    IsAffineOpen.isoSpec_inv_ι]
  exact hU.map_fromSpec hV (homOfLE e).op

theorem fromSpec_comp_eq {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

theorem isoSpec_inv_comp_eq {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.isoSpec.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  rw [← Category.assoc, IsAffineOpen.isoSpec_inv_ι]; exact fromSpec_comp_eq f hU

theorem flat_sections {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem isPullback_comp_of_factor {B B₁ : Type} [CommRing B] [IsLocalRing B] [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    {A₁ X₀ X Xκ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (.of B₁))
    (f₀ : X₀ ⟶ Spec (.of B)) (g₀ : A₁ ⟶ X₀) (hg₀ : IsPullback g₀ f₁ f₀ (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (f : X ⟶ Spec (.of B)) (g : A₁ ⟶ X) (hg : IsPullback g f₁ f (Spec.map (CommRingCat.ofHom (algebraMap B B₁))))
    (bκ : Xκ ⟶ X₀) (pκ : Xκ ⟶ Spec (.of (ResidueField B)))
    (hκ : IsPullback bκ pκ f₀ (Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B)))))
    (jκ : Xκ ⟶ A₁) (hjκ : jκ ≫ g₀ = bκ) :
    IsPullback (jκ ≫ g) pκ f (Spec.map (CommRingCat.ofHom (residue B))) := by
  have hk : RingHom.ker (algebraMap B B₁) ≤ RingHom.ker (residue B) := by rwa [ker_residue]
  let ρ : B₁ →+* ResidueField B := RingHom.liftOfSurjective (algebraMap B B₁) hπ ⟨residue B, hk⟩
  have hρ : ρ.comp (algebraMap B B₁) = residue B := RingHom.liftOfRightInverse_comp _ _ _ _
  have e1 : Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁)) =
      Spec.map (CommRingCat.ofHom (residue B)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  have e2 : Spec.map (CommRingCat.ofHom (algebraMap B (ResidueField B))) = Spec.map (CommRingCat.ofHom (residue B)) := rfl
  haveI : IsClosedImmersion (Spec.map (CommRingCat.ofHom (algebraMap B B₁))) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have hcomm : jκ ≫ f₁ = pκ ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap B B₁))), Category.assoc, Category.assoc, e1,
      ← hg₀.w, ← Category.assoc, hjκ, hκ.w, e2]
  have big : IsPullback (jκ ≫ g₀) pκ f₀ (Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁))) := by
    rw [hjκ, e1, ← e2]; exact hκ
  have sqL : IsPullback jκ pκ f₁ (Spec.map (CommRingCat.ofHom ρ)) := IsPullback.of_right big hcomm hg₀
  have := IsPullback.paste_horiz sqL hg
  rwa [e1] at this

theorem specMap_mk_comp_eq_of_isTangentCoordsOfPairAt {T' : Type} [CommRing T'] [IsLocalRing T'] (I : Ideal T')
    (V : Type) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (C : Type) [CommRing C] [Algebra T' C]
    {Y : Scheme.{0}} (u v : Spec (CommRingCat.of C) ⟶ Y)
    {Ak : Scheme.{0}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (Ue : Ak.Opens)
    (c : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C)))
    (h : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue c) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v := by
  obtain ⟨w₀, hw₀, w₁, ⟨ϑ, _, φ, hu, hv, -⟩, -, -⟩ := h
  rw [← hu, ← hv, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp]
  have : (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairFst I C) =
      (Ideal.Quotient.mk (I.map (algebraMap T' C))).comp (pairSnd I C) := RingHom.ext fun x => x.2
  rw [this]

p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover AlgebraicGeometry.SmallExtension"

theorem sort_two_eq_one {α : Type} [LinearOrder α] (f : Fin 2 → α) (h : f 0 < f 1) : Tuple.sort f = 1 := by
  symm
  rw [Tuple.eq_sort_iff]
  refine ⟨?_, ?_⟩
  · refine (Fin.strictMono_iff_lt_succ.2 (fun k => ?_)).monotone
    fin_cases k; simpa using h
  · intro i j hij hfij
    exfalso
    have hinj : Function.Injective f := fun a b hab => by
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_lt h)
      · exact absurd hab (ne_of_gt h)
      · rfl
    exact absurd (hinj (by simpa using hfij)) (ne_of_lt hij)

theorem sort_two_eq_swap {α : Type} [LinearOrder α] (f : Fin 2 → α) (h : f 1 < f 0) :
    Tuple.sort f = Equiv.swap 0 1 := by
  symm
  rw [Tuple.eq_sort_iff]
  refine ⟨?_, ?_⟩
  · refine (Fin.strictMono_iff_lt_succ.2 (fun k => ?_)).monotone
    fin_cases k; simpa using h
  · intro i j hij hfij
    exfalso
    have hinj : Function.Injective f := fun a b hab => by
      fin_cases a <;> fin_cases b
      · rfl
      · exact absurd hab (ne_of_gt h)
      · exact absurd hab (ne_of_lt h)
      · rfl
    exact absurd ((Equiv.swap (0 : Fin 2) 1).injective (hinj hfij)) (ne_of_lt hij)

theorem sortIdx_of_lt {X Y : Scheme.{0}} (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (s : 𝒲.Idx 1) (h : lam (s.1 0) < lam (s.1 1)) (hinj : Function.Injective (lam ∘ s.1)) :
    (𝒲.sortIdx 𝒦 lam s hinj).1 0 = lam (s.1 0) ∧ (𝒲.sortIdx 𝒦 lam s hinj).1 1 = lam (s.1 1) ∧
      Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) = 1 := by
  have hs : Tuple.sort (lam ∘ s.1) = 1 := sort_two_eq_one _ h
  refine ⟨?_, ?_, ?_⟩
  · rw [sortIdx_val, hs]; rfl
  · rw [sortIdx_val, hs]; rfl
  · rw [hs]; exact Equiv.Perm.sign_one

theorem sortIdx_of_gt {X Y : Scheme.{0}} (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (s : 𝒲.Idx 1) (h : lam (s.1 1) < lam (s.1 0)) (hinj : Function.Injective (lam ∘ s.1)) :
    (𝒲.sortIdx 𝒦 lam s hinj).1 0 = lam (s.1 1) ∧ (𝒲.sortIdx 𝒦 lam s hinj).1 1 = lam (s.1 0) ∧
      Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) = -1 := by
  have hs : Tuple.sort (lam ∘ s.1) = Equiv.swap 0 1 := sort_two_eq_swap _ h
  refine ⟨?_, ?_, ?_⟩
  · rw [sortIdx_val, hs]; rfl
  · rw [sortIdx_val, hs]; rfl
  · rw [hs]; exact Equiv.Perm.sign_swap (by decide)

theorem injective_of_ne {X Y : Scheme.{0}} (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (s : 𝒲.Idx 1) (h : lam (s.1 0) ≠ lam (s.1 1)) : Function.Injective (lam ∘ s.1) := by
  intro a b hab
  fin_cases a <;> fin_cases b
  · rfl
  · exact absurd hab h
  · exact absurd hab.symm h
  · rfl

theorem not_injective_of_eq {X Y : Scheme.{0}} (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι)
    (s : 𝒲.Idx 1) (h : lam (s.1 0) = lam (s.1 1)) : ¬ Function.Injective (lam ∘ s.1) := by
  intro hinj
  exact absurd (hinj (show (lam ∘ s.1) 0 = (lam ∘ s.1) 1 from h)) (by decide)

theorem inter_one_eq {X : Scheme.{0}} (𝒦 : X.OrderedAffineCover) (t : 𝒦.Idx 1) :
    𝒦.inter t = 𝒦.U (t.1 0) ⊓ 𝒦.U (t.1 1) := by
  apply le_antisymm
  · exact le_inf (𝒦.inter_le t 0) (𝒦.inter_le t 1)
  · refine le_iInf fun j => ?_
    fin_cases j
    · exact inf_le_left
    · exact inf_le_right

theorem homOfLE_comp_idx_eq {X Y : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (m : ∀ k, (↑(U k) : Scheme.{0}) ⟶ Y)
    {k k' : ι} (h : k = k') {W : X.Opens} (h₁ : W ≤ U k) (h₂ : W ≤ U k') :
    X.homOfLE h₁ ≫ m k = X.homOfLE h₂ ≫ m k' := by
  subst h; rfl

section AtTorsor

variable {T' : Type} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    (I : Ideal T') (hI : I ≤ maximalIdeal T') (hsmall : I * maximalIdeal T' = ⊥)
    (V : Type) [AddCommGroup V] [Module (ResidueField T') V] [Module (ResidueField T')ᵐᵒᵖ V]
    [IsCentralScalar (ResidueField T') V] [Module.Finite (ResidueField T') V]
    [Module T' V] [IsScalarTower T' (ResidueField T') V]
    (ι : V →ₗ[T'] T') (hι : Function.Injective ι) (hιI : LinearMap.range ι = Submodule.restrictScalars T' I)
    (C : Type) [CommRing C] [Algebra T' C] [Module.Flat T' C]
    {Y : Scheme.{0}} (qY : Y ⟶ Spec (CommRingCat.of T'))
    {Ak : Scheme.{0}} (xk : Ak ⟶ Spec (CommRingCat.of (ResidueField T'))) (Lk : RelativeGroupLaw (ResidueField T') xk)
    (ak : Ak ⟶ Y) (hak : IsPullback ak xk qY (Spec.map (CommRingCat.ofHom (residue T'))))
    (Ue : Ak.Opens) (hUe : IsAffineOpen Ue)
    (e₁ : Spec (CommRingCat.of (ResidueField T')) ⟶ (Ue : Scheme.{0})) (he₁ : e₁ ≫ Ue.ι = (Lk.one (𝟙 _)).1)

include hI hsmall hι hιI hak hUe e₁ he₁

theorem at_self (u : Spec (CommRingCat.of C) ⟶ Y) (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C))) :
    IsTangentCoordsOfPairAt I V ι C u u xk Lk ak Ue 0 := by
  obtain ⟨c, hc⟩ := exists_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI C qY u hu xk Lk ak hak Ue hUe e₁ he₁ u hu rfl
  have h := isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI C qY u u u hu hu hu rfl rfl xk Lk ak hak Ue hUe e₁ he₁ c c c hc hc hc
  have hc0 : c = 0 := by
    funext a
    have := congrFun h a
    rw [Pi.add_apply] at this
    rw [Pi.zero_apply]
    exact left_eq_add.mp this
  rwa [hc0] at hc

theorem at_unique (u v : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    {D D' : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (hD : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue D)
    (hD' : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue D') : D = D' := by
  have h0 := at_self I hI hsmall V ι hι hιI C qY xk Lk ak hak Ue hUe e₁ he₁ v hv
  have h := isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI C qY u v v hu hv hv huv rfl xk Lk ak hak Ue hUe e₁ he₁ D 0 D' hD h0 hD'
  rw [add_zero] at h
  exact h.symm

theorem at_symm (u v : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    {D : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (hD : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue D) :
    IsTangentCoordsOfPairAt I V ι C v u xk Lk ak Ue (-D) := by
  obtain ⟨c, hc⟩ := exists_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI C qY v hv xk Lk ak hak Ue hUe e₁ he₁ u hu huv.symm
  have h0 := at_self I hI hsmall V ι hι hιI C qY xk Lk ak hak Ue hUe e₁ he₁ u hu
  have h := isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI C qY u v u hu hv hu huv huv.symm xk Lk ak hak Ue hUe e₁ he₁ D c 0 hD hc h0
  have : c = -D := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact h.symm
  rwa [this] at hc

theorem at_trans (u v w : Spec (CommRingCat.of C) ⟶ Y)
    (hu : u ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hv : v ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (hw : w ≫ qY = Spec.map (CommRingCat.ofHom (algebraMap T' C)))
    (huv : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ u
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v)
    (hvw : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ v
      = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map (algebraMap T' C)))) ≫ w)
    {D₁ D₂ : Γ(Ak, Ue) → (Module.Dual (ResidueField T') V →ₗ[ResidueField T'] (ResidueField T' ⊗[T'] C))}
    (h₁ : IsTangentCoordsOfPairAt I V ι C u v xk Lk ak Ue D₁)
    (h₂ : IsTangentCoordsOfPairAt I V ι C v w xk Lk ak Ue D₂) :
    IsTangentCoordsOfPairAt I V ι C u w xk Lk ak Ue (D₁ + D₂) := by
  obtain ⟨c, hc⟩ := exists_isTangentCoordsOfPairAt I hI hsmall V ι hι hιI C qY u hu xk Lk ak hak Ue hUe e₁ he₁ w hw (huv.trans hvw)
  have h := isTangentCoordsOfPairAt_add I hI hsmall V ι hι hιI C qY u v w hu hv hw huv hvw xk Lk ak hak Ue hUe e₁ he₁ D₁ D₂ c h₁ h₂ hc
  rwa [h] at hc

end AtTorsor

p2m_open "AlgebraicGeometry.Scheme.OrderedAffineCover AlgebraicGeometry.SmallExtension Opposite TopologicalSpace"

theorem map_id_app_map_app_eq {X Y : Scheme.{0}} (f : X ⟶ Y) {U U' : Y.Opens} (hUU : U' ≤ U)
    {W W'' : X.Opens} (e₁ : W'' ≤ f ⁻¹ᵁ U) (e₂ : W ≤ (𝟙 X) ⁻¹ᵁ W'') (e₃ : W ≤ f ⁻¹ᵁ U') (y : Γ(Y, U)) :
    (X.presheaf.map (homOfLE e₂).op).hom ((Scheme.Hom.app (𝟙 X) W'').hom ((X.presheaf.map (homOfLE e₁).op).hom ((f.app U).hom y))) =
      (X.presheaf.map (homOfLE e₃).op).hom ((f.app U').hom ((Y.presheaf.map (homOfLE hUU).op).hom y)) := by
  have h1 : (Y.presheaf.map (homOfLE hUU).op ≫ f.app U').hom y = (f.app U ≫ X.presheaf.map (homOfLE (f.preimage_mono hUU)).op).hom y := by
    rw [f.naturality (homOfLE hUU).op]; rfl
  simp only [CommRingCat.comp_apply] at h1
  rw [h1, Scheme.Hom.id_app]
  change ((X.presheaf.map (homOfLE e₁).op ≫ X.presheaf.map (homOfLE e₂).op)).hom ((f.app U).hom y) =
    (X.presheaf.map (homOfLE (f.preimage_mono hUU)).op ≫ X.presheaf.map (homOfLE e₃).op).hom ((f.app U).hom y)
  rw [← Functor.map_comp, ← Functor.map_comp]
  rfl

theorem read_id {R : Type} [CommRing R] {Y : Scheme.{0}} (π : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (A : Type) [CommRing A] [Algebra R A]
    (𝒰 𝒱 : Y.OrderedAffineCover) (lam : 𝒱.ι → 𝒰.ι)
    (hl : ∀ v, (𝒱.baseChange π A).U v ≤ (𝟙 (pullback π (specMap R A))) ⁻¹ᵁ (𝒰.baseChange π A).U (lam v))
    (n : ℕ) (z : (OModulePresheaf.unit (pullback.snd π (specMap R A))).cochain (𝒰.baseChange π A) n)
    (s : 𝒱.Idx n) (hinj : Function.Injective (lam ∘ s.1))
    (hle : 𝒱.inter s ≤ 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
    (σ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      (A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))) ≃+*
        Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hσ₁ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ y : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)),
        σ ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map
              (homOfLE (𝒰.baseChange_inter_le π A ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).op).hom
            (((pullback.fst π (specMap R A)).app (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom y))
    (hσ₂ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom (pullback.snd π (specMap R A))
        ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))) =
        algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) a)
    (σV : letI := algebraOfHom π (𝒱.inter s)
      (A ⊗[R] Γ(Y, 𝒱.inter s)) ≃+* Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s))
    (hσV₁ : letI := algebraOfHom π (𝒱.inter s)
      ∀ y : Γ(Y, 𝒱.inter s),
        σV ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒱.baseChange_inter_le π A s)).op).hom
            (((pullback.fst π (specMap R A)).app (𝒱.inter s)).hom y))
    (hσV₂ : letI := algebraOfHom π (𝒱.inter s)
      letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒱.baseChange π A).inter s)
      ∀ a : A, σV (a ⊗ₜ[R] (1 : Γ(Y, 𝒱.inter s))) = algebraMap A Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s) a)
    (x : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hx : σ x = z ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) :
    letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
    letI := algebraOfHom π (𝒱.inter s)
    OModulePresheaf.unitPullback (πX := pullback.snd π (specMap R A)) (𝟙 (pullback π (specMap R A))) (𝒱.baseChange π A) (𝒰.baseChange π A) lam hl n z s =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        σV ((Algebra.TensorProduct.map (AlgHom.id A A) (restrictAlgHom π hle)) x) :=
  AlgebraicGeometry.OModulePresheaf.unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin π A 𝒰 𝒱 (𝟙 _) (Category.id_comp _)
    lam hl n z s hinj σ hσ₁ hσ₂ σV hσV₁ hσV₂ (restrictAlgHom π hle)
    (fun y => map_id_app_map_app_eq (pullback.fst π (specMap R A)) hle _ _ _ y) x hx

theorem homOfLE_eq_comp_idx {X Y : Scheme.{0}} {ι : Type} (U : ι → X.Opens) (m : ∀ k, (↑(U k) : Scheme.{0}) ⟶ Y)
    {k k' : ι} (h : k = k') : X.homOfLE (le_of_eq (congrArg U h)) ≫ m k' = m k := by
  subst h; simp

end PVBK1b

set_option maxHeartbeats 160000000 in
theorem solution
    (B B₁ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [IsAlgClosed (ResidueField B)]
    [CommRing B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₁)))
    (hsmall : RingHom.ker (algebraMap B B₁) * maximalIdeal B = ⊥)
    {A₁ : Scheme.{0}} (f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)) (L₁ : RelativeGroupLaw B₁ f₁) (hc₁ : L₁.IsCommutative)
    (h₁ : AbelianSchemePropertyBundle B₁ f₁)
    (hI : RingHom.ker (algebraMap B B₁) ≤ maximalIdeal B)
    (V : Type) [AddCommGroup V] [Module (ResidueField B) V] [Module.Finite (ResidueField B) V]
    [Module B V] [IsScalarTower B (ResidueField B) V]
    [Module (ResidueField B)ᵐᵒᵖ V] [IsCentralScalar (ResidueField B) V]
    (ι : V →ₗ[B] B) (hι : Function.Injective ι)
    (hιI : LinearMap.range ι = Submodule.restrictScalars B (RingHom.ker (algebraMap B B₁)))

    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f]
    (𝒰 : D₀.A.OrderedAffineCover) (i₀ : 𝒰.ι) (e₀ : Spec (CommRingCat.of B) ⟶ ↑(𝒰.U i₀)) (he₀ : e₀ ≫ (𝒰.U i₀).ι = (D₀.L.one (𝟙 _)).1)

    (e₁ : Spec (CommRingCat.of (ResidueField B)) ⟶ (((𝒰.baseChange D₀.f (ResidueField B)).U i₀) : Scheme.{0}))
    (he₁ : e₁ ≫ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀).ι = ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).one (𝟙 _)).1)
    (σ : ∀ s : 𝒰.Idx 1,
      letI := algebraOfHom D₀.f (𝒰.inter s)
      ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s)) ≃+* Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s))
    (hσ₁ : ∀ (s : 𝒰.Idx 1) (x : Γ(D₀.A, 𝒰.inter s)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      σ s ((1 : (ResidueField B)) ⊗ₜ[B] x) =
        ((pullback D₀.f (specMap B (ResidueField B))).presheaf.map (homOfLE (𝒰.baseChange_inter_le D₀.f (ResidueField B) s)).op).hom
          (((pullback.fst D₀.f (specMap B (ResidueField B))).app (𝒰.inter s)).hom x))
    (hσ₂ : ∀ (s : 𝒰.Idx 1) (a : (ResidueField B)),
      letI := algebraOfHom D₀.f (𝒰.inter s)
      letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).inter s)
      σ s (a ⊗ₜ[B] (1 : Γ(D₀.A, 𝒰.inter s))) = algebraMap (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), (𝒰.baseChange D₀.f (ResidueField B)).inter s) a)
    (c : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) (((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom
          (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)))
    (hc : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ
        ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1))

    (τ : ∀ s : 𝒰.Idx 1, ((↑(𝒰.inter s) : Scheme.{0}) ≅ ↑(𝒰.inter s)))
    (D : BareDeformation f₁ L₁ B)

    (hτB : ∀ s : 𝒰.Idx 1, (τ s).hom ≫ (𝒰.inter s).ι ≫ D₀.f = (𝒰.inter s).ι ≫ D₀.f)
    (hτg : ∀ s : 𝒰.Idx 1, (D₀.g ∣_ 𝒰.inter s) ≫ (τ s).hom = D₀.g ∣_ 𝒰.inter s)
    (ιD : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A) (hιopen : ∀ i, IsOpenImmersion (ιD i))
    (hιf : ∀ i, ιD i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hιsurj : ∀ x : D.A, ∃ (i : 𝒰.ι) (y : ↑(𝒰.U i)), (ιD i).base y = x)
    (hιg : ∀ i, (D₀.g ∣_ 𝒰.U i) ≫ ιD i = (D₀.g ⁻¹ᵁ 𝒰.U i).ι ≫ D.g)
    (hιglue : ∀ s : 𝒰.Idx 1,
      D₀.A.homOfLE (𝒰.inter_le s 0) ≫ ιD (s.1 0) = (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ ιD (s.1 1))
    (hτ : ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).fromSpec)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ (𝒰.inter s).ι)
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
            σ s (cs a ξ) = (c : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) a ξ s)

    (hU : IsAffineOpen ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))
    (W : Type) [AddCommGroup W] [Module (ResidueField B) W]
    (τW : W → SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hWinj : Function.Injective τW)
    (hWrange : ∀ P : SchemeHomOver (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))), P ∈ Set.range τW ↔ IsTangentVector (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (ResidueField B) (RingHom.id (ResidueField B)) P)
    (hWadd : ∀ v w : W, τW (v + w) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul (tangentBase (ResidueField B) (RingHom.id (ResidueField B))) (τW v) (τW w))
    (hWsmul : ∀ (a : (ResidueField B)) (v : W), (τW (a • v)).1 = tangentScale (ResidueField B) a ≫ (τW v).1)

    (Φ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M : Type) [AddCommGroup M] [Module (ResidueField B) M], ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M) ≃ₗ[(ResidueField B)] (W ⊗[(ResidueField B)] M))
    (hΦnat : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (M M' : Type) [AddCommGroup M] [Module (ResidueField B) M] [AddCommGroup M'] [Module (ResidueField B) M'] (g : M →ₗ[(ResidueField B)] M') (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) M)),
        Φ M' (Algebra.PointDerivations.map ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) g δ) = TensorProduct.map (LinearMap.id : W →ₗ[(ResidueField B)] W) g (Φ M δ))
    (hΦpin : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (δ : ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (ResidueField B))) (χ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →+* DualNumber (ResidueField B)),
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.fst (χ a) = ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) a) →
        (∀ a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)), TrivSqZeroExt.snd (χ a) = (δ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (ResidueField B)) a) →
        (τW (TensorProduct.rid (ResidueField B) W (Φ (ResidueField B) δ))).1 = Spec.map (CommRingCat.ofHom χ) ≫ hU.fromSpec)

    (φ₁ : A₁ ⟶ A₁) (hφ₁ : φ₁ ≫ f₁ = f₁)
    (jκ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ A₁) (hjκ : jκ ≫ D₀.g = (pullback.fst D₀.f (specMap B (ResidueField B))))
    (ψ : (pullback D₀.f (specMap B (ResidueField B))) ⟶ (pullback D₀.f (specMap B (ResidueField B)))) (hψ : ψ ≫ (pullback.snd D₀.f (specMap B (ResidueField B))) = (pullback.snd D₀.f (specMap B (ResidueField B))))
    (hψ₁ : ψ ≫ jκ = jκ ≫ φ₁)
    (hψhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField B))) (P Q : SchemeHomOver t (pullback.snd D₀.f (specMap B (ResidueField B)))),
      pushPt ψ hψ ((RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t P Q) = (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L).mul t (pushPt ψ hψ P) (pushPt ψ hψ Q))

    (m : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D₀.A)
    (hmf : ∀ i, m i ≫ D₀.f = (𝒰.U i).ι ≫ D₀.f)
    (hmμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ m i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D₀.g)
    (c₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc₀ : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ m (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ m (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = (c₀ : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) a ξ s)
    (hc₀Z : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒰.baseChange D₀.f (ResidueField B)) 1 (c₀.1 a ξ) = 0)

    (θψ : W →ₗ[(ResidueField B)] W) (hθψ : ∀ w : W, τW (θψ w) = pushPt ψ hψ (τW w))

    (mp : ∀ i : 𝒰.ι, (↑(𝒰.U i) : Scheme.{0}) ⟶ D.A)
    (hmpf : ∀ i, mp i ≫ D.f = (𝒰.U i).ι ≫ D₀.f)
    (hmpμ : ∀ i, morphismRestrict D₀.g (𝒰.U i) ≫ mp i = (D₀.g ⁻¹ᵁ (𝒰.U i)).ι ≫ φ₁ ≫ D.g)
    (c' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ↥(Algebra.PointDerivations (ResidueField B) Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) ((((𝒰.baseChange D₀.f (ResidueField B)).U i₀).topIso.inv ≫ e₁.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of (ResidueField B))).hom).hom) (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))))
    (hc' : letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
      ∀ s : 𝒰.Idx 1,
        letI := algebraOfHom D₀.f (𝒰.inter s)
        ∃ cs : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒰.inter s))),
          AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒰.inter s)
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒰.inter_le s 0) ≫ mp (s.1 0))
            ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 s).isoSpec.inv ≫ (τ s).hom ≫ D₀.A.homOfLE (𝒰.inter_le s 1) ≫ mp (s.1 1))
            (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) cs ∧
          ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V), σ s (cs a ξ) = c'.1 a ξ s)

    (𝒱 : D₀.A.OrderedAffineCover) (lam₀ lam₀' : 𝒱.ι → 𝒰.ι) (hsub : ∀ v, 𝒱.U v ≤ 𝒰.U (lam₀' v))
    (n n' : ∀ v : 𝒱.ι, (↑(𝒱.U v) : Scheme.{0}) ⟶ ↑(𝒰.U (lam₀ v)))
    (hn : ∀ v, n v ≫ (𝒰.U (lam₀ v)).ι = D₀.A.homOfLE (hsub v) ≫ m (lam₀' v))
    (hn' : ∀ v, n' v ≫ ιD (lam₀ v) = D₀.A.homOfLE (hsub v) ≫ mp (lam₀' v))
    (hl₀ : ∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤ ψ ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀ v))
    (hl₀' : ∀ v, (𝒱.baseChange D₀.f (ResidueField B)).U v ≤
      (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) ⁻¹ᵁ (𝒰.baseChange D₀.f (ResidueField B)).U (lam₀' v)) :
    letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
    ∀ (a : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀))) (ξ : Module.Dual (ResidueField B) V),
      ∃ b : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒱.baseChange D₀.f (ResidueField B)) 0,
        (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).d (𝒱.baseChange D₀.f (ResidueField B)) 0 b =
          OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c'.1 a ξ)
            - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ)
            - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c))).1 a ξ)
            + OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c.1 a ξ) := by
  letI := algebraOfHom (pullback.snd D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)
  intro a ξ
  haveI hsm : Smooth D₀.f := D₀.bundle.smooth
  haveI hfl : Flat D₀.f := inferInstance
  have hak : IsPullback (jκ ≫ D.g) (pullback.snd D₀.f (specMap B (ResidueField B))) D.f (Spec.map (CommRingCat.ofHom (residue B))) :=
    PVBK1b.isPullback_comp_of_factor hπ hI f₁ D₀.f D₀.g D₀.cart D.f D.g D.cart (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B)))
      (IsPullback.of_hasPullback _ _) jκ hjκ

  have hσV0 := fun s₀ : 𝒱.Idx 0 =>
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter D₀.f 𝒱 (ResidueField B) s₀
  choose σV0 hσV0₁ hσV0₂ using hσV0
  have hσV1 := fun s : 𝒱.Idx 1 =>
    AlgebraicGeometry.Scheme.OrderedAffineCover.exists_ringEquiv_tensor_sections_baseChange_inter D₀.f 𝒱 (ResidueField B) s
  choose σV1 hσV1₁ hσV1₂ using hσV1

  have hE := fun s₀ : 𝒱.Idx 0 =>
    GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_factor_bare
      B B₁ hπ hsmall f₁ L₁ hI V ι hι hιI D₀ 𝒰 i₀ e₁ he₁ hU φ₁ jκ hjκ m hmf hmμ D ιD hιf hιg mp hmpf hmpμ
      (lam₀ (s₀.1 0)) (lam₀' (s₀.1 0)) (𝒱.inter s₀) (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s₀)
      ((𝒱.inter_le s₀ 0).trans (hsub (s₀.1 0)))
      (D₀.A.homOfLE (𝒱.inter_le s₀ 0) ≫ n (s₀.1 0)) (D₀.A.homOfLE (𝒱.inter_le s₀ 0) ≫ n' (s₀.1 0))
      (by rw [Category.assoc, hn, ← Category.assoc, Scheme.homOfLE_homOfLE])
      (by rw [Category.assoc, hn', ← Category.assoc, Scheme.homOfLE_homOfLE])
  choose es hes using hE
  refine ⟨fun s₀ => σV0 s₀ (es s₀ a ξ), ?_⟩

  have key : ∀ s : 𝒱.Idx 1,
      ((-1 : ℤ) ^ ((0 : Fin (0 + 2)) : ℕ)) • (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 0) ((fun s₀ : (𝒱.baseChange D₀.f (ResidueField B)).Idx 0 => σV0 s₀ (es s₀ a ξ)) ((𝒱.baseChange D₀.f (ResidueField B)).face s 0)) +
        ((-1 : ℤ) ^ ((1 : Fin (0 + 2)) : ℕ)) • (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 1) ((fun s₀ : (𝒱.baseChange D₀.f (ResidueField B)).Idx 0 => σV0 s₀ (es s₀ a ξ)) ((𝒱.baseChange D₀.f (ResidueField B)).face s 1)) =
      OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c'.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c))).1 a ξ) s + OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c.1 a ξ) s := by
    intro s
    letI iC : Algebra B Γ(D₀.A, 𝒱.inter s) := algebraOfHom D₀.f (𝒱.inter s)
    have hCaff : IsAffineOpen (𝒱.inter s) := Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s
    haveI hCflat : Module.Flat B Γ(D₀.A, 𝒱.inter s) := PVBK1b.flat_sections D₀.f hCaff
    letI iC0 : Algebra B Γ(D₀.A, 𝒱.inter (𝒱.face s 0)) := algebraOfHom D₀.f (𝒱.inter (𝒱.face s 0))
    letI iC1 : Algebra B Γ(D₀.A, 𝒱.inter (𝒱.face s 1)) := algebraOfHom D₀.f (𝒱.inter (𝒱.face s 1))
    have hW0 : 𝒱.inter s ≤ 𝒱.U (s.1 0) := 𝒱.inter_le s 0
    have hW1 : 𝒱.inter s ≤ 𝒱.U (s.1 1) := 𝒱.inter_le s 1
    have eC : (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ (𝒱.inter s).ι ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := PVBK1b.isoSpec_inv_comp_eq D₀.f hCaff

    obtain ⟨xa, hxa⟩ : ∃ xa : Spec (CommRingCat.of Γ(D₀.A, 𝒱.inter s)) ⟶ D.A, xa = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW0 ≫ n (s.1 0) ≫ ιD (lam₀ (s.1 0)) := ⟨_, rfl⟩
    obtain ⟨xa', hxa'⟩ : ∃ xa' : Spec (CommRingCat.of Γ(D₀.A, 𝒱.inter s)) ⟶ D.A, xa' = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW0 ≫ n' (s.1 0) ≫ ιD (lam₀ (s.1 0)) := ⟨_, rfl⟩
    obtain ⟨xb, hxb⟩ : ∃ xb : Spec (CommRingCat.of Γ(D₀.A, 𝒱.inter s)) ⟶ D.A, xb = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW1 ≫ n (s.1 1) ≫ ιD (lam₀ (s.1 1)) := ⟨_, rfl⟩
    obtain ⟨xb', hxb'⟩ : ∃ xb' : Spec (CommRingCat.of Γ(D₀.A, 𝒱.inter s)) ⟶ D.A, xb' = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW1 ≫ n' (s.1 1) ≫ ιD (lam₀ (s.1 1)) := ⟨_, rfl⟩

    have hover : ∀ (v : 𝒱.ι) (hv : 𝒱.inter s ≤ 𝒱.U v),
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hv ≫ n v ≫ ιD (lam₀ v)) ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) ∧
        ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hv ≫ n' v ≫ ιD (lam₀ v)) ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := by
      intro v hv
      constructor
      · rw [← eC]; simp only [Category.assoc]
        rw [hιf, ← Category.assoc (n v), hn, Category.assoc, hmf, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]
      · rw [← eC]; simp only [Category.assoc]
        rw [← Category.assoc (n' v), hn', Category.assoc, hmpf, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]
    have hxaf : xa ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := hxa ▸ (hover _ hW0).1
    have hxa'f : xa' ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := hxa' ▸ (hover _ hW0).2
    have hxbf : xb ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := hxb ▸ (hover _ hW1).1
    have hxb'f : xb' ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := hxb' ▸ (hover _ hW1).2

    have hE0 : AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒱.inter s) xa xa' (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 1))).toLinearMap ∘ₗ es (𝒱.face s 1) a) := by
      have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
        Γ(D₀.A, 𝒱.inter (𝒱.face s 1)) Γ(D₀.A, 𝒱.inter s) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 1)) _ _ (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) _ (hes (𝒱.face s 1))
      have er : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 1)).toRingHom) ≫
          (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 (𝒱.face s 1)).isoSpec.inv = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒱.inter_le_inter_face s 1) :=
        PVBK1b.spec_map_comp_isoSpec_inv _ hCaff _
      simp only [← Category.assoc] at h
      rw [er] at h
      simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc] at h
      rw [hxa, hxa']
      exact h
    have hE1 : AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒱.inter s) xb xb' (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) (fun a => (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 0))).toLinearMap ∘ₗ es (𝒱.face s 0) a) := by
      have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
        Γ(D₀.A, 𝒱.inter (𝒱.face s 0)) Γ(D₀.A, 𝒱.inter s) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 0)) _ _ (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) _ (hes (𝒱.face s 0))
      have er : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 0)).toRingHom) ≫
          (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 (𝒱.face s 0)).isoSpec.inv = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (𝒱.inter_le_inter_face s 0) :=
        PVBK1b.spec_map_comp_isoSpec_inv _ hCaff _
      simp only [← Category.assoc] at h
      rw [er] at h
      simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc] at h
      rw [hxb, hxb']
      exact h
    have hEres1 : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 0) (σV0 (𝒱.face s 0) (es (𝒱.face s 0) a ξ)) =
        σV1 s ((Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 0)))
          (es (𝒱.face s 0) a ξ)) :=
      (AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq D₀.f (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))) (𝒱.inter_le_inter_face s 0)
        (𝒱.baseChange_inter_le D₀.f (ResidueField B) (𝒱.face s 0)) (𝒱.baseChange_inter_le D₀.f (ResidueField B) s) ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 0)
        (σV0 (𝒱.face s 0)).toRingHom (σV1 s).toRingHom (hσV0₁ (𝒱.face s 0)) (hσV0₂ (𝒱.face s 0)) (hσV1₁ s) (hσV1₂ s)
        (es (𝒱.face s 0) a ξ)).symm
    have hEres0 : (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 1) (σV0 (𝒱.face s 1) (es (𝒱.face s 1) a ξ)) =
        σV1 s ((Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 1)))
          (es (𝒱.face s 1) a ξ)) :=
      (AlgebraicGeometry.Scheme.TwoAffineOpenCover.map_restrictAlgHom_eq_presheaf_map_of_tmul_eq D₀.f (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))) (𝒱.inter_le_inter_face s 1)
        (𝒱.baseChange_inter_le D₀.f (ResidueField B) (𝒱.face s 1)) (𝒱.baseChange_inter_le D₀.f (ResidueField B) s) ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 1)
        (σV0 (𝒱.face s 1)).toRingHom (σV1 s).toRingHom (hσV0₁ (𝒱.face s 1)) (hσV0₂ (𝒱.face s 1)) (hσV1₁ s) (hσV1₂ s)
        (es (𝒱.face s 1) a ξ)).symm

    have hqaa' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xa = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xa' := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hE0
    have hqbb' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xb = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xb' := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hE1

    have hJ : ∃ X1 : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒱.inter s))),
        AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒱.inter s) xa' xb' (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) X1 ∧
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c'.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c))).1 a ξ) s = σV1 s (X1 a ξ) := by
      rcases lt_trichotomy (lam₀' (s.1 0)) (lam₀' (s.1 1)) with hj | hj | hj
      ·
        have hinj : Function.Injective (lam₀' ∘ s.1) := PVBK1b.injective_of_ne 𝒱 𝒰 lam₀' s (ne_of_lt hj)
        obtain ⟨ht0, ht1, -⟩ := PVBK1b.sortIdx_of_lt (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hj hinj
        obtain ⟨-, -, hsgn⟩ := PVBK1b.sortIdx_of_lt 𝒱 𝒰 lam₀' s hj hinj
        have hWt : 𝒱.inter s ≤ 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) :=
          le_iInf fun j => (iInf_le (fun k => 𝒱.U (s.1 k)) (Tuple.sort (lam₀' ∘ s.1) j)).trans (hsub _)
        letI := algebraOfHom D₀.f (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj))
        obtain ⟨cs', hcs', hcs'σ⟩ := hc' ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)
        obtain ⟨y, xθ, hy, hxθ, hsplit⟩ := GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
          B B₁ hπ hker hsmall f₁ L₁ hc₁ h₁ hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ c hc τ D hτB hτg ιD hιopen hιf hιsurj hιg hιglue hτ hU W τW hWinj hWrange hWadd hWsmul Φ hΦnat hΦpin φ₁ hφ₁ jκ hjκ ψ hψ hψ₁ hψhom m hmf hmμ c₀ hc₀ hc₀Z θψ hθψ mp hmpf hmpμ c' hc' ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) (𝒱.inter s) hCaff hWt cs' hcs'
        have hTp := PVBK1b.read_id D₀.f (ResidueField B) 𝒰 𝒱 lam₀' hl₀' 1 (c'.1 a ξ) s hinj hWt (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) (cs' a ξ) (hcs'σ a ξ)
        have hTth := PVBK1b.read_id D₀.f (ResidueField B) 𝒰 𝒱 lam₀' hl₀' 1 ((((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c)))).1 a ξ) s hinj hWt (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) (xθ a ξ) (hxθ a ξ)
        rw [hsgn, Units.val_one, one_smul] at hTp hTth
        have hsplitξ := LinearMap.congr_fun (hsplit a) ξ
        simp only [LinearMap.comp_apply, LinearMap.add_apply, AlgHom.toLinearMap_apply] at hsplitξ
        have e0 : D₀.A.homOfLE (hWt.trans (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) 0)) ≫ mp (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj).1 0) = D₀.A.homOfLE hW0 ≫ n' (s.1 0) ≫ ιD (lam₀ (s.1 0)) := by
          rw [hn', Scheme.homOfLE_homOfLE_assoc]; exact PVBK1b.homOfLE_comp_idx_eq 𝒰.U mp ht0 _ _
        have e1 : D₀.A.homOfLE (hWt.trans (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) 1)) ≫ mp (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj).1 1) = D₀.A.homOfLE hW1 ≫ n' (s.1 1) ≫ ιD (lam₀ (s.1 1)) := by
          rw [hn', Scheme.homOfLE_homOfLE_assoc]; exact PVBK1b.homOfLE_comp_idx_eq 𝒰.U mp ht1 _ _
        rw [e0, e1, ← hxa', ← hxb'] at hy
        refine ⟨y, hy, ?_⟩
        rw [hTp, hTth, hsplitξ, map_add]
        abel
      ·
        have hninj : ¬ Function.Injective (lam₀' ∘ s.1) := PVBK1b.not_injective_of_eq 𝒱 𝒰 lam₀' s hj
        have e : xa' = xb' := by
          rw [hxa', hxb', hn', hn', Scheme.homOfLE_homOfLE_assoc, Scheme.homOfLE_homOfLE_assoc,
            PVBK1b.homOfLE_comp_idx_eq 𝒰.U mp hj (hW0.trans (hsub _)) (hW1.trans (hsub _))]
        refine ⟨0, ?_, ?_⟩
        · rw [e]
          exact PVBK1b.at_self (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ xb' hxb'f
        · rw [AlgebraicGeometry.OModulePresheaf.unitPullback_apply_of_not_injective (𝒲 := 𝒱.baseChange D₀.f (ResidueField B)) (𝒦 := 𝒰.baseChange D₀.f (ResidueField B)) (hinj := hninj),
            AlgebraicGeometry.OModulePresheaf.unitPullback_apply_of_not_injective (𝒲 := 𝒱.baseChange D₀.f (ResidueField B)) (𝒦 := 𝒰.baseChange D₀.f (ResidueField B)) (hinj := hninj)]
          simp
          try rfl
      ·
        have hinj : Function.Injective (lam₀' ∘ s.1) := PVBK1b.injective_of_ne 𝒱 𝒰 lam₀' s (ne_of_gt hj)
        obtain ⟨ht0, ht1, -⟩ := PVBK1b.sortIdx_of_gt (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hj hinj
        obtain ⟨-, -, hsgn⟩ := PVBK1b.sortIdx_of_gt 𝒱 𝒰 lam₀' s hj hinj
        have hWt : 𝒱.inter s ≤ 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) :=
          le_iInf fun j => (iInf_le (fun k => 𝒱.U (s.1 k)) (Tuple.sort (lam₀' ∘ s.1) j)).trans (hsub _)
        letI := algebraOfHom D₀.f (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj))
        obtain ⟨cs', hcs', hcs'σ⟩ := hc' ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)
        obtain ⟨y, xθ, hy, hxθ, hsplit⟩ := GoodReductionJacobian.BareDeformation.exists_isTangentCoordsOfPairAt_local_lifts_untwist_bare
          B B₁ hπ hker hsmall f₁ L₁ hc₁ h₁ hI V ι hι hιI D₀ 𝒰 i₀ e₀ he₀ e₁ he₁ σ hσ₁ hσ₂ c hc τ D hτB hτg ιD hιopen hιf hιsurj hιg hιglue hτ hU W τW hWinj hWrange hWadd hWsmul Φ hΦnat hΦpin φ₁ hφ₁ jκ hjκ ψ hψ hψ₁ hψhom m hmf hmμ c₀ hc₀ hc₀Z θψ hθψ mp hmpf hmpμ c' hc' ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) (𝒱.inter s) hCaff hWt cs' hcs'
        have hTp := PVBK1b.read_id D₀.f (ResidueField B) 𝒰 𝒱 lam₀' hl₀' 1 (c'.1 a ξ) s hinj hWt (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) (cs' a ξ) (hcs'σ a ξ)
        have hTth := PVBK1b.read_id D₀.f (ResidueField B) 𝒰 𝒱 lam₀' hl₀' 1 ((((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c)))).1 a ξ) s hinj hWt (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) (xθ a ξ) (hxθ a ξ)
        rw [hsgn, Units.val_neg, Units.val_one, neg_one_smul] at hTp hTth
        have hsplitξ := LinearMap.congr_fun (hsplit a) ξ
        simp only [LinearMap.comp_apply, LinearMap.add_apply, AlgHom.toLinearMap_apply] at hsplitξ
        have e0 : D₀.A.homOfLE (hWt.trans (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) 0)) ≫ mp (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj).1 0) = D₀.A.homOfLE hW1 ≫ n' (s.1 1) ≫ ιD (lam₀ (s.1 1)) := by
          rw [hn', Scheme.homOfLE_homOfLE_assoc]; exact PVBK1b.homOfLE_comp_idx_eq 𝒰.U mp ht0 _ _
        have e1 : D₀.A.homOfLE (hWt.trans (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) 1)) ≫ mp (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj).1 1) = D₀.A.homOfLE hW0 ≫ n' (s.1 0) ≫ ιD (lam₀ (s.1 0)) := by
          rw [hn', Scheme.homOfLE_homOfLE_assoc]; exact PVBK1b.homOfLE_comp_idx_eq 𝒰.U mp ht1 _ _
        rw [e0, e1, ← hxa', ← hxb'] at hy
        have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xb' =
            Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xa' :=
          PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hy
        refine ⟨-y, PVBK1b.at_symm (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ xb' xa' hxb'f hxa'f hq hy, ?_⟩
        rw [hTp, hTth, hsplitξ, map_add, Pi.neg_apply, LinearMap.neg_apply, map_neg]
        abel

    have hF := GoodReductionJacobian.BareDeformation.exists_factor_inf_of_local_lifts_factor_bare B B₁ hπ hI f₁ L₁ D₀ 𝒰 φ₁ m hmμ D ιD hιg mp hmpμ
      (lam₀ (s.1 0)) (lam₀ (s.1 1)) (lam₀' (s.1 0)) (lam₀' (s.1 1)) (𝒱.U (s.1 0)) (𝒱.U (s.1 1)) (hsub (s.1 0)) (hsub (s.1 1))
      (n (s.1 0)) (n' (s.1 0)) (n (s.1 1)) (n' (s.1 1)) (hn (s.1 0)) (hn' (s.1 0)) (hn (s.1 1)) (hn' (s.1 1))
    obtain ⟨p, p', q, q', hp, hp', hq, hq'⟩ := hF
    have hVs : 𝒱.inter s ≤ 𝒱.U (s.1 0) ⊓ 𝒱.U (s.1 1) := le_inf (𝒱.inter_le s 0) (𝒱.inter_le s 1)

    have hak₀ : IsPullback (pullback.fst D₀.f (specMap B (ResidueField B))) (pullback.snd D₀.f (specMap B (ResidueField B))) D₀.f (Spec.map (CommRingCat.ofHom (residue B))) := IsPullback.of_hasPullback _ _
    have hmover : ∀ (k : 𝒰.ι) (hk : 𝒱.inter s ≤ 𝒰.U k), ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hk ≫ m k) ≫ D₀.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := by
      intro k hk
      rw [← eC]; simp only [Category.assoc]; rw [hmf, Scheme.homOfLE_ι_assoc]

    have hI0 : ∃ Y0 : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒱.inter s))),
        AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒱.inter s) ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW0.trans (hsub (s.1 0))) ≫ m (lam₀' (s.1 0))) ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW1.trans (hsub (s.1 1))) ≫ m (lam₀' (s.1 1))) (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) Y0 ∧
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ) s = σV1 s (Y0 a ξ) := by
      rcases lt_trichotomy (lam₀' (s.1 0)) (lam₀' (s.1 1)) with hj | hj | hj
      ·

        have hinj : Function.Injective (lam₀' ∘ s.1) := PVBK1b.injective_of_ne 𝒱 𝒰 lam₀' s (ne_of_lt hj)
        obtain ⟨ht0, ht1, -⟩ := PVBK1b.sortIdx_of_lt (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hj hinj
        obtain ⟨-, -, hsgn⟩ := PVBK1b.sortIdx_of_lt 𝒱 𝒰 lam₀' s hj hinj
        have hWt : 𝒱.inter s ≤ 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) :=
          le_iInf fun j => (iInf_le (fun k => 𝒱.U (s.1 k)) (Tuple.sort (lam₀' ∘ s.1) j)).trans (hsub _)
        letI := algebraOfHom D₀.f (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj))
        obtain ⟨cs₀, hcs₀, hcs₀σ⟩ := hc₀ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)
        have hT0 := PVBK1b.read_id D₀.f (ResidueField B) 𝒰 𝒱 lam₀' hl₀' 1 (c₀.1 a ξ) s hinj hWt (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) (cs₀ a ξ) (hcs₀σ a ξ)
        rw [hsgn, Units.val_one, one_smul] at hT0
        have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
          Γ(D₀.A, 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) Γ(D₀.A, 𝒱.inter s) (restrictAlgHom D₀.f hWt) _ _ (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) _ hcs₀
        have er : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hWt).toRingHom) ≫
            (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)).isoSpec.inv = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hWt :=
          PVBK1b.spec_map_comp_isoSpec_inv _ hCaff _
        simp only [← Category.assoc] at h
        rw [er] at h
        simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc] at h
        rw [PVBK1b.homOfLE_comp_idx_eq 𝒰.U m ht0 _ (hW0.trans (hsub (s.1 0))), PVBK1b.homOfLE_comp_idx_eq 𝒰.U m ht1 _ (hW1.trans (hsub (s.1 1)))] at h
        exact ⟨_, h, hT0⟩
      ·
        have hninj : ¬ Function.Injective (lam₀' ∘ s.1) := PVBK1b.not_injective_of_eq 𝒱 𝒰 lam₀' s hj
        refine ⟨0, ?_, ?_⟩
        · rw [PVBK1b.homOfLE_comp_idx_eq 𝒰.U m hj (hW0.trans (hsub (s.1 0))) (hW1.trans (hsub (s.1 1)))]
          exact PVBK1b.at_self (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D₀.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) hak₀ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ _ (hmover _ _)
        · rw [AlgebraicGeometry.OModulePresheaf.unitPullback_apply_of_not_injective (𝒲 := 𝒱.baseChange D₀.f (ResidueField B)) (𝒦 := 𝒰.baseChange D₀.f (ResidueField B)) (hinj := hninj)]
          simp
          try rfl
      ·

        have hinj : Function.Injective (lam₀' ∘ s.1) := PVBK1b.injective_of_ne 𝒱 𝒰 lam₀' s (ne_of_gt hj)
        obtain ⟨ht0, ht1, -⟩ := PVBK1b.sortIdx_of_gt (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hj hinj
        obtain ⟨-, -, hsgn⟩ := PVBK1b.sortIdx_of_gt 𝒱 𝒰 lam₀' s hj hinj
        have hWt : 𝒱.inter s ≤ 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj) :=
          le_iInf fun j => (iInf_le (fun k => 𝒱.U (s.1 k)) (Tuple.sort (lam₀' ∘ s.1) j)).trans (hsub _)
        letI := algebraOfHom D₀.f (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj))
        obtain ⟨cs₀, hcs₀, hcs₀σ⟩ := hc₀ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)
        have hT0 := PVBK1b.read_id D₀.f (ResidueField B) 𝒰 𝒱 lam₀' hl₀' 1 (c₀.1 a ξ) s hinj hWt (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) (cs₀ a ξ) (hcs₀σ a ξ)
        rw [hsgn, Units.val_neg, Units.val_one, neg_one_smul] at hT0
        have h := AlgebraicGeometry.SmallExtension.isTangentCoordsOfPairAt_comp_of_flat (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI
          Γ(D₀.A, 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)) Γ(D₀.A, 𝒱.inter s) (restrictAlgHom D₀.f hWt) _ _ (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) _ hcs₀
        have er : Spec.map (CommRingCat.ofHom (restrictAlgHom D₀.f hWt).toRingHom) ≫
            (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀' s hinj)).isoSpec.inv = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hWt :=
          PVBK1b.spec_map_comp_isoSpec_inv _ hCaff _
        simp only [← Category.assoc] at h
        rw [er] at h
        simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc] at h
        rw [PVBK1b.homOfLE_comp_idx_eq 𝒰.U m ht0 _ (hW1.trans (hsub (s.1 1))), PVBK1b.homOfLE_comp_idx_eq 𝒰.U m ht1 _ (hW0.trans (hsub (s.1 0)))] at h
        have hq := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ h
        refine ⟨_, PVBK1b.at_symm (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D₀.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (pullback.fst D₀.f (specMap B (ResidueField B))) hak₀ ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ _ _ (hmover _ _) (hmover _ _) hq h, ?_⟩
        rw [hT0]
        simp only [Pi.neg_apply, LinearMap.neg_apply, map_neg, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
    obtain ⟨Y0, hY0, hT0e⟩ := hI0
    have hI' : ∃ X2 : Γ((pullback D₀.f (specMap B (ResidueField B))), ((𝒰.baseChange D₀.f (ResidueField B)).U i₀)) → (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((ResidueField B) ⊗[B] Γ(D₀.A, 𝒱.inter s))),
        AlgebraicGeometry.SmallExtension.IsTangentCoordsOfPairAt (RingHom.ker (algebraMap B B₁)) V ι Γ(D₀.A, 𝒱.inter s) xa xb (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) X2 ∧
        OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c.1 a ξ) s = σV1 s (X2 a ξ) := by
      rcases lt_trichotomy (lam₀ (s.1 0)) (lam₀ (s.1 1)) with hi | hi | hi
      ·
        have hinj : Function.Injective (lam₀ ∘ s.1) := PVBK1b.injective_of_ne 𝒱 𝒰 lam₀ s (ne_of_lt hi)
        obtain ⟨ht0, ht1, -⟩ := PVBK1b.sortIdx_of_lt (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hi hinj
        obtain ⟨-, -, hsgn⟩ := PVBK1b.sortIdx_of_lt 𝒱 𝒰 lam₀ s hi hinj
        have et : 𝒰.U (lam₀ (s.1 0)) ⊓ 𝒰.U (lam₀ (s.1 1)) ≤ 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) := by
          rw [PVBK1b.inter_one_eq, ht0, ht1]
        have hWj : 𝒱.inter s ≤ 𝒰.U (lam₀' (s.1 0)) := hW0.trans (hsub (s.1 0))
        obtain ⟨Pt, hPt⟩ : ∃ Pt : (↑(𝒱.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)), Pt = D₀.A.homOfLE hVs ≫ p ≫ D₀.A.homOfLE et := ⟨_, rfl⟩
        have hPι : Pt ≫ (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)).ι = D₀.A.homOfLE hWj ≫ m (lam₀' (s.1 0)) := by
          rw [hPt]; simp only [Category.assoc, Scheme.homOfLE_ι]
          rw [← Scheme.homOfLE_ι D₀.A (inf_le_left : 𝒰.U (lam₀ (s.1 0)) ⊓ 𝒰.U (lam₀ (s.1 1)) ≤ 𝒰.U (lam₀ (s.1 0))), reassoc_of% hp, hn]
          simp only [Scheme.homOfLE_homOfLE_assoc]
        letI := algebraOfHom D₀.f (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj))
        obtain ⟨cst, hcst, hcstσ⟩ := hτ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)
        obtain ⟨θ, hθ, hψc⟩ := GoodReductionJacobian.BareDeformation.exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
          B B₁ hsmall f₁ L₁ hI V ι hι hιI D₀ 𝒰 i₀ jκ hjκ τ D ιD hιg hιglue m hmf ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) (lam₀' (s.1 0)) (𝒱.inter s) hCaff hWj Pt hPι cst hcst
        have hlift := GoodReductionJacobian.BareDeformation.map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare
          B B₁ hπ f₁ L₁ D₀ 𝒰 φ₁ jκ hjκ ψ hψ₁ m hmμ (lam₀' (s.1 0)) (𝒱.inter s) (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) hCaff
          (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) hWj Pt hPι θ hθ
          ((𝒱.baseChange D₀.f (ResidueField B)).inter s) ((𝒰.baseChange D₀.f (ResidueField B)).inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (𝒰.baseChange_inter_le D₀.f (ResidueField B) ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj))
          ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_preimage_inter_sortIdx ψ (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ s hinj) (𝒱.baseChange_inter_le D₀.f (ResidueField B) s)
        have hTψ := AlgebraicGeometry.OModulePresheaf.unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin D₀.f (ResidueField B) 𝒰 𝒱 ψ hψ lam₀ hl₀ 1 (c.1 a ξ) s hinj
          (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) θ hlift (cst a ξ) (hcstσ a ξ)
        rw [hsgn, Units.val_one, one_smul] at hTψ
        obtain ⟨xp', hxp'⟩ : ∃ xp' : Spec (CommRingCat.of Γ(D₀.A, 𝒱.inter s)) ⟶ D.A, xp' = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hVs ≫ p ≫ D₀.A.homOfLE inf_le_right ≫ ιD (lam₀ (s.1 1)) := ⟨_, rfl⟩
        have eP1 : Pt ≫ D₀.A.homOfLE (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) 1) ≫ ιD (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj).1 1) = D₀.A.homOfLE hVs ≫ p ≫ D₀.A.homOfLE inf_le_right ≫ ιD (lam₀ (s.1 1)) := by
          rw [hPt]; simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
          rw [PVBK1b.homOfLE_comp_idx_eq 𝒰.U ιD ht1 _ inf_le_right]
        have eP0 : Pt ≫ D₀.A.homOfLE (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) 0) ≫ ιD (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj).1 0) = D₀.A.homOfLE hW0 ≫ n (s.1 0) ≫ ιD (lam₀ (s.1 0)) := by
          rw [hPt]; simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
          rw [PVBK1b.homOfLE_comp_idx_eq 𝒰.U ιD ht0 _ inf_le_left, reassoc_of% hp]
          simp only [Scheme.homOfLE_homOfLE_assoc]
        rw [eP1, eP0, ← hxa, ← hxp'] at hψc
        have e1 : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hVs ≫ p ≫ D₀.A.homOfLE inf_le_right) ≫ (𝒰.U (lam₀ (s.1 1))).ι = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW0.trans (hsub (s.1 0))) ≫ m (lam₀' (s.1 0)) := by
          simp only [Category.assoc, Scheme.homOfLE_ι]
          rw [← Scheme.homOfLE_ι D₀.A (inf_le_left : 𝒰.U (lam₀ (s.1 0)) ⊓ 𝒰.U (lam₀ (s.1 1)) ≤ 𝒰.U (lam₀ (s.1 0))), reassoc_of% hp, hn]
          simp only [Scheme.homOfLE_homOfLE_assoc]
        have e2 : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW1 ≫ n (s.1 1)) ≫ (𝒰.U (lam₀ (s.1 1))).ι = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW1.trans (hsub (s.1 1))) ≫ m (lam₀' (s.1 1)) := by
          simp only [Category.assoc]; rw [hn]; simp only [Scheme.homOfLE_homOfLE_assoc]
        rw [← e1, ← e2] at hY0
        have hY0D := GoodReductionJacobian.BareDeformation.isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
          B B₁ hsmall f₁ L₁ hI V ι D₀ 𝒰 i₀ jκ hjκ D (lam₀ (s.1 1)) (ιD _) (hιg _) Γ(D₀.A, 𝒱.inter s) _ _ Y0 hY0
        simp only [Category.assoc] at hY0D
        rw [← hxb, ← hxp'] at hY0D
        have hxp'f : xp' ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := by
          have h := hmover _ (hW0.trans (hsub (s.1 0))); rw [← e1] at h; rw [hxp']; simpa only [Category.assoc, hιf] using h
        have hq1 := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hψc
        have hq2 := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hY0D
        refine ⟨_, PVBK1b.at_trans (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ xa xp' xb hxaf hxp'f hxbf hq1.symm hq2 (PVBK1b.at_symm (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ xp' xa hxp'f hxaf hq1 hψc) hY0D, ?_⟩
        rw [hT0e, hTψ]
        simp only [Pi.add_apply, Pi.neg_apply, LinearMap.add_apply, LinearMap.neg_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_add, map_neg]
        abel
      ·
        have hninj : ¬ Function.Injective (lam₀ ∘ s.1) := PVBK1b.not_injective_of_eq 𝒱 𝒰 lam₀ s hi
        have e1 : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW0 ≫ n (s.1 0) ≫ D₀.A.homOfLE (le_of_eq (congrArg 𝒰.U hi))) ≫ (𝒰.U (lam₀ (s.1 1))).ι = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW0.trans (hsub (s.1 0))) ≫ m (lam₀' (s.1 0)) := by
          simp only [Category.assoc, Scheme.homOfLE_ι]; rw [hn]; simp only [Scheme.homOfLE_homOfLE_assoc]
        have e2 : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW1 ≫ n (s.1 1)) ≫ (𝒰.U (lam₀ (s.1 1))).ι = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW1.trans (hsub (s.1 1))) ≫ m (lam₀' (s.1 1)) := by
          simp only [Category.assoc]; rw [hn]; simp only [Scheme.homOfLE_homOfLE_assoc]
        rw [← e1, ← e2] at hY0
        have hY0D := GoodReductionJacobian.BareDeformation.isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
          B B₁ hsmall f₁ L₁ hI V ι D₀ 𝒰 i₀ jκ hjκ D (lam₀ (s.1 1)) (ιD _) (hιg _) Γ(D₀.A, 𝒱.inter s) _ _ Y0 hY0
        simp only [Category.assoc] at hY0D
        rw [PVBK1b.homOfLE_eq_comp_idx 𝒰.U ιD hi, ← hxa, ← hxb] at hY0D
        refine ⟨Y0, hY0D, ?_⟩
        rw [AlgebraicGeometry.OModulePresheaf.unitPullback_apply_of_not_injective (𝒲 := 𝒱.baseChange D₀.f (ResidueField B)) (𝒦 := 𝒰.baseChange D₀.f (ResidueField B)) (hinj := hninj), sub_zero]
        exact hT0e
      ·
        have hinj : Function.Injective (lam₀ ∘ s.1) := PVBK1b.injective_of_ne 𝒱 𝒰 lam₀ s (ne_of_gt hi)
        obtain ⟨ht0, ht1, -⟩ := PVBK1b.sortIdx_of_gt (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hi hinj
        obtain ⟨-, -, hsgn⟩ := PVBK1b.sortIdx_of_gt 𝒱 𝒰 lam₀ s hi hinj
        have et : 𝒰.U (lam₀ (s.1 0)) ⊓ 𝒰.U (lam₀ (s.1 1)) ≤ 𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) := by
          rw [PVBK1b.inter_one_eq, ht0, ht1]; exact le_inf inf_le_right inf_le_left
        have hWj : 𝒱.inter s ≤ 𝒰.U (lam₀' (s.1 1)) := hW1.trans (hsub (s.1 1))
        obtain ⟨Qt, hQt⟩ : ∃ Qt : (↑(𝒱.inter s) : Scheme.{0}) ⟶ ↑(𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)), Qt = D₀.A.homOfLE hVs ≫ q ≫ D₀.A.homOfLE et := ⟨_, rfl⟩
        have hQι : Qt ≫ (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)).ι = D₀.A.homOfLE hWj ≫ m (lam₀' (s.1 1)) := by
          rw [hQt]; simp only [Category.assoc, Scheme.homOfLE_ι]
          rw [← Scheme.homOfLE_ι D₀.A (inf_le_right : 𝒰.U (lam₀ (s.1 0)) ⊓ 𝒰.U (lam₀ (s.1 1)) ≤ 𝒰.U (lam₀ (s.1 1))), reassoc_of% hq, hn]
          simp only [Scheme.homOfLE_homOfLE_assoc]
        letI := algebraOfHom D₀.f (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj))
        obtain ⟨cst, hcst, hcstσ⟩ := hτ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)
        obtain ⟨θ, hθ, hψc⟩ := GoodReductionJacobian.BareDeformation.exists_algHom_isTangentCoordsOfPairAt_regluing_of_local_lift_factor_bare
          B B₁ hsmall f₁ L₁ hI V ι hι hιI D₀ 𝒰 i₀ jκ hjκ τ D ιD hιg hιglue m hmf ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) (lam₀' (s.1 1)) (𝒱.inter s) hCaff hWj Qt hQι cst hcst
        have hlift := GoodReductionJacobian.BareDeformation.map_app_app_eq_map_app_of_specMap_comp_eq_of_local_lift_factor_bare
          B B₁ hπ f₁ L₁ D₀ 𝒰 φ₁ jκ hjκ ψ hψ₁ m hmμ (lam₀' (s.1 1)) (𝒱.inter s) (𝒰.inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) hCaff
          (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) hWj Qt hQι θ hθ
          ((𝒱.baseChange D₀.f (ResidueField B)).inter s) ((𝒰.baseChange D₀.f (ResidueField B)).inter ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (𝒰.baseChange_inter_le D₀.f (ResidueField B) ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj))
          ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_preimage_inter_sortIdx ψ (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ s hinj) (𝒱.baseChange_inter_le D₀.f (ResidueField B) s)
        have hTψ := AlgebraicGeometry.OModulePresheaf.unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin D₀.f (ResidueField B) 𝒰 𝒱 ψ hψ lam₀ hl₀ 1 (c.1 a ξ) s hinj
          (σ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (hσ₁ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (hσ₂ ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj)) (σV1 s) (hσV1₁ s) (hσV1₂ s) θ hlift (cst a ξ) (hcstσ a ξ)
        rw [hsgn, Units.val_neg, Units.val_one, neg_one_smul] at hTψ
        obtain ⟨xq, hxq⟩ : ∃ xq : Spec (CommRingCat.of Γ(D₀.A, 𝒱.inter s)) ⟶ D.A, xq = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hVs ≫ q ≫ D₀.A.homOfLE inf_le_left ≫ ιD (lam₀ (s.1 0)) := ⟨_, rfl⟩
        have eQ1 : Qt ≫ D₀.A.homOfLE (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) 1) ≫ ιD (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj).1 1) = D₀.A.homOfLE hVs ≫ q ≫ D₀.A.homOfLE inf_le_left ≫ ιD (lam₀ (s.1 0)) := by
          rw [hQt]; simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
          rw [PVBK1b.homOfLE_comp_idx_eq 𝒰.U ιD ht1 _ inf_le_left]
        have eQ0 : Qt ≫ D₀.A.homOfLE (𝒰.inter_le ((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj) 0) ≫ ιD (((𝒱.baseChange D₀.f (ResidueField B)).sortIdx (𝒰.baseChange D₀.f (ResidueField B)) lam₀ s hinj).1 0) = D₀.A.homOfLE hW1 ≫ n (s.1 1) ≫ ιD (lam₀ (s.1 1)) := by
          rw [hQt]; simp only [Category.assoc, Scheme.homOfLE_homOfLE_assoc]
          rw [PVBK1b.homOfLE_comp_idx_eq 𝒰.U ιD ht0 _ inf_le_right, reassoc_of% hq]
          simp only [Scheme.homOfLE_homOfLE_assoc]
        rw [eQ1, eQ0, ← hxb, ← hxq] at hψc
        have e1 : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hW0 ≫ n (s.1 0)) ≫ (𝒰.U (lam₀ (s.1 0))).ι = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW0.trans (hsub (s.1 0))) ≫ m (lam₀' (s.1 0)) := by
          simp only [Category.assoc]; rw [hn]; simp only [Scheme.homOfLE_homOfLE_assoc]
        have e2 : ((Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE hVs ≫ q ≫ D₀.A.homOfLE inf_le_left) ≫ (𝒰.U (lam₀ (s.1 0))).ι = (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒱 s).isoSpec.inv ≫ D₀.A.homOfLE (hW1.trans (hsub (s.1 1))) ≫ m (lam₀' (s.1 1)) := by
          simp only [Category.assoc, Scheme.homOfLE_ι]
          rw [← Scheme.homOfLE_ι D₀.A (inf_le_right : 𝒰.U (lam₀ (s.1 0)) ⊓ 𝒰.U (lam₀ (s.1 1)) ≤ 𝒰.U (lam₀ (s.1 1))), reassoc_of% hq, hn]
          simp only [Scheme.homOfLE_homOfLE_assoc]
        rw [← e1, ← e2] at hY0
        have hY0D := GoodReductionJacobian.BareDeformation.isTangentCoordsOfPairAt_comp_regluing_chart_of_comp_incl_bare
          B B₁ hsmall f₁ L₁ hI V ι D₀ 𝒰 i₀ jκ hjκ D (lam₀ (s.1 0)) (ιD _) (hιg _) Γ(D₀.A, 𝒱.inter s) _ _ Y0 hY0
        simp only [Category.assoc] at hY0D
        rw [← hxa, ← hxq] at hY0D
        have hxqf : xq ≫ D.f = Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, 𝒱.inter s))) := by
          have h := hmover _ (hW1.trans (hsub (s.1 1))); rw [← e2] at h; rw [hxq]; simpa only [Category.assoc, hιf] using h
        have hq1 := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hψc
        have hq2 := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hY0D
        refine ⟨_, PVBK1b.at_trans (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁ xa xq xb hxaf hxqf hxbf hq2 hq1 hY0D hψc, ?_⟩
        rw [hT0e, hTψ]
        simp only [Pi.add_apply, LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_add]
        abel
    obtain ⟨X1, hX1, hJe⟩ := hJ
    obtain ⟨X2, hX2, hIe⟩ := hI'
    have hqa'b' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xa' = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xb' := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hX1
    have hqab : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xa = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, 𝒱.inter s))))) ≫ xb := PVBK1b.specMap_mk_comp_eq_of_isTangentCoordsOfPairAt _ V ι _ _ _ _ _ _ _ _ hX2

    have h3 := PVBK1b.at_trans (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁
      xa xa' xb' hxaf hxa'f hxb'f hqaa' hqa'b' hE0 hX1
    have h3' := PVBK1b.at_trans (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁
      xa xb xb' hxaf hxbf hxb'f hqab hqbb' hX2 hE1
    have hsum := PVBK1b.at_unique (RingHom.ker (algebraMap B B₁)) hI hsmall V ι hι hιI Γ(D₀.A, 𝒱.inter s) D.f (pullback.snd D₀.f (specMap B (ResidueField B))) (RelativeGroupLaw.baseChange (specMap B (ResidueField B)) D₀.L) (jκ ≫ D.g) hak ((𝒰.baseChange D₀.f (ResidueField B)).U i₀) hU e₁ he₁
      xa xb' hxaf hxb'f (hqaa'.trans hqa'b') h3 h3'
    have hsumξ : (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 1))) (es (𝒱.face s 1) a ξ) + X1 a ξ =
        X2 a ξ + (Algebra.TensorProduct.map (AlgHom.id (ResidueField B) (ResidueField B)) (restrictAlgHom D₀.f (𝒱.inter_le_inter_face s 0))) (es (𝒱.face s 0) a ξ) := by
      have h := congrFun hsum a
      simp only [Pi.add_apply] at h
      have h2 := LinearMap.congr_fun h ξ
      simpa only [LinearMap.comp_apply, LinearMap.add_apply, AlgHom.toLinearMap_apply] using h2
    have hσsum := congrArg (σV1 s) hsumξ
    rw [map_add, map_add] at hσsum
    have hR : OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c'.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c))).1 a ξ) s + OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c.1 a ξ) s = (OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c'.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (((Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))).symm (TensorProduct.map θψ (LinearMap.id : (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) →ₗ[(ResidueField B)] (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1))) (Φ (Module.Dual (ResidueField B) V →ₗ[(ResidueField B)] ((OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).cochain (𝒰.baseChange D₀.f (ResidueField B)) 1)) c))).1 a ξ) s) - (OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) (𝟙 (pullback D₀.f (specMap B (ResidueField B)))) (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀' hl₀' 1 (c₀.1 a ξ) s - OModulePresheaf.unitPullback (πX := (pullback.snd D₀.f (specMap B (ResidueField B)))) ψ (𝒱.baseChange D₀.f (ResidueField B)) (𝒰.baseChange D₀.f (ResidueField B)) lam₀ hl₀ 1 (c.1 a ξ) s) := by abel
    change ((-1 : ℤ) ^ ((0 : Fin (0 + 2)) : ℕ)) • (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 0) (σV0 (𝒱.face s 0) (es (𝒱.face s 0) a ξ)) +
        ((-1 : ℤ) ^ ((1 : Fin (0 + 2)) : ℕ)) • (OModulePresheaf.unit (pullback.snd D₀.f (specMap B (ResidueField B)))).res ((𝒱.baseChange D₀.f (ResidueField B)).inter_le_inter_face s 1) (σV0 (𝒱.face s 1) (es (𝒱.face s 1) a ξ)) = _
    rw [hEres1, hEres0, hR, hJe, hIe, eq_sub_of_add_eq' hσsum]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, one_zsmul, neg_one_zsmul]
    abel

  funext s
  rw [OModulePresheaf.d_apply, Fin.sum_univ_two, Pi.add_apply, Pi.sub_apply, Pi.sub_apply]
  exact key s

end S_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_d_eq_unitPullback_hom_obstruction_cocycle_sub_baseChange_of_local_lifts_factor_bare (solution)
