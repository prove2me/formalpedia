-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_endo_comap_inter_of_slices
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5d33c188-0fe0-5b28-9092-08f21f0cab47

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_IsRegluingBy
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isAffineOpen_preimage_and_isPushout_of_isPullback
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_exists_appLE_apply_eq_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq
import Theorems.Thm_Algebra_IsPushout_exists_algHom_slice_eq_of_flat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices.GoodReductionJacobian CerednikDrinfeld IsLocalRing AlgebraicGeometry.Scheme.TwoAffineOpenCover"

open scoped TensorProduct

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "RelativeGroupLaw BareDeformation"
namespace P2mFatEndo
p2m_open "GoodReductionJacobian"

universe u

noncomputable def ringMap {X : Scheme.{u}} (U : X.Opens) (θ : (U : Scheme.{u}) ⟶ U) : Γ(X, U) ⟶ Γ(X, U) :=
  U.topIso.inv ≫ θ.appTop ≫ U.topIso.hom

theorem toSpecΓ_ringMap {X : Scheme.{u}} (U : X.Opens) (θ : (U : Scheme.{u}) ⟶ U) :
    θ ≫ U.toSpecΓ = U.toSpecΓ ≫ Spec.map (ringMap U θ) := by
  rw [Scheme.Opens.toSpecΓ, ← Category.assoc, Scheme.toSpecΓ_naturality, Category.assoc, Category.assoc, ← Spec.map_comp,
    ← Spec.map_comp, ringMap, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem ringMap_comp {X : Scheme.{u}} (U : X.Opens) (θ θ' : (U : Scheme.{u}) ⟶ U) :
    ringMap U (θ ≫ θ') = ringMap U θ' ≫ ringMap U θ := by
  simp only [ringMap, Scheme.Hom.comp_appTop, Category.assoc, Iso.hom_inv_id_assoc]

theorem ringMap_id {X : Scheme.{u}} (U : X.Opens) : ringMap U (𝟙 _) = 𝟙 _ := by
  rw [ringMap, show Scheme.Hom.appTop (𝟙 (U : Scheme.{u})) = 𝟙 _ from rfl, Category.id_comp, Iso.inv_hom_id]

theorem isoSpec_ringMap {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (θ : (U : Scheme.{u}) ⟶ U) :
    θ ≫ hU.isoSpec.hom = hU.isoSpec.hom ≫ Spec.map (ringMap U θ) := by
  rw [IsAffineOpen.isoSpec_hom]; exact toSpecΓ_ringMap U θ

theorem flat_sections {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [hf : Flat f] {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    Module.Flat R Γ(X, U) := by
  have h := HasRingHomProperty.appLE @Flat f hf ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩ (by simp)
  have h' : RingHom.Flat ((Scheme.ΓSpecIso (.of R)).inv ≫ f.appLE ⊤ U le_top).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Flat.comp (RingHom.Flat.of_bijective (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact h'

theorem fromSpec_comp_eq {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) {U : X.Opens}
    (hU : IsAffineOpen U) :
    letI := algebraOfHom f U
    hU.fromSpec ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) := by
  letI := algebraOfHom f U
  have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (.of R))) hU
    (show U ≤ f ⁻¹ᵁ ⊤ by simp)
  rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  rfl

end GoodReductionJacobian.P2mFatEndo

open GoodReductionJacobian.P2mFatEndo

namespace GoodReductionJacobian p2m_export "GoodReductionJacobian" "RelativeGroupLaw BareDeformation" namespace P2mFatEndo end GoodReductionJacobian.P2mFatEndo
p2m_open_scoped "GoodReductionJacobian" in
theorem GoodReductionJacobian.P2mFatEndo.overlap_endo
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (δ : B →+* B') (hδ : (algebraMap B' B₁).comp δ = algebraMap B B₁)
    (p₀ p₁ p₂ : B' →+* B) (hp₀δ : p₀.comp δ = RingHom.id B) (hp₁δ : p₁.comp δ = RingHom.id B) (hp₂δ : p₂.comp δ = RingHom.id B)
    (hp₀ : (algebraMap B B₁).comp p₀ = algebraMap B' B₁) (hp₁ : (algebraMap B B₁).comp p₁ = algebraMap B' B₁)
    (hp₂ : (algebraMap B B₁).comp p₂ = algebraMap B' B₁)
    (hinj : ∀ x y : B', p₀ x = p₀ y → p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hsurj : ∀ b₀ b₁ b₂ : B, algebraMap B B₁ b₀ = algebraMap B B₁ b₁ → algebraMap B B₁ b₁ = algebraMap B B₁ b₂ →
      ∃ x : B', p₀ x = b₀ ∧ p₁ x = b₁ ∧ p₂ x = b₂)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) (D₀' : BareDeformation f₁ L₁ B')
    (h' : D₀'.A ⟶ D₀.A) [IsAffineHom h'] (hc' : IsPullback h' D₀'.f D₀.f (Spec.map (CommRingCat.ofHom δ)))
    (k₀ k₁ k₂ : D₀.A ⟶ D₀'.A) (hk₀ : k₀ ≫ h' = 𝟙 D₀.A) (hk₁ : k₁ ≫ h' = 𝟙 D₀.A) (hk₂ : k₂ ≫ h' = 𝟙 D₀.A)
    (hk₀f : k₀ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₀)) (hk₁f : k₁ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₁))
    (hk₂f : k₂ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₂))
    (U : D₀.A.Opens) (hU : IsAffineOpen U)
    (τU τU' : (U : Scheme.{0}) ⟶ U)
    (hτB : τU ≫ U.ι ≫ D₀.f = U.ι ≫ D₀.f) (hτg : (D₀.g ∣_ U) ≫ τU = D₀.g ∣_ U)
    (hτ'B : τU' ≫ U.ι ≫ D₀.f = U.ι ≫ D₀.f) (hτ'g : (D₀.g ∣_ U) ≫ τU' = D₀.g ∣_ U) :
    ∃ α : (↑(h' ⁻¹ᵁ U) : Scheme.{0}) ⟶ ↑(h' ⁻¹ᵁ U),
      α ≫ (h' ⁻¹ᵁ U).ι ≫ D₀'.f = (h' ⁻¹ᵁ U).ι ≫ D₀'.f ∧
      (D₀'.g ∣_ h' ⁻¹ᵁ U) ≫ α = D₀'.g ∣_ h' ⁻¹ᵁ U ∧
      (∀ κ : (U : Scheme.{0}) ⟶ ↑(h' ⁻¹ᵁ U), κ ≫ (h' ⁻¹ᵁ U).ι = U.ι ≫ k₀ → κ ≫ α = κ) ∧
      (∀ κ : (U : Scheme.{0}) ⟶ ↑(h' ⁻¹ᵁ U), κ ≫ (h' ⁻¹ᵁ U).ι = U.ι ≫ k₁ → τU ≫ κ = κ ≫ α) ∧
      (∀ κ : (U : Scheme.{0}) ⟶ ↑(h' ⁻¹ᵁ U), κ ≫ (h' ⁻¹ᵁ U).ι = U.ι ≫ k₂ → τU' ≫ κ = κ ≫ α) := by
  classical

  haveI hflat : Flat D₀.f := by haveI := D₀.bundle.smooth; infer_instance
  letI algBB' : Algebra B B' := δ.toAlgebra
  letI algM : Algebra B Γ(D₀.A, U) := algebraOfHom D₀.f U
  letI algN : Algebra B' Γ(D₀'.A, h' ⁻¹ᵁ U) := algebraOfHom D₀'.f (h' ⁻¹ᵁ U)
  letI algMN : Algebra Γ(D₀.A, U) Γ(D₀'.A, h' ⁻¹ᵁ U) := (h'.appLE U (h' ⁻¹ᵁ U) le_rfl).hom.toAlgebra
  letI algBN : Algebra B Γ(D₀'.A, h' ⁻¹ᵁ U) := ((algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U)).comp δ).toAlgebra
  haveI instBB'N : IsScalarTower B B' Γ(D₀'.A, h' ⁻¹ᵁ U) := IsScalarTower.of_algebraMap_eq (fun b => rfl)
  have h094 := AlgebraicGeometry.Scheme.Hom.isAffineOpen_preimage_and_isPushout_of_isPullback (A := B) (B := B')
    D₀.f D₀'.f h' hc' U hU
  have hU' : IsAffineOpen (h' ⁻¹ᵁ U) := h094.1

  haveI instBMN : IsScalarTower B Γ(D₀.A, U) Γ(D₀'.A, h' ⁻¹ᵁ U) := by
    refine IsScalarTower.of_algebraMap_eq (fun b => ?_)
    change algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U) (δ b) = (h'.appLE U (h' ⁻¹ᵁ U) le_rfl).hom (algebraMap B Γ(D₀.A, U) b)
    have key : Spec.map (CommRingCat.ofHom δ ≫ CommRingCat.ofHom (algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U))) =
        Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, U)) ≫ h'.appLE U (h' ⁻¹ᵁ U) le_rfl) := by
      rw [Spec.map_comp, Spec.map_comp, ← fromSpec_comp_eq D₀'.f hU', ← fromSpec_comp_eq D₀.f hU, ← Category.assoc,
        IsAffineOpen.SpecMap_appLE_fromSpec h' hU hU' le_rfl]
      simp only [Category.assoc, hc'.w]
    have k2 := congrArg Spec.preimage key
    rw [Spec.preimage_map, Spec.preimage_map] at k2
    exact congrArg (fun φ : CommRingCat.of B ⟶ _ => φ.hom b) k2
  haveI hPO : Algebra.IsPushout B B' Γ(D₀.A, U) Γ(D₀'.A, h' ⁻¹ᵁ U) := @h094.2 algBN instBB'N instBMN
  haveI : Module.Flat B Γ(D₀.A, U) := flat_sections D₀.f hU

  have hkB : ∀ (i : Fin 3), (![k₀, k₁, k₂] i) ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom (![p₀, p₁, p₂] i)) := by
    intro i; fin_cases i <;> assumption
  have hkh : ∀ (i : Fin 3), (![k₀, k₁, k₂] i) ≫ h' = 𝟙 D₀.A := by intro i; fin_cases i <;> assumption
  have hslice := fun i : Fin 3 =>
    AlgebraicGeometry.Scheme.Hom.exists_appLE_apply_eq_of_comp_eq_id D₀.f D₀'.f h' (![k₀, k₁, k₂] i) (hkh i) (![p₀, p₁, p₂] i) (hkB i) U
  choose hle he1 he2 using hslice
  have hpδ : ∀ (i : Fin 3) (b : B), (![p₀, p₁, p₂] i) (δ b) = b := by
    intro i b
    fin_cases i
    · exact congrArg (fun g : B →+* B => g b) hp₀δ
    · exact congrArg (fun g : B →+* B => g b) hp₁δ
    · exact congrArg (fun g : B →+* B => g b) hp₂δ
  let e : Fin 3 → (Γ(D₀'.A, h' ⁻¹ᵁ U) →ₐ[B] Γ(D₀.A, U)) := fun i =>
    { ((![k₀, k₁, k₂] i).appLE (h' ⁻¹ᵁ U) U (hle i)).hom with
      commutes' := fun b => by
        change ((![k₀, k₁, k₂] i).appLE (h' ⁻¹ᵁ U) U (hle i)).hom (algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U) (δ b)) = algebraMap B Γ(D₀.A, U) b
        rw [he2, hpδ] }
  have he_apply : ∀ (i : Fin 3) (n : Γ(D₀'.A, h' ⁻¹ᵁ U)), e i n = ((![k₀, k₁, k₂] i).appLE (h' ⁻¹ᵁ U) U (hle i)).hom n :=
    fun i n => rfl
  let P : Fin 3 → (B' →ₐ[B] B) := fun i =>
    { (![p₀, p₁, p₂] i) with commutes' := fun b => hpδ i b }
  have hP_apply : ∀ (i : Fin 3) (x : B'), P i x = (![p₀, p₁, p₂] i) x := fun i x => rfl
  have hP : ∀ (i : Fin 3) (x : B'), algebraMap B B₁ (P i x) = algebraMap B' B₁ x := by
    intro i x; fin_cases i
    · exact congrArg (fun g : B' →+* B₁ => g x) hp₀
    · exact congrArg (fun g : B' →+* B₁ => g x) hp₁
    · exact congrArg (fun g : B' →+* B₁ => g x) hp₂
  have hPinj : ∀ x y : B', (∀ i, P i x = P i y) → x = y := fun x y h => hinj x y (h 0) (h 1) (h 2)
  have hPsurj : ∀ b : Fin 3 → B, (∀ i j, algebraMap B B₁ (b i) = algebraMap B B₁ (b j)) → ∃ x : B', ∀ i, P i x = b i := by
    intro b hb
    obtain ⟨x, h0, h1, h2⟩ := hsurj (b 0) (b 1) (b 2) (hb 0 1) (hb 1 2)
    exact ⟨x, fun i => by fin_cases i <;> assumption⟩
  have heM : ∀ (i : Fin 3) (m : Γ(D₀.A, U)), e i (algebraMap Γ(D₀.A, U) Γ(D₀'.A, h' ⁻¹ᵁ U) m) = m := fun i m => he1 i m
  have heB : ∀ (i : Fin 3) (x : B'), e i (algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U) x) = algebraMap B Γ(D₀.A, U) (P i x) := fun i x => he2 i x

  have hιf : U.ι ≫ D₀.f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, U))) := by
    rw [← fromSpec_comp_eq D₀.f hU, ← IsAffineOpen.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have mkEndo : ∀ (θ : (U : Scheme.{0}) ⟶ U), θ ≫ U.ι ≫ D₀.f = U.ι ≫ D₀.f → (D₀.g ∣_ U) ≫ θ = D₀.g ∣_ U →
      ∃ t : Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U), (∀ m, t m = (ringMap U θ).hom m) ∧
        (∀ m, t m - m ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, U))) := by
    intro θ hθB hθg
    have hcomm : ∀ b : B, (ringMap U θ).hom (algebraMap B Γ(D₀.A, U) b) = algebraMap B Γ(D₀.A, U) b := by
      have key : CommRingCat.ofHom (algebraMap B Γ(D₀.A, U)) ≫ ringMap U θ = CommRingCat.ofHom (algebraMap B Γ(D₀.A, U)) := by
        have h1 : θ ≫ U.ι ≫ D₀.f = hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap B Γ(D₀.A, U)) ≫ ringMap U θ) := by
          rw [hιf, ← Category.assoc, isoSpec_ringMap hU, Category.assoc, ← Spec.map_comp]
        rw [hθB, hιf, cancel_epi] at h1
        have h2 := congrArg Spec.preimage h1
        rwa [Spec.preimage_map, Spec.preimage_map, eq_comm] at h2
      intro b
      exact congrArg (fun φ : CommRingCat.of B ⟶ _ => φ.hom b) key
    refine ⟨{ (ringMap U θ).hom with commutes' := hcomm }, fun m => rfl, fun m => ?_⟩
    have hred := AlgebraicGeometry.specMap_comp_fromSpec_eq_specMap_comp_of_morphismRestrict_comp_eq hπ D₀.f f₁ D₀.g D₀.cart U hU
      θ hθg
    have hθ' : hU.isoSpec.inv ≫ θ = Spec.map (ringMap U θ) ≫ hU.isoSpec.inv := by
      rw [← cancel_mono hU.isoSpec.hom, Category.assoc, Category.assoc, isoSpec_ringMap hU, Iso.inv_hom_id_assoc,
        Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc (hU.isoSpec.inv), hθ', Category.assoc, IsAffineOpen.isoSpec_inv_ι, ← Category.assoc,
      cancel_mono hU.fromSpec, ← Spec.map_comp] at hred
    have h2 := congrArg Spec.preimage hred
    rw [Spec.preimage_map, Spec.preimage_map] at h2
    have h3 := congrArg (fun φ : CommRingCat.of Γ(D₀.A, U) ⟶ _ => φ.hom m) h2
    change Ideal.Quotient.mk _ m = Ideal.Quotient.mk _ ((ringMap U θ).hom m) at h3
    rw [← Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    exact h3.symm
  obtain ⟨t₁, ht₁, ht₁J⟩ := mkEndo τU hτB hτg
  obtain ⟨t₂, ht₂, ht₂J⟩ := mkEndo τU' hτ'B hτ'g
  let t : Fin 3 → (Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U)) := ![AlgHom.id B _, t₁, t₂]
  have htJ : ∀ (i : Fin 3) (m : Γ(D₀.A, U)), t i m - m ∈ (RingHom.ker (algebraMap B B₁)).map (algebraMap B Γ(D₀.A, U)) := by
    intro i m; fin_cases i
    · change m - m ∈ _; rw [sub_self]; exact Ideal.zero_mem _
    · exact ht₁J m
    · exact ht₂J m

  obtain ⟨σ, hσ, hσJ, hσuniq⟩ := Algebra.IsPushout.exists_algHom_slice_eq_of_flat (B := B) (B₁ := B₁) (B' := B')
    (M := Γ(D₀.A, U)) (N := Γ(D₀'.A, h' ⁻¹ᵁ U)) hπ P hP hPinj hPsurj e heM heB t htJ
  let φh : Γ(D₀'.A, h' ⁻¹ᵁ U) ⟶ Γ(D₀'.A, h' ⁻¹ᵁ U) := CommRingCat.ofHom σ.toRingHom
  let α : (↑(h' ⁻¹ᵁ U) : Scheme.{0}) ⟶ ↑(h' ⁻¹ᵁ U) := hU'.isoSpec.hom ≫ Spec.map φh ≫ hU'.isoSpec.inv
  have hα : α ≫ hU'.isoSpec.hom = hU'.isoSpec.hom ≫ Spec.map φh := by
    simp only [α, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hαB : α ≫ (h' ⁻¹ᵁ U).ι ≫ D₀'.f = (h' ⁻¹ᵁ U).ι ≫ D₀'.f := by
    have hc : CommRingCat.ofHom (algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U)) ≫ φh = CommRingCat.ofHom (algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U)) := by
      apply CommRingCat.hom_ext; exact σ.comp_algebraMap
    simp only [α, Category.assoc]
    rw [IsAffineOpen.isoSpec_inv_ι_assoc, fromSpec_comp_eq D₀'.f hU', ← Spec.map_comp, hc, ← fromSpec_comp_eq D₀'.f hU',
      ← IsAffineOpen.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  have hαg : (D₀'.g ∣_ h' ⁻¹ᵁ U) ≫ α = D₀'.g ∣_ h' ⁻¹ᵁ U := by
    set J : Ideal Γ(D₀'.A, h' ⁻¹ᵁ U) := (RingHom.ker (algebraMap B' B₁)).map (algebraMap B' Γ(D₀'.A, h' ⁻¹ᵁ U)) with hJdef
    have hnat := Scheme.Opens.toSpecΓ_naturality D₀'.g (h' ⁻¹ᵁ U)
    have hkill : ∀ c ∈ J, (D₀'.g.app (h' ⁻¹ᵁ U)).hom c = 0 := by
      intro c hc
      induction hc using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨i, hi, rfl⟩ := hx
        rw [algebraMap_algebraOfHom]
        have s1 : (D₀'.g.app (h' ⁻¹ᵁ U)).hom ((D₀'.f.appLE ⊤ (h' ⁻¹ᵁ U) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i)) =
            (D₀'.A.presheaf.map (homOfLE (le_top : h' ⁻¹ᵁ U ≤ ⊤)).op ≫ D₀'.g.app (h' ⁻¹ᵁ U)).hom
              (D₀'.f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i)) := rfl
        rw [s1, D₀'.g.naturality]
        show (A₁.presheaf.map _).hom ((D₀'.g.app ⊤).hom (D₀'.f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i))) = 0
        have s2 : (D₀'.g.app ⊤).hom (D₀'.f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B')).inv.hom i)) =
            ((Scheme.ΓSpecIso (CommRingCat.of B')).inv ≫ (D₀'.g ≫ D₀'.f).appTop).hom i := by
          rw [Scheme.Hom.comp_appTop]; rfl
        rw [s2, D₀'.cart.w, Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
        show (A₁.presheaf.map _).hom (f₁.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of B₁)).inv.hom (algebraMap B' B₁ i))) = 0
        rw [RingHom.mem_ker.mp hi, map_zero, map_zero, map_zero]
      | zero => exact map_zero _
      | add x y hx hy ihx ihy => rw [map_add, ihx, ihy, add_zero]
      | smul a x hx ihx => rw [smul_eq_mul, map_mul, ihx, mul_zero]
    let ℓ : (Γ(D₀'.A, h' ⁻¹ᵁ U) ⧸ J) →+* Γ(A₁, D₀'.g ⁻¹ᵁ (h' ⁻¹ᵁ U)) := Ideal.Quotient.lift _ (D₀'.g.app (h' ⁻¹ᵁ U)).hom hkill
    have hfac : D₀'.g.app (h' ⁻¹ᵁ U) = CommRingCat.ofHom (Ideal.Quotient.mk J) ≫ CommRingCat.ofHom ℓ :=
      CommRingCat.hom_ext (RingHom.ext fun c => rfl)
    have hφmk : φh ≫ CommRingCat.ofHom (Ideal.Quotient.mk J) = CommRingCat.ofHom (Ideal.Quotient.mk J) := by
      refine CommRingCat.hom_ext (RingHom.ext fun c => ?_)
      show Ideal.Quotient.mk J (σ c) = Ideal.Quotient.mk J c
      rw [Ideal.Quotient.eq]
      exact hσJ c
    calc (D₀'.g ∣_ h' ⁻¹ᵁ U) ≫ hU'.isoSpec.hom ≫ Spec.map φh ≫ hU'.isoSpec.inv
        = ((D₀'.g ∣_ h' ⁻¹ᵁ U) ≫ (h' ⁻¹ᵁ U).toSpecΓ) ≫ Spec.map φh ≫ hU'.isoSpec.inv := by rw [hU'.isoSpec_hom, Category.assoc]
      _ = (D₀'.g ⁻¹ᵁ (h' ⁻¹ᵁ U)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ℓ) ≫ (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Spec.map φh) ≫
            hU'.isoSpec.inv := by rw [← hnat, hfac, Spec.map_comp]; simp only [Category.assoc]
      _ = (D₀'.g ⁻¹ᵁ (h' ⁻¹ᵁ U)).toSpecΓ ≫ Spec.map (CommRingCat.ofHom ℓ) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ hU'.isoSpec.inv := by
            rw [← Spec.map_comp, hφmk]
      _ = ((D₀'.g ∣_ h' ⁻¹ᵁ U) ≫ (h' ⁻¹ᵁ U).toSpecΓ) ≫ hU'.isoSpec.inv := by rw [← hnat, hfac, Spec.map_comp]; simp only [Category.assoc]
      _ = D₀'.g ∣_ h' ⁻¹ᵁ U := by rw [← hU'.isoSpec_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

  have hA : ∀ (i : Fin 3) (κ : (U : Scheme.{0}) ⟶ ↑(h' ⁻¹ᵁ U)), κ ≫ (h' ⁻¹ᵁ U).ι = U.ι ≫ (![k₀, k₁, k₂] i) →
      κ ≫ hU'.isoSpec.hom = hU.isoSpec.hom ≫ Spec.map ((![k₀, k₁, k₂] i).appLE (h' ⁻¹ᵁ U) U (hle i)) := by
    intro i κ hκ
    have hκ' : κ = (![k₀, k₁, k₂] i).resLE (h' ⁻¹ᵁ U) U (hle i) := by
      rw [← cancel_mono (h' ⁻¹ᵁ U).ι, hκ, Scheme.Hom.resLE_comp_ι]
    rw [hκ', IsAffineOpen.isoSpec_hom, IsAffineOpen.isoSpec_hom]
    exact (Scheme.Opens.toSpecΓ_SpecMap_appLE _ _ _ _).symm
  have hE : ∀ (i : Fin 3), φh ≫ (![k₀, k₁, k₂] i).appLE (h' ⁻¹ᵁ U) U (hle i) =
      (![k₀, k₁, k₂] i).appLE (h' ⁻¹ᵁ U) U (hle i) ≫ CommRingCat.ofHom ((t i : Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U)) : Γ(D₀.A, U) →+* Γ(D₀.A, U)) := by
    intro i
    apply CommRingCat.hom_ext; apply RingHom.ext; intro n
    exact hσ i n
  have hslice : ∀ (i : Fin 3) (κ : (U : Scheme.{0}) ⟶ ↑(h' ⁻¹ᵁ U)), κ ≫ (h' ⁻¹ᵁ U).ι = U.ι ≫ (![k₀, k₁, k₂] i) →
      (hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ((t i : Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U)) : Γ(D₀.A, U) →+* Γ(D₀.A, U))) ≫ hU.isoSpec.inv)
        ≫ κ = κ ≫ α := by
    intro i κ hκ
    rw [← cancel_mono hU'.isoSpec.hom]
    simp only [Category.assoc]
    rw [hα, ← Category.assoc κ, hA i κ hκ, Category.assoc, Iso.inv_hom_id_assoc, ← Spec.map_comp, ← Spec.map_comp, hE i]
  refine ⟨α, hαB, hαg, ?_, ?_, ?_⟩
  · intro κ hκ
    have h := hslice 0 κ hκ
    have h0 : CommRingCat.ofHom ((t 0 : Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U)) : Γ(D₀.A, U) →+* Γ(D₀.A, U)) = 𝟙 (Γ(D₀.A, U)) := by
      apply CommRingCat.hom_ext; apply RingHom.ext; intro m; rfl
    have h1 : hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ((t 0 : Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U)) : Γ(D₀.A, U) →+* Γ(D₀.A, U)))
        ≫ hU.isoSpec.inv = 𝟙 _ := by
      rw [h0]
      erw [Spec.map_id, Category.id_comp, Iso.hom_inv_id]
    rw [h1, Category.id_comp] at h
    exact h.symm
  · intro κ hκ
    have h := hslice 1 κ hκ
    have h1 : hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ((t 1 : Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U)) : Γ(D₀.A, U) →+* Γ(D₀.A, U)))
        ≫ hU.isoSpec.inv = τU := by
      rw [← cancel_mono hU.isoSpec.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, isoSpec_ringMap hU]
      congr 2
      apply CommRingCat.hom_ext; apply RingHom.ext; intro m
      exact ht₁ m
    rwa [h1] at h
  · intro κ hκ
    have h := hslice 2 κ hκ
    have h1 : hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ((t 2 : Γ(D₀.A, U) →ₐ[B] Γ(D₀.A, U)) : Γ(D₀.A, U) →+* Γ(D₀.A, U)))
        ≫ hU.isoSpec.inv = τU' := by
      rw [← cancel_mono hU.isoSpec.hom, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, isoSpec_ringMap hU]
      congr 2
      apply CommRingCat.hom_ext; apply RingHom.ext; intro m
      exact ht₂ m
    rwa [h1] at h

theorem solution
    (B' B B₁ : Type) [CommRing B'] [CommRing B] [CommRing B₁] [Algebra B' B₁] [Algebra B B₁]
    (hπ : Function.Surjective (algebraMap B B₁))
    (δ : B →+* B') (hδ : (algebraMap B' B₁).comp δ = algebraMap B B₁)
    (p₀ p₁ p₂ : B' →+* B) (hp₀δ : p₀.comp δ = RingHom.id B) (hp₁δ : p₁.comp δ = RingHom.id B) (hp₂δ : p₂.comp δ = RingHom.id B)
    (hp₀ : (algebraMap B B₁).comp p₀ = algebraMap B' B₁) (hp₁ : (algebraMap B B₁).comp p₁ = algebraMap B' B₁)
    (hp₂ : (algebraMap B B₁).comp p₂ = algebraMap B' B₁)
    (hinj : ∀ x y : B', p₀ x = p₀ y → p₁ x = p₁ y → p₂ x = p₂ y → x = y)
    (hsurj : ∀ b₀ b₁ b₂ : B, algebraMap B B₁ b₀ = algebraMap B B₁ b₁ → algebraMap B B₁ b₁ = algebraMap B B₁ b₂ →
      ∃ x : B', p₀ x = b₀ ∧ p₁ x = b₁ ∧ p₂ x = b₂)
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D₀ : BareDeformation f₁ L₁ B) [IsSeparated D₀.f] (D₀' : BareDeformation f₁ L₁ B')
    (h' : D₀'.A ⟶ D₀.A) [IsAffineHom h'] (hc' : IsPullback h' D₀'.f D₀.f (Spec.map (CommRingCat.ofHom δ)))
    (hg' : D₀'.g ≫ h' = D₀.g)
    (k₀ k₁ k₂ : D₀.A ⟶ D₀'.A) (hk₀ : k₀ ≫ h' = 𝟙 D₀.A) (hk₁ : k₁ ≫ h' = 𝟙 D₀.A) (hk₂ : k₂ ≫ h' = 𝟙 D₀.A)
    (hk₀f : k₀ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₀)) (hk₁f : k₁ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₁))
    (hk₂f : k₂ ≫ D₀'.f = D₀.f ≫ Spec.map (CommRingCat.ofHom p₂))
    (𝒰 : D₀.A.OrderedAffineCover)
    {n : ℕ} (t : 𝒰.Idx n)
    (α α' : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑(𝒰.inter t))
    (hαB : α ≫ (𝒰.inter t).ι ≫ D₀.f = (𝒰.inter t).ι ≫ D₀.f) (hαg : (D₀.g ∣_ 𝒰.inter t) ≫ α = D₀.g ∣_ 𝒰.inter t)
    (hα'B : α' ≫ (𝒰.inter t).ι ≫ D₀.f = (𝒰.inter t).ι ≫ D₀.f) (hα'g : (D₀.g ∣_ 𝒰.inter t) ≫ α' = D₀.g ∣_ 𝒰.inter t) :
    ∃ σ : (↑((𝒰.comap h').inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
      σ ≫ ((𝒰.comap h').inter t).ι ≫ D₀'.f = ((𝒰.comap h').inter t).ι ≫ D₀'.f ∧
      (D₀'.g ∣_ (𝒰.comap h').inter t) ≫ σ = D₀'.g ∣_ (𝒰.comap h').inter t ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₀ → κ ≫ σ = κ) ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₁ → α ≫ κ = κ ≫ σ) ∧
      (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ ↑((𝒰.comap h').inter t),
        κ ≫ ((𝒰.comap h').inter t).ι = (𝒰.inter t).ι ≫ k₂ → α' ≫ κ = κ ≫ σ) := by
  classical
  have key : ∀ (W : D₀'.A.Opens), W = h' ⁻¹ᵁ 𝒰.inter t →
      ∃ σ : (W : Scheme.{0}) ⟶ W,
        σ ≫ W.ι ≫ D₀'.f = W.ι ≫ D₀'.f ∧
        (D₀'.g ∣_ W) ≫ σ = D₀'.g ∣_ W ∧
        (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ W, κ ≫ W.ι = (𝒰.inter t).ι ≫ k₀ → κ ≫ σ = κ) ∧
        (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ W, κ ≫ W.ι = (𝒰.inter t).ι ≫ k₁ → α ≫ κ = κ ≫ σ) ∧
        (∀ κ : (↑(𝒰.inter t) : Scheme.{0}) ⟶ W, κ ≫ W.ι = (𝒰.inter t).ι ≫ k₂ → α' ≫ κ = κ ≫ σ) := by
    intro W hW
    subst hW
    exact GoodReductionJacobian.P2mFatEndo.overlap_endo B' B B₁ hπ δ hδ p₀ p₁ p₂ hp₀δ hp₁δ hp₂δ hp₀ hp₁ hp₂ hinj hsurj D₀ D₀' h' hc'
      k₀ k₁ k₂ hk₀ hk₁ hk₂ hk₀f hk₁f hk₂f (𝒰.inter t) (Scheme.OrderedAffineCover.isAffineOpen_inter D₀.f 𝒰 t)
      α α' hαB hαg hα'B hα'g
  exact key ((𝒰.comap h').inter t) (𝒰.comap_inter h' t)

end S_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_endo_comap_inter_of_slices (solution)
