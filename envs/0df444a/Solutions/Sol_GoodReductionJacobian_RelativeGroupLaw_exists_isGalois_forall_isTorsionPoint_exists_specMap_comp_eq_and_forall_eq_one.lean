-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/58556c61-9622-50e0-9004-4ccc85f2e591

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import Theorems.Thm_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace P2mTorsionFieldDescent

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem nsmul_coe (G : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

theorem one_coe (G : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) :
    (G.one t).1 = t ≫ (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  have h := G.one_natural (𝟙 (Spec (CommRingCat.of K))) t t (Category.comp_id t)
  rw [← h]
  rfl

theorem isTorsionPoint_iff_comp (G : RelativeGroupLaw K f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (n : ℕ) (x : SchemeHomOver t f) :
    G.IsTorsionPoint t n x ↔
      x.1 ≫ G.schemeNsmul n = t ≫ (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  rw [RelativeGroupLaw.isTorsionPoint_def, Subtype.ext_iff, nsmul_coe, one_coe]

theorem mono_unit (G : RelativeGroupLaw K f) :
    Mono (G.one (𝟙 (Spec (CommRingCat.of K)))).1 := by
  haveI : Mono ((G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f) := by
    rw [(G.one (𝟙 (Spec (CommRingCat.of K)))).2]
    infer_instance
  exact mono_of_mono _ f

theorem kerFst_comp (G : RelativeGroupLaw K f) (n : ℕ) :
    pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f =
      G.schemeKerStr n := by
  calc pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫ f
      = pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫
          (G.schemeNsmul n ≫ f) := by rw [G.schemeNsmul_over n]
    _ = (pullback.snd (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 ≫
          (G.one (𝟙 (Spec (CommRingCat.of K)))).1) ≫ f := by
        rw [← Category.assoc, pullback.condition]
    _ = G.schemeKerStr n := by
        rw [Category.assoc, (G.one (𝟙 (Spec (CommRingCat.of K)))).2, Category.comp_id]

theorem isTorsionPoint_of_ker (G : RelativeGroupLaw K f) (n : ℕ) {T : Scheme.{u}}
    (y : T ⟶ G.schemeKer n) (t : T ⟶ Spec (CommRingCat.of K)) (ht : y ≫ G.schemeKerStr n = t) :
    ∃ h : (y ≫ pullback.fst _ _) ≫ f = t,
      G.IsTorsionPoint t n ⟨y ≫ pullback.fst _ _, h⟩ := by
  refine ⟨by rw [Category.assoc, kerFst_comp, ht], ?_⟩
  rw [isTorsionPoint_iff_comp]
  change (y ≫ pullback.fst _ _) ≫ G.schemeNsmul n = t ≫ _
  rw [Category.assoc, pullback.condition, ← Category.assoc, ht]

section Kernel

variable (G : RelativeGroupLaw K f) (n : ℕ) [IsAffine (G.schemeKer n)]

noncomputable def kerAlgMap : CommRingCat.of K ⟶ Γ(G.schemeKer n, ⊤) :=
  Spec.preimage ((G.schemeKer n).isoSpec.inv ≫ G.schemeKerStr n)

theorem spec_kerAlgMap :
    Spec.map (kerAlgMap G n) = (G.schemeKer n).isoSpec.inv ≫ G.schemeKerStr n :=
  Spec.map_preimage _

variable {T : Type u} [CommRing T] [Algebra K T]

noncomputable def homToPt (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)) :
    SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f :=
  ⟨Spec.map φ ≫ (G.schemeKer n).isoSpec.inv ≫
      pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1, by
    rw [Category.assoc, Category.assoc, kerFst_comp, ← hφ, Spec.map_comp, spec_kerAlgMap]⟩

@[scoped simp]
theorem homToPt_coe (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)) :
    (homToPt G n φ hφ).1 = Spec.map φ ≫ (G.schemeKer n).isoSpec.inv ≫
      pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1 :=
  rfl

theorem isTorsionPoint_homToPt (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)) :
    G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K T))) n (homToPt G n φ hφ) := by
  have hy : (Spec.map φ ≫ (G.schemeKer n).isoSpec.inv) ≫ G.schemeKerStr n =
      Spec.map (CommRingCat.ofHom (algebraMap K T)) := by
    rw [Category.assoc, ← spec_kerAlgMap, ← Spec.map_comp, hφ]
  obtain ⟨h, ht⟩ := isTorsionPoint_of_ker G n _ _ hy
  have he : homToPt G n φ hφ = ⟨_, h⟩ := Subtype.ext (by simp only [homToPt_coe, Category.assoc])
  rw [he]
  exact ht

theorem homToPt_comp_coe (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T))
    {T' : Type u} [CommRing T'] [Algebra K T'] (j : CommRingCat.of T ⟶ CommRingCat.of T')
    (hj : kerAlgMap G n ≫ (φ ≫ j) = CommRingCat.ofHom (algebraMap K T')) :
    (homToPt G n (φ ≫ j) hj).1 = Spec.map j ≫ (homToPt G n φ hφ).1 := by
  simp only [homToPt_coe, Spec.map_comp, Category.assoc]

theorem eq_of_homToPt_coe_eq {φ φ' : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T}
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T))
    (hφ' : kerAlgMap G n ≫ φ' = CommRingCat.ofHom (algebraMap K T))
    (h : (homToPt G n φ hφ).1 = (homToPt G n φ' hφ').1) : φ = φ' := by
  haveI := mono_unit G
  haveI : Mono ((G.schemeKer n).isoSpec.inv ≫
      pullback.fst (G.schemeNsmul n) (G.one (𝟙 (Spec (CommRingCat.of K)))).1) := inferInstance
  rw [homToPt_coe, homToPt_coe] at h
  exact Spec.map_injective ((cancel_mono _).mp h)

theorem exists_homToPt_eq (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K T))) f)
    (hx : G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K T))) n x) :
    ∃ (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of T)
      (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K T)), homToPt G n φ hφ = x := by
  rw [isTorsionPoint_iff_comp] at hx
  refine ⟨Spec.preimage (pullback.lift x.1 _ hx ≫ (G.schemeKer n).isoSpec.hom), ?_, ?_⟩
  · apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, spec_kerAlgMap, Category.assoc, Iso.hom_inv_id_assoc,
      pullback.lift_snd]
  · apply Subtype.ext
    simp only [homToPt_coe, Spec.map_preimage, Category.assoc, Iso.hom_inv_id_assoc,
      pullback.lift_fst]

end Kernel

section Structure

variable (G : RelativeGroupLaw K f)
  (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    G.mul t x y = G.mul t y x)
  (hA : AbelianSchemePropertyBundle K f) (n : ℕ) (hn : IsUnit (n : K))

include hcomm hA hn in
theorem isFinite_schemeKerStr : IsFinite (G.schemeKerStr n) := by
  haveI := (GoodReductionJacobian.RelativeGroupLaw.isFinite_and_flat_schemeNsmul_of_isUnit
    G hA hcomm n hn).1
  infer_instance

include hcomm hA hn in
theorem isAffine_schemeKer : IsAffine (G.schemeKer n) := by
  haveI := isFinite_schemeKerStr G hcomm hA n hn
  exact isAffine_of_isAffineHom (G.schemeKerStr n)

include hcomm hn in
theorem formallyUnramified_schemeKerStr (d : ℕ) [SmoothOfRelativeDimension d f] :
    FormallyUnramified (G.schemeKerStr n) := by
  haveI := GoodReductionJacobian.RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
    G hcomm d n hn
  infer_instance

theorem finite_kerAlgMap [IsAffine (G.schemeKer n)] (hfin : IsFinite (G.schemeKerStr n)) :
    (kerAlgMap G n).hom.Finite := by
  rw [← IsFinite.SpecMap_iff, spec_kerAlgMap]
  infer_instance

theorem formallyUnramified_kerAlgMap [IsAffine (G.schemeKer n)]
    (h : FormallyUnramified (G.schemeKerStr n)) : (kerAlgMap G n).hom.FormallyUnramified := by
  rw [← HasRingHomProperty.Spec_iff (P := @FormallyUnramified), spec_kerAlgMap]
  exact MorphismProperty.RespectsIso.precomp (P := @FormallyUnramified) _ _ h

end Structure

section Field

variable (G : RelativeGroupLaw K f) (n : ℕ) [IsAffine (G.schemeKer n)]
  (Ω : Type u) [Field Ω] [Algebra K Ω]

def torsionCoords : Set Ω :=
  {y | ∃ (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω),
    kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω) ∧ ∃ a, φ.hom a = y}

noncomputable def torsionField : IntermediateField K Ω :=
  IntermediateField.adjoin K (torsionCoords G n Ω)

theorem image_torsionCoords_subset (σ : Ω ≃ₐ[K] Ω) :
    σ '' torsionCoords G n Ω ⊆ torsionCoords G n Ω := by
  rintro _ ⟨y, ⟨φ, hφ, a, rfl⟩, rfl⟩
  refine ⟨φ ≫ CommRingCat.ofHom (σ : Ω →+* Ω), ?_, a, rfl⟩
  rw [← Category.assoc, hφ, ← CommRingCat.ofHom_comp]
  congr 1
  exact σ.toAlgHom.comp_algebraMap

theorem normal_torsionField [Normal K Ω] : Normal K (torsionField G n Ω) := by
  rw [IntermediateField.normal_iff_forall_map_le']
  intro σ
  rw [torsionField, IntermediateField.adjoin_map]
  exact IntermediateField.adjoin.mono K _ _ (image_torsionCoords_subset G n Ω σ)

noncomputable def restrictHom (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω)) :
    Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of (torsionField G n Ω) :=
  CommRingCat.ofHom (φ.hom.codRestrict (torsionField G n Ω)
    (fun a => IntermediateField.subset_adjoin K _ ⟨φ, hφ, a, rfl⟩))

theorem restrictHom_comp (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω)) :
    restrictHom G n Ω φ hφ ≫ CommRingCat.ofHom (algebraMap (torsionField G n Ω) Ω) = φ := by
  ext a
  rfl

theorem kerAlgMap_comp_restrictHom (φ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of Ω)
    (hφ : kerAlgMap G n ≫ φ = CommRingCat.ofHom (algebraMap K Ω)) :
    kerAlgMap G n ≫ restrictHom G n Ω φ hφ =
      CommRingCat.ofHom (algebraMap K (torsionField G n Ω)) := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  apply Subtype.ext
  change φ.hom ((kerAlgMap G n).hom r) = ((algebraMap K (torsionField G n Ω) r : _) : Ω)
  have := congrArg (fun ψ : CommRingCat.of K ⟶ CommRingCat.of Ω => ψ.hom r) hφ
  simpa using this

theorem exists_descent (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f)
    (hx : G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x) :
    ∃ z : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) f,
      G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) n z ∧
      Spec.map (CommRingCat.ofHom (algebraMap (torsionField G n Ω) Ω)) ≫ z.1 = x.1 := by
  obtain ⟨φ, hφ, rfl⟩ := exists_homToPt_eq G n x hx
  refine ⟨homToPt G n (restrictHom G n Ω φ hφ) (kerAlgMap_comp_restrictHom G n Ω φ hφ),
    isTorsionPoint_homToPt G n _ _, ?_⟩
  have hj : kerAlgMap G n ≫ (restrictHom G n Ω φ hφ ≫
      CommRingCat.ofHom (algebraMap (torsionField G n Ω) Ω)) =
      CommRingCat.ofHom (algebraMap K Ω) := by rw [restrictHom_comp, hφ]
  rw [← homToPt_comp_coe G n _ (kerAlgMap_comp_restrictHom G n Ω φ hφ) _ hj]
  simp only [homToPt_coe, restrictHom_comp]

theorem eq_one_of_forall_comp_eq [Normal K Ω] (τ : torsionField G n Ω ≃ₐ[K] torsionField G n Ω)
    (hτ : ∀ z : SchemeHomOver
        (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) f,
      G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K (torsionField G n Ω)))) n z →
      Spec.map (CommRingCat.ofHom (τ : torsionField G n Ω →+* torsionField G n Ω)) ≫ z.1 = z.1) :
    τ = 1 := by

  have hfix : ∀ y ∈ torsionCoords G n Ω, τ.liftNormal Ω y = y := by
    rintro _ ⟨φ, hφ, a, rfl⟩
    have hj : kerAlgMap G n ≫ (restrictHom G n Ω φ hφ ≫
        CommRingCat.ofHom (τ : torsionField G n Ω →+* torsionField G n Ω)) =
        CommRingCat.ofHom (algebraMap K (torsionField G n Ω)) := by
      rw [← Category.assoc, kerAlgMap_comp_restrictHom, ← CommRingCat.ofHom_comp]
      congr 1
      exact τ.toAlgHom.comp_algebraMap
    have h1 := hτ _ (isTorsionPoint_homToPt G n _ (kerAlgMap_comp_restrictHom G n Ω φ hφ))
    rw [← homToPt_comp_coe G n _ (kerAlgMap_comp_restrictHom G n Ω φ hφ) _ hj] at h1
    have h2 := eq_of_homToPt_coe_eq G n hj (kerAlgMap_comp_restrictHom G n Ω φ hφ) h1
    have h3 := congrArg (fun ψ : Γ(G.schemeKer n, ⊤) ⟶ CommRingCat.of (torsionField G n Ω) =>
      algebraMap (torsionField G n Ω) Ω (ψ.hom a)) h2
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at h3
    rw [RingHom.coe_coe, ← AlgEquiv.liftNormal_commutes τ Ω] at h3
    exact h3

  have hfixL : ∀ y ∈ torsionField G n Ω, τ.liftNormal Ω y = y := by
    intro y hy
    induction hy using IntermediateField.adjoin_induction with
    | mem y hy => exact hfix y hy
    | algebraMap r => exact (τ.liftNormal Ω).commutes r
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | inv x _ hx => rw [map_inv₀, hx]
    | mul x y _ _ hx hy => rw [map_mul, hx, hy]

  apply AlgEquiv.ext
  intro w
  apply Subtype.ext
  rw [AlgEquiv.one_apply]
  calc ((τ w : torsionField G n Ω) : Ω) = τ.liftNormal Ω (w : Ω) :=
        (AlgEquiv.liftNormal_commutes τ Ω w).symm
    _ = w := hfixL _ w.2

end Field

end P2mTorsionFieldDescent
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one.P2mTorsionFieldDescent"

open P2mTorsionFieldDescent in

theorem solution (K : Type u) [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
    (G : RelativeGroupLaw K f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (hA : AbelianSchemePropertyBundle K f) (d : ℕ) [SmoothOfRelativeDimension d f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (Ω : Type u) [Field Ω] [Algebra K Ω] [Normal K Ω] :
    ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧
      (∀ x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) f,
        G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) n x →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z ∧
          Spec.map (CommRingCat.ofHom (algebraMap L Ω)) ≫ z.1 = x.1) ∧
      (∀ τ : L ≃ₐ[K] L,
        (∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) f,
          G.IsTorsionPoint (Spec.map (CommRingCat.ofHom (algebraMap K L))) n z →
          Spec.map (CommRingCat.ofHom (τ : L →+* L)) ≫ z.1 = z.1) → τ = 1) := by
  have hnU : IsUnit (n : K) := isUnit_iff_ne_zero.mpr hn
  haveI : IsAffine (G.schemeKer n) := isAffine_schemeKer G hcomm hA n hnU

  letI : Algebra K Γ(G.schemeKer n, ⊤) := (kerAlgMap G n).hom.toAlgebra
  haveI : Module.Finite K Γ(G.schemeKer n, ⊤) :=
    finite_kerAlgMap G n (isFinite_schemeKerStr G hcomm hA n hnU)
  haveI : Algebra.FormallyUnramified K Γ(G.schemeKer n, ⊤) :=
    formallyUnramified_kerAlgMap G n (formallyUnramified_schemeKerStr G hcomm n hnU d)
  obtain ⟨L₁, hfd₁, hgal₁, hL₁⟩ :=
    Algebra.FormallyUnramified.exists_isGalois_forall_algHom_apply_mem K Γ(G.schemeKer n, ⊤) Ω

  have hle : torsionField G n Ω ≤ L₁ := by
    rw [torsionField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨φ, hφ, a, rfl⟩
    let φa : Γ(G.schemeKer n, ⊤) →ₐ[K] Ω :=
      { φ.hom with
        commutes' := fun r => congrArg (fun ψ : CommRingCat.of K ⟶ CommRingCat.of Ω => ψ.hom r) hφ }
    exact hL₁ φa a
  haveI : FiniteDimensional K L₁ := hfd₁
  haveI : IsGalois K L₁ := hgal₁
  haveI : FiniteDimensional K (torsionField G n Ω) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  haveI : Algebra.IsSeparable K (torsionField G n Ω) :=
    Algebra.IsSeparable.of_algHom K _ (IntermediateField.inclusion hle)
  haveI : Normal K (torsionField G n Ω) := normal_torsionField G n Ω
  haveI : IsGalois K (torsionField G n Ω) := IsGalois.mk
  exact ⟨torsionField G n Ω, inferInstance, inferInstance, fun x hx => exists_descent G n Ω x hx,
    fun τ hτ => eq_one_of_forall_comp_eq G n Ω τ hτ⟩

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isGalois_forall_isTorsionPoint_exists_specMap_comp_eq_and_forall_eq_one (solution)
