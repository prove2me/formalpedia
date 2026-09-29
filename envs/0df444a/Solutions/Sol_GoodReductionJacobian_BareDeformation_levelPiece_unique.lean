-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.levelPiece_unique
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/287fa9aa-471e-51d9-8310-5bee16819f57

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_etale_schemeKerStr_of_isUnit
import Theorems.Thm_GoodReductionJacobian_BareDeformation_exists_schemeKer_comparison
import Theorems.Thm_GoodReductionJacobian_BareDeformation_levelPiece_isClosedImmersion_finite_flat_finrank
import Theorems.Thm_AlgebraicGeometry_isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_of_isClosedImmersion_of_flat_comp_of_etale
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_restrict_add_finrank_restrict_of_isCompl
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing"

open scoped Quaternion TensorProduct NumberField

universe u
namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp_coe RelativeGroupLaw BareDeformation RelativeGroupLaw.nsmul_succ RelativeGroupLaw.schemeNsmul_over RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul RelativeGroupLaw.isFinite_flat_etale_schemeKerStr_of_isUnit BareDeformation.exists_schemeKer_comparison BareDeformation.levelPiece_isClosedImmersion_finite_flat_finrank"
namespace BareDeformation
p2m_export "GoodReductionJacobian.BareDeformation" "hom A comm cart L bundle g f exists_schemeKer_comparison levelPiece_isClosedImmersion_finite_flat_finrank"
p2m_open "GoodReductionJacobian.BareDeformation GoodReductionJacobian"

section Lift

variable {S B : Type} [CommRing S] [CommRing B] [Algebra B S]
  {Aₛ : Scheme.{0}} {fₛ : Aₛ ⟶ Spec (CommRingCat.of S)} {Lₛ : RelativeGroupLaw S fₛ}
  (D : BareDeformation fₛ Lₛ B)

private theorem _root_.GoodReductionJacobian.BareDeformation.ext_g {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of S)} (Q Q' : SchemeHomOver t fₛ)
    (h : Q.1 ≫ D.g = Q'.1 ≫ D.g) : Q = Q' := by
  apply Subtype.ext
  exact D.cart.hom_ext h (by rw [Q.2, Q'.2])

p2m_export "GoodReductionJacobian.BareDeformation" "ext_g"

private def _root_.GoodReductionJacobian.BareDeformation.pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T ⟶ Spec (CommRingCat.of B))
    (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) (Q : SchemeHomOver t fₛ) :
    SchemeHomOver t' D.f :=
  ⟨Q.1 ≫ D.g, by rw [Category.assoc, D.cart.w, ← Category.assoc, Q.2, ht]⟩

p2m_export "GoodReductionJacobian.BareDeformation" "pushG"
@[scoped simp] theorem pushG_coe {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (Q : SchemeHomOver t fₛ) :
    (D.pushG t t' ht Q).1 = Q.1 ≫ D.g := rfl

private noncomputable def _root_.GoodReductionJacobian.BareDeformation.liftG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B))
    (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) (P : SchemeHomOver t' D.f) :
    SchemeHomOver t fₛ :=
  ⟨D.cart.lift P.1 t (by rw [P.2, ht]), D.cart.lift_snd _ _ _⟩

p2m_export "GoodReductionJacobian.BareDeformation" "liftG"
@[scoped simp] private theorem _root_.GoodReductionJacobian.BareDeformation.liftG_g {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (P : SchemeHomOver t' D.f) :
    (D.liftG t t' ht P).1 ≫ D.g = P.1 :=
  D.cart.lift_fst _ _ _

p2m_export "GoodReductionJacobian.BareDeformation" "liftG_g"
theorem pushG_liftG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (P : SchemeHomOver t' D.f) :
    D.pushG t t' ht (D.liftG t t' ht P) = P :=
  Subtype.ext (D.liftG_g t t' ht P)

theorem liftG_pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht) (Q : SchemeHomOver t fₛ) :
    D.liftG t t' ht (D.pushG t t' ht Q) = Q :=
  D.ext_g _ _ (by rw [liftG_g, pushG_coe])

private theorem _root_.GoodReductionJacobian.BareDeformation.mul_pushG {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S)))
    (P Q : SchemeHomOver t fₛ) :
    (D.L.mul t' (D.pushG t t' ht P) (D.pushG t t' ht Q)).1 = (Lₛ.mul t P Q).1 ≫ D.g := by
  subst ht
  rw [D.hom t P Q]
  rfl

p2m_export "GoodReductionJacobian.BareDeformation" "mul_pushG"

theorem one_g {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S))
    (t' : T ⟶ Spec (CommRingCat.of B)) (ht : t' = t ≫ Spec.map (CommRingCat.ofHom (algebraMap B S))) :
    (Lₛ.one t).1 ≫ D.g = (D.L.one t').1 := by
  set u := D.pushG t t' ht (Lₛ.one t) with hu
  have h1 : D.L.mul t' u u = u := by
    apply Subtype.ext
    rw [hu, D.mul_pushG t t' ht, Lₛ.one_mul, pushG_coe]
  letI := D.L.pointGroup t'
  have h2 : u = 1 := mul_eq_left.mp h1
  have h3 : u.1 = (D.L.one t').1 := congrArg Subtype.val h2
  rw [← h3, hu, pushG_coe]

end Lift

end GoodReductionJacobian.BareDeformation
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian.BareDeformation"
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian"

namespace E160LV

theorem nsmulPt_eq_nsmul {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem one_coe {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id _)
  have h1 := congrArg Subtype.val h
  rw [schemeHomOverComp_coe] at h1
  exact h1.symm

theorem comp_schemeNsmul_eq_of_torsion {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f)
    (hP : L.nsmul t n P = L.one t) :
    P.1 ≫ L.schemeNsmul n = (P.1 ≫ f) ≫ (L.one (𝟙 _)).1 := by
  rw [← RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul, hP, one_coe, P.2]

theorem torsion_of_comp_schemeNsmul_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f)
    (h : P.1 ≫ L.schemeNsmul n = (P.1 ≫ f) ≫ (L.one (𝟙 _)).1) :
    L.nsmul t n P = L.one t := by
  apply Subtype.ext
  rw [RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul, h, P.2, ← one_coe]

theorem isClosedImmersion_oneSection {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) [IsSeparated f] :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h1 : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
    rw [(L.one (𝟙 (Spec (CommRingCat.of R)))).2]; infer_instance
  exact IsClosedImmersion.of_comp (L.one (𝟙 (Spec (CommRingCat.of R)))).1 f

theorem kerFst_comp_f {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = L.schemeKerStr n := by
  calc pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f
      = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
          (L.schemeNsmul n ≫ f) := by rw [RelativeGroupLaw.schemeNsmul_over]
    _ = (pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
          (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by
        rw [← Category.assoc, pullback.condition]
    _ = L.schemeKerStr n := by
        rw [Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]

end E160LV
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian.BareDeformation"

namespace E160LV

section Level

variable {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ} {B₀ : Type} [CommRing B₀]
  (E₀ : FakeEllipticCurve Λ N B₀)

theorem lev_comp_schemeNsmul :
    E₀.lev ≫ E₀.L.schemeNsmul N = (E₀.lev ≫ E₀.f) ≫ (E₀.L.one (𝟙 _)).1 := by
  have ht : FactorsThrough E₀.lev (⟨E₀.lev, rfl⟩ : SchemeHomOver (E₀.lev ≫ E₀.f) E₀.f) :=
    ⟨𝟙 _, Category.id_comp _⟩
  have h := E₀.lev_torsion (E₀.lev ≫ E₀.f) ⟨E₀.lev, rfl⟩ ht
  rw [nsmulPt_eq_nsmul] at h
  exact comp_schemeNsmul_eq_of_torsion E₀.L _ N _ h

noncomputable def levKer : E₀.C ⟶ E₀.L.schemeKer N :=
  pullback.lift E₀.lev (E₀.lev ≫ E₀.f) (lev_comp_schemeNsmul E₀)

@[scoped simp] theorem levKer_fst :
    levKer E₀ ≫ pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 _)).1 = E₀.lev :=
  pullback.lift_fst _ _ _

@[scoped simp] theorem levKer_snd : levKer E₀ ≫ E₀.L.schemeKerStr N = E₀.lev ≫ E₀.f :=
  pullback.lift_snd _ _ _

theorem isClosedImmersion_kerFst₀ :
    IsClosedImmersion (pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1) := by
  haveI : IsProper E₀.f := E₀.bundle.proper
  haveI := isClosedImmersion_oneSection E₀.L
  infer_instance

theorem isClosedImmersion_levKer : IsClosedImmersion (levKer E₀) := by
  haveI := isClosedImmersion_kerFst₀ E₀
  haveI : IsClosedImmersion (levKer E₀ ≫
      pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1) := by
    rw [levKer_fst]; exact E₀.lev_closed
  exact IsClosedImmersion.of_comp (levKer E₀)
    (pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1)

theorem range_levKer :
    Set.range (levKer E₀).base =
      (pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 (Spec (CommRingCat.of B₀)))).1).base ⁻¹'
        Set.range E₀.lev.base := by
  haveI := isClosedImmersion_kerFst₀ E₀
  ext x
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨c, ?_⟩
    change E₀.lev.base c = (levKer E₀ ≫ pullback.fst _ _).base c
    rw [levKer_fst]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    apply (pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 _)).1).isClosedEmbedding.injective
    change (levKer E₀ ≫ pullback.fst _ _).base c = _
    rw [levKer_fst]; exact hc

theorem flat_levKer_comp : Flat (levKer E₀ ≫ E₀.L.schemeKerStr N) := by
  rw [levKer_snd]; exact E₀.lev_flat

theorem lfp_levKer_comp : LocallyOfFinitePresentation (levKer E₀ ≫ E₀.L.schemeKerStr N) := by
  rw [levKer_snd]; exact E₀.lev_finitePresentation

theorem finite_levKer_comp : IsFinite (levKer E₀ ≫ E₀.L.schemeKerStr N) := by
  rw [levKer_snd]; exact E₀.lev_finite

end Level
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian.BareDeformation"

end E160LV
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.GoodReductionJacobian.BareDeformation P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique.E160LV"

theorem solution
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (B B₀ : Type) [CommRing B] [IsLocalRing B] [IsArtinianRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    (hN : IsUnit ((N : ℕ) : B))
    (E₀ : FakeEllipticCurve Λ N B₀) (D : BareDeformation E₀.f E₀.L B) [SmoothOfRelativeDimension 2 D.f]
    (W : (D.L.schemeKer N).Opens)
    (hW : (W : Set ↥(D.L.schemeKer N)) = ((pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹' (D.g.base '' Set.range E₀.lev.base))) :
      (∀ (C' : Scheme.{0}) (lev' : C' ⟶ D.A), IsClosedImmersion lev' →
        (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
          FactorsThrough lev' P → nsmulPt D.L t N P = D.L.one t) →
        IsFinite (lev' ≫ D.f) → Flat (lev' ≫ D.f) → LocallyOfFinitePresentation (lev' ≫ D.f) →
        (∀ s : ↥(Spec (CommRingCat.of B)), (lev' ≫ D.f).finrank s = N ^ 2) →
        (∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of B₀)) (P : SchemeHomOver t' E₀.f),
          FactorsThrough E₀.lev P → ∃ P₀ : T ⟶ C', P₀ ≫ lev' = P.1 ≫ D.g) →
        ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P : SchemeHomOver t D.f),
          FactorsThrough (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1) P ↔ FactorsThrough lev' P) := by
  intro C' lev' hcl' hT' hfin' hflat' hlfp' hrank' hlev' T t P

  obtain ⟨hKfin, hKflat, hKet, hκ⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.isFinite_flat_etale_schemeKerStr_of_isUnit
      (R := B) D.L D.bundle D.comm 2 N hN
  obtain ⟨gK, hgK, hpb⟩ := GoodReductionJacobian.BareDeformation.exists_schemeKer_comparison D N
  obtain ⟨_, _, hgKhomeo⟩ :=
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
      (algebraMap B B₀) hπ hker (D.L.schemeKerStr N) (E₀.L.schemeKerStr N) gK hpb
  obtain ⟨_, hgsurj, hghomeo⟩ :=
    AlgebraicGeometry.isHomeomorph_of_isPullback_of_surjective_of_isNilpotent_ker
      (algebraMap B B₀) hπ hker D.f E₀.f D.g D.cart
  haveI := hKfin; haveI := hKflat; haveI := hKet; haveI := hκ
  haveI := E160LV.isClosedImmersion_kerFst₀ E₀
  haveI := E160LV.isClosedImmersion_levKer E₀
  haveI := hcl'; haveI := hfin'; haveI := hflat'; haveI := hlfp'

  have hS : (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base ⁻¹'
      (D.g.base '' Set.range E₀.lev.base) = gK.base '' Set.range (E160LV.levKer E₀).base := by
    ext x
    obtain ⟨x₀, rfl⟩ := gK.surjective x
    have hx : (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 (Spec (CommRingCat.of B)))).1).base
        (gK.base x₀) = D.g.base ((pullback.fst (E₀.L.schemeNsmul N) (E₀.L.one (𝟙 _)).1).base x₀) := by
      change (gK ≫ pullback.fst _ _).base x₀ = (pullback.fst _ _ ≫ D.g).base x₀
      rw [hgK]
    simp only [Set.mem_preimage, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, hc⟩
      rw [hx] at hc
      have hc' := hghomeo.injective hc
      have : x₀ ∈ Set.range (E160LV.levKer E₀).base := by
        rw [E160LV.range_levKer]; exact ⟨c, hc'⟩
      obtain ⟨c', hc''⟩ := this
      exact ⟨x₀, ⟨c', hc''⟩, rfl⟩
    · rintro ⟨y₀, ⟨c, rfl⟩, hy⟩
      have hy' := hgKhomeo.injective hy
      subst hy'
      refine ⟨E₀.lev.base c, ⟨c, rfl⟩, ?_⟩
      rw [hx]
      congr 1
      change _ = ((E160LV.levKer E₀) ≫ pullback.fst _ _).base c
      rw [E160LV.levKer_fst]
  have hWclosed : IsClosed (W : Set ↥(D.L.schemeKer N)) := by
    rw [hW, hS]
    exact gK.isClosedEmbedding.isClosedMap _ (E160LV.levKer E₀).isClosedEmbedding.isClosed_range

  have w' : lev' ≫ D.L.schemeNsmul N = (lev' ≫ D.f) ≫ (D.L.one (𝟙 _)).1 := by
    have ht : FactorsThrough lev' (⟨lev', rfl⟩ : SchemeHomOver (lev' ≫ D.f) D.f) :=
      ⟨𝟙 _, Category.id_comp _⟩
    have h := hT' (lev' ≫ D.f) ⟨lev', rfl⟩ ht
    rw [E160LV.nsmulPt_eq_nsmul] at h
    exact E160LV.comp_schemeNsmul_eq_of_torsion D.L _ N _ h
  let j' : C' ⟶ D.L.schemeKer N := pullback.lift lev' (lev' ≫ D.f) w'
  have hj'fst : j' ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 _)).1 = lev' :=
    pullback.lift_fst _ _ _
  have hj'snd : j' ≫ D.L.schemeKerStr N = lev' ≫ D.f := pullback.lift_snd _ _ _
  haveI : IsClosedImmersion j' := by
    haveI : IsClosedImmersion (j' ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 _)).1) := by
      rw [hj'fst]; exact hcl'
    exact IsClosedImmersion.of_comp j' (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 _)).1)
  haveI : Flat (j' ≫ D.L.schemeKerStr N) := by rw [hj'snd]; exact hflat'
  haveI : LocallyOfFinitePresentation (j' ≫ D.L.schemeKerStr N) := by rw [hj'snd]; exact hlfp'
  obtain ⟨hj'open, _⟩ := AlgebraicGeometry.IsOpenImmersion.of_isClosedImmersion_of_flat_comp_of_etale
    j' (D.L.schemeKerStr N)
  haveI := hj'open

  have hWle : (W : Set ↥(D.L.schemeKer N)) ⊆ Set.range j'.base := by
    intro x hx
    rw [hW] at hx
    obtain ⟨_, ⟨c, rfl⟩, hc⟩ := hx
    obtain ⟨Q, hQ⟩ := hlev' (E₀.lev ≫ E₀.f) ⟨E₀.lev, rfl⟩ ⟨𝟙 _, Category.id_comp _⟩
    refine ⟨Q.base c, ?_⟩
    apply (pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 _)).1).isClosedEmbedding.injective
    change (j' ≫ pullback.fst _ _).base (Q.base c) = _
    rw [hj'fst, ← hc]
    change (Q ≫ lev').base c = (E₀.lev ≫ D.g).base c
    rw [hQ]

  have hrange : Set.range j'.base = (W : Set ↥(D.L.schemeKer N)) := by
    refine le_antisymm ?_ hWle

    let Wc : (D.L.schemeKer N).Opens := ⟨(W : Set _)ᶜ, hWclosed.isOpen_compl⟩
    let U : C'.Opens := j' ⁻¹ᵁ W
    let V : C'.Opens := j' ⁻¹ᵁ Wc
    have hUV : U ⊔ V = ⊤ := by
      ext x; constructor
      · intro _; trivial
      · intro _
        by_cases h : j'.base x ∈ (W : Set _)
        · exact Or.inl h
        · exact Or.inr h
    have hdisj : U ⊓ V = ⊥ := by
      ext x; constructor
      · rintro ⟨h1, h2⟩; exact h2 h1
      · intro h; exact h.elim
    have hadd := AlgebraicGeometry.Scheme.Hom.finrank_restrict_add_finrank_restrict_of_isCompl
      (lev' ≫ D.f) U V hUV hdisj

    have hUrange : Set.range (U.ι ≫ j').base = Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι]
      ext y; constructor
      · rintro ⟨u, rfl⟩
        exact u.2
      · intro hy
        obtain ⟨c', hc'⟩ := hWle hy
        exact ⟨⟨c', show j'.base c' ∈ (W : Set _) from hc'.symm ▸ hy⟩, hc'⟩
    let eU := IsOpenImmersion.isoOfRangeEq (U.ι ≫ j') W.ι hUrange
    have heU : eU.hom ≫ W.ι = U.ι ≫ j' := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hUrange
    obtain ⟨_, hWfin, hWflat, _, hWrank⟩ :=
      GoodReductionJacobian.BareDeformation.levelPiece_isClosedImmersion_finite_flat_finrank
        B B₀ hπ hker hN E₀ D W hW
    have hUeq : U.ι ≫ (lev' ≫ D.f) =
        eU.hom ≫ ((W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 _)).1) ≫ D.f) := by
      rw [← hj'fst, ← Category.assoc, ← Category.assoc, ← heU, Category.assoc, Category.assoc,
        Category.assoc]
    haveI := hWfin; haveI := hWflat
    have hUrank : ∀ s, (U.ι ≫ (lev' ≫ D.f)).finrank s = N ^ 2 := by
      intro s; rw [hUeq, Scheme.Hom.finrank_comp_left_of_isIso]; exact hWrank s

    have hV0 : ∀ s, (V.ι ≫ (lev' ≫ D.f)).finrank s = 0 := by
      intro s; have := hadd s; rw [hUrank s, hrank' s] at this; omega

    have hVclosed : IsClosed (V : Set ↥C') := by
      have : (V : Set ↥C') = (U : Set ↥C')ᶜ := rfl
      rw [this, isClosed_compl_iff]; exact U.isOpen
    haveI : IsClosedImmersion V.ι :=
      IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hVclosed)
    have hVempty : ∀ v : ↥V, False := by
      intro v
      have h1 := Scheme.Hom.one_le_finrank_map (V.ι ≫ (lev' ≫ D.f)) v
      rw [hV0] at h1
      exact Nat.not_succ_le_zero 0 h1
    rintro _ ⟨c', rfl⟩
    by_contra hc
    exact hVempty ⟨c', hc⟩

  let e' := IsOpenImmersion.isoOfRangeEq j' W.ι (by rw [Scheme.Opens.range_ι]; exact hrange)
  have he' : e'.hom ≫ W.ι = j' := IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
  have hlevlev : lev' = e'.hom ≫ (W.ι ≫ pullback.fst (D.L.schemeNsmul N) (D.L.one (𝟙 _)).1) := by
    rw [← Category.assoc, he', hj'fst]
  constructor
  · rintro ⟨Q₀, hQ₀⟩
    exact ⟨Q₀ ≫ e'.inv, by rw [hlevlev, Category.assoc, e'.inv_hom_id_assoc, hQ₀]⟩
  · rintro ⟨P₀, hP₀⟩
    exact ⟨P₀ ≫ e'.hom, by rw [Category.assoc, ← hlevlev, hP₀]⟩

end S_GoodReductionJacobian_BareDeformation_levelPiece_unique
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_levelPiece_unique (solution)
