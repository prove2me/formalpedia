-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6b91e06b-62ae-5c45-9b2b-4b5a3911efd1

import Mathlib
import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Definitions.Def_AlgebraicGeometry_ModulesPullbackLocalSection
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
import Theorems.Thm_CerednikDrinfeld_QM_isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe"

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra~schemeHomOverComp~schemeHomOverComp_coe GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.GoodReductionJacobian"

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "AbelianSchemePropertyBundle schemeHomOverComp schemeHomOverComp_coe RelativeGroupLaw RelativeGroupLaw.nsmul_succ RelativeGroupLaw.idPoint"
namespace LevelL3
p2m_open "GoodReductionJacobian"

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

def compHom {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    letI := L.pointGroup t; letI := L.pointGroup t'; SchemeHomOver t f →* SchemeHomOver t' f :=
  letI := L.pointGroup t; letI := L.pointGroup t'
  { toFun := schemeHomOverComp ψ hψ
    map_one' := L.one_natural t t' ψ hψ
    map_mul' := fun x y => L.mul_natural t t' ψ hψ x y }

theorem finComb_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (t' : T' ⟶ Spec (CommRingCat.of S))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') {m : ℕ} (x : Fin m → SchemeHomOver t f) (c : Fin m → ℕ) :
    schemeHomOverComp ψ hψ (L.finComb t x c) = L.finComb t' (fun i => schemeHomOverComp ψ hψ (x i)) c := by
  letI := L.pointGroup t; letI := L.pointGroup t'
  show compHom L t t' ψ hψ (List.ofFn fun i => x i ^ c i).prod =
    (List.ofFn fun i => schemeHomOverComp ψ hψ (x i) ^ c i).prod
  rw [map_list_prod, List.map_ofFn]
  congr 1
  refine congrArg List.ofFn (funext fun i => ?_)
  show compHom L t t' ψ hψ (x i ^ c i) = _
  rw [map_pow]
  rfl

theorem nsmul_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = (letI := L.pointGroup t; x ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]; rfl

theorem nsmul_finComb_eq_one (hc : L.IsCommutative) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ)
    {m : ℕ} (x : Fin m → SchemeHomOver t f) (hx : ∀ i, L.nsmul t n (x i) = L.one t) (c : Fin m → ℕ) :
    L.nsmul t n (L.finComb t x c) = L.one t := by
  letI : CommGroup (SchemeHomOver t f) := { L.pointGroup t with mul_comm := fun a b => hc t a b }
  rw [nsmul_eq_pow]
  show (List.ofFn fun i => x i ^ c i).prod ^ n = 1
  have hmem : (List.ofFn fun i => x i ^ c i).prod ∈ MonoidHom.mker (powMonoidHom n : SchemeHomOver t f →* _) := by
    apply Submonoid.list_prod_mem
    rw [List.forall_mem_ofFn_iff]
    intro i
    rw [MonoidHom.mem_mker, powMonoidHom_apply, ← pow_mul, mul_comm, pow_mul]
    have : x i ^ n = 1 := by rw [← nsmul_eq_pow]; exact hx i
    rw [this, one_pow]
  rwa [MonoidHom.mem_mker, powMonoidHom_apply] at hmem

theorem comp_schemeNsmul {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (n : ℕ) (x : SchemeHomOver t f) :
    x.1 ≫ L.schemeNsmul n = (L.nsmul t n x).1 := by
  have h := L.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

def torsLift (n : ℕ) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hQ : L.nsmul (𝟙 _) n Q = L.one (𝟙 _)) : Spec (CommRingCat.of S) ⟶ L.schemeKer n :=
  pullback.lift Q.1 (𝟙 _) (by rw [comp_schemeNsmul, hQ, Category.id_comp])

@[scoped simp] theorem torsLift_fst (n : ℕ) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hQ : L.nsmul (𝟙 _) n Q = L.one (𝟙 _)) :
    torsLift L n Q hQ ≫ pullback.fst _ _ = Q.1 := pullback.lift_fst _ _ _

@[scoped simp] theorem torsLift_snd (n : ℕ) (Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hQ : L.nsmul (𝟙 _) n Q = L.one (𝟙 _)) :
    torsLift L n Q hQ ≫ L.schemeKerStr n = 𝟙 _ := pullback.lift_snd _ _ _

theorem comp_torsLift_eq_iff (n : ℕ) (Q Q' : SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hQ : L.nsmul (𝟙 _) n Q = L.one (𝟙 _)) (hQ' : L.nsmul (𝟙 _) n Q' = L.one (𝟙 _))
    {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of S)) :
    g ≫ torsLift L n Q hQ = g ≫ torsLift L n Q' hQ' ↔ g ≫ Q.1 = g ≫ Q'.1 := by
  constructor
  · intro h
    rw [← torsLift_fst L n Q hQ, ← torsLift_fst L n Q' hQ', ← Category.assoc, h, Category.assoc]
  · intro h
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, torsLift_fst, torsLift_fst, h]
    · rw [Category.assoc, Category.assoc]
      show g ≫ torsLift L n Q hQ ≫ L.schemeKerStr n = g ≫ torsLift L n Q' hQ' ≫ L.schemeKerStr n
      rw [torsLift_snd, torsLift_snd]

theorem nsmulPt_one {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) :
    ∀ m : ℕ, CerednikDrinfeld.QM.nsmulPt L t m (L.one t) = L.one t
  | 0 => rfl
  | m + 1 => by
    show L.mul t (CerednikDrinfeld.QM.nsmulPt L t m (L.one t)) (L.one t) = L.one t
    rw [nsmulPt_one t m, L.mul_one]

theorem isFinite_etale_schemeKerStr (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (n : ℕ) (hn : IsUnit ((n : ℕ) : S)) : IsFinite (L.schemeKerStr n) ∧ Etale (L.schemeKerStr n) := by
  haveI : IsProper f := hA.proper
  haveI hEci : IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of S)))).1 := by
    haveI : IsIso ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) := by
      rw [(L.one (𝟙 (Spec (CommRingCat.of S)))).2]; infer_instance
    have hfac : (L.one (𝟙 (Spec (CommRingCat.of S)))).1 =
        pullback.lift (𝟙 _) (L.one (𝟙 (Spec (CommRingCat.of S)))).1
          (Category.id_comp ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f)) ≫
        pullback.snd ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) f :=
      (pullback.lift_snd _ _ _).symm
    rw [hfac]; infer_instance
  have htors : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (P : SchemeHomOver t f),
      CerednikDrinfeld.QM.FactorsThrough (L.one (𝟙 (Spec (CommRingCat.of S)))).1 P →
        CerednikDrinfeld.QM.nsmulPt L t n P = L.one t := by
    intro T t P ⟨P₀, hP₀⟩
    have ht : P₀ = t := by
      have := P.2
      rw [← hP₀, Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of S)))).2, Category.comp_id] at this
      exact this
    have hP : P = L.one t := by
      rw [← L.one_natural (𝟙 _) t t (Category.comp_id _)]
      apply Subtype.ext
      rw [schemeHomOverComp_coe, ← hP₀, ht]
    rw [hP]
    exact nsmulPt_one L t n
  have hover : (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f = 𝟙 _ := (L.one (𝟙 (Spec (CommRingCat.of S)))).2
  have hflat : Flat ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) := by rw [hover]; infer_instance
  have hfp : LocallyOfFinitePresentation ((L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f) := by
    rw [hover]; infer_instance
  obtain ⟨h1, h2, -, -⟩ :=
    CerednikDrinfeld.QM.isFinite_etale_schemeKerStr_and_etale_isOpenImmersion_of_forall_nsmulPt_eq_one_of_isUnit
      L hc hA (L.one (𝟙 (Spec (CommRingCat.of S)))).1 hEci n htors hflat hfp hn
  exact ⟨h1, h2⟩

theorem range_specMap_eq_singleton {k : Type} [Field k] (sk : S →+* k) (s : Spec (CommRingCat.of S))
    (hk : RingHom.ker sk = s.asIdeal) : Set.range (Spec.map (CommRingCat.ofHom sk)).base = {s} := by
  have hpt : ∀ x : Spec (CommRingCat.of k), (Spec.map (CommRingCat.ofHom sk)).base x = s := by
    intro x
    apply PrimeSpectrum.ext
    have hx : x.asIdeal = ⊥ := by
      haveI : Subsingleton (PrimeSpectrum k) := inferInstance
      have : x = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
      rw [this]; rfl
    show Ideal.comap sk x.asIdeal = s.asIdeal
    rw [hx, ← RingHom.ker_eq_comap_bot, hk]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩; exact hpt x
  · intro y hy
    rw [Set.mem_singleton_iff] at hy
    obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨(default : PrimeSpectrum k)⟩
    exact ⟨x, hy ▸ hpt x⟩

theorem exists_geomPoint (s : Spec (CommRingCat.of S)) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (sk : S →+* k), RingHom.ker sk = s.asIdeal := by
  let D := S ⧸ s.asIdeal
  let K := FractionRing D
  refine ⟨AlgebraicClosure K, inferInstance, inferInstance,
    (algebraMap K (AlgebraicClosure K)).comp ((algebraMap D K).comp (Ideal.Quotient.mk s.asIdeal)), ?_⟩
  rw [RingHom.ker_eq_comap_bot, ← Ideal.comap_comap, ← Ideal.comap_comap,
    Ideal.comap_bot_of_injective _ (algebraMap K (AlgebraicClosure K)).injective,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective D K), ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

theorem kerFst_comp (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f = L.schemeKerStr n := by
  have h : pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ L.schemeNsmul n ≫ f =
      pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1 ≫ f := by rw [L.schemeNsmul_over]
  rw [← h, ← Category.assoc, pullback.condition, Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of S)))).2,
    Category.comp_id]

def kerPt (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (γ : T ⟶ L.schemeKer n)
    (hγ : γ ≫ L.schemeKerStr n = t) : SchemeHomOver t f :=
  ⟨γ ≫ pullback.fst _ _, by rw [Category.assoc, kerFst_comp, hγ]⟩

theorem kerPt_torsion (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (γ : T ⟶ L.schemeKer n)
    (hγ : γ ≫ L.schemeKerStr n = t) : L.nsmul t n (kerPt L n t γ hγ) = L.one t := by
  apply Subtype.ext
  rw [← comp_schemeNsmul]
  show (γ ≫ pullback.fst _ _) ≫ L.schemeNsmul n = (L.one t).1
  rw [Category.assoc, pullback.condition, ← Category.assoc, hγ,
    ← L.one_natural (𝟙 _) t t (Category.comp_id _), schemeHomOverComp_coe]

def liftPt (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t f)
    (hQ : L.nsmul t n Q = L.one t) : T ⟶ L.schemeKer n :=
  pullback.lift Q.1 t (by
    rw [comp_schemeNsmul, hQ, ← L.one_natural (𝟙 _) t t (Category.comp_id _), schemeHomOverComp_coe])

@[scoped simp] theorem liftPt_fst (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t f)
    (hQ : L.nsmul t n Q = L.one t) : liftPt L n t Q hQ ≫ pullback.fst _ _ = Q.1 := pullback.lift_fst _ _ _

@[scoped simp] theorem liftPt_snd (n : ℕ) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (Q : SchemeHomOver t f)
    (hQ : L.nsmul t n Q = L.one t) : liftPt L n t Q hQ ≫ L.schemeKerStr n = t := pullback.lift_snd _ _ _

theorem exists_geomPoint_through {X : Scheme.{0}} (z : X) :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (γ : Spec (CommRingCat.of k) ⟶ X), ∀ x, γ.base x = z := by
  let K0 : Type := X.residueField z
  refine ⟨AlgebraicClosure K0, inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap K0 (AlgebraicClosure K0))) ≫ X.fromSpecResidueField z, fun x => ?_⟩
  have hr := Scheme.range_fromSpecResidueField (X := X) z
  have hx : (Spec.map (CommRingCat.ofHom (algebraMap K0 (AlgebraicClosure K0))) ≫ X.fromSpecResidueField z).base x
      ∈ Set.range (X.fromSpecResidueField z).base := by
    rw [Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  rwa [hr, Set.mem_singleton_iff] at hx

theorem main (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
    (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hP : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))) :
    IsClopen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      RingHom.ker sk = s.asIdeal →
      ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * g) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q} := by
  classical

  obtain ⟨hfin, het⟩ := isFinite_etale_schemeKerStr L hc hA n hn
  haveI := hfin
  haveI := het
  haveI : IsSeparated (L.schemeKerStr n) := IsSeparated.of_isAffineHom _
  obtain ⟨hflat, -, hlfp⟩ := Etale.iff_flat_and_formallyUnramified.mp het
  haveI := hflat
  haveI := hlfp

  let σ : (Fin (2 * g) → Fin n) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f :=
    fun c => L.finComb (𝟙 _) P (fun i => (c i : ℕ))
  have hσ : ∀ c, L.nsmul (𝟙 _) n (σ c) = L.one (𝟙 _) := fun c =>
    nsmul_finComb_eq_one L hc (𝟙 _) n P hP _
  let τ : (Fin (2 * g) → Fin n) → (Spec (CommRingCat.of S) ⟶ L.schemeKer n) :=
    fun c => torsLift L n (σ c) (hσ c)
  have hτ : ∀ c, τ c ≫ L.schemeKerStr n = 𝟙 _ := fun c => torsLift_snd L n (σ c) (hσ c)
  have hτfst : ∀ c, τ c ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of S)))).1 = (σ c).1 :=
    fun c => torsLift_fst L n (σ c) (hσ c)

  let p' := pullback.fst (L.schemeKerStr n) (L.schemeKerStr n)
  haveI : FormallyUnramified p' := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : LocallyOfFiniteType p' := MorphismProperty.pullback_fst _ _ inferInstance
  haveI : IsSeparated p' := MorphismProperty.pullback_fst _ _ inferInstance
  let δ : L.schemeKer n ⟶ pullback (L.schemeKerStr n) (L.schemeKerStr n) :=
    pullback.lift (𝟙 _) (𝟙 _) rfl
  have hδ : δ ≫ p' = 𝟙 _ := pullback.lift_fst _ _ _
  let ρ : (Fin (2 * g) → Fin n) → (L.schemeKer n ⟶ pullback (L.schemeKerStr n) (L.schemeKerStr n)) :=
    fun c => pullback.lift (𝟙 _) (L.schemeKerStr n ≫ τ c)
      (by rw [Category.id_comp, Category.assoc, hτ c, Category.comp_id])
  have hρ : ∀ c, ρ c ≫ p' = 𝟙 _ := fun c => pullback.lift_fst _ _ _
  have key := fun c =>
    AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated p' δ (ρ c) hδ (hρ c)
  let V : (Fin (2 * g) → Fin n) → Set ↥(L.schemeKer n) :=
    fun c => ((pullback.lift δ (ρ c) (hδ.trans (hρ c).symm) ⁻¹ᵁ
      (pullback.diagonal p').opensRange : (L.schemeKer n).Opens) : Set _)
  have hV : ∀ c, IsClopen (V c) := fun c => (key c).1

  have hdictV : ∀ c {T : Scheme.{0}} (γ : T ⟶ L.schemeKer n),
      Set.range γ.base ⊆ V c ↔ γ = γ ≫ L.schemeKerStr n ≫ τ c := by
    intro c T γ
    rw [(key c).2 γ]
    constructor
    · intro h
      have h2 := congrArg (fun x => x ≫ pullback.snd (L.schemeKerStr n) (L.schemeKerStr n)) h
      simp only [δ, ρ, Category.assoc, pullback.lift_snd, Category.comp_id] at h2
      exact h2
    · intro h
      apply pullback.hom_ext
      · simp only [δ, ρ, Category.assoc, pullback.lift_fst]
      · simp only [δ, ρ, Category.assoc, pullback.lift_snd, Category.comp_id]
        exact h

  let Z : Set ↥(L.schemeKer n) := ⋃ c, V c
  have hZ : IsClopen Z := isClopen_iUnion_of_finite hV
  have himg : IsClopen ((L.schemeKerStr n).base '' Zᶜ) :=
    ⟨(L.schemeKerStr n).isClosedMap _ hZ.compl.1, (L.schemeKerStr n).isOpenMap _ hZ.compl.2⟩

  have hset : {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      RingHom.ker sk = s.asIdeal →
      ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * g) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q}
      = ((L.schemeKerStr n).base '' Zᶜ)ᶜ := by
    ext s
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    ·
      intro h z hzZ hzs
      apply hzZ

      obtain ⟨k, _, _, γ, hγz⟩ := exists_geomPoint_through z
      obtain ⟨sk, hsk⟩ : ∃ sk : S →+* k, Spec.map (CommRingCat.ofHom sk) = γ ≫ L.schemeKerStr n :=
        ⟨(Spec.preimage (γ ≫ L.schemeKerStr n)).hom, by simp only [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
      obtain ⟨x0⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨(default : PrimeSpectrum k)⟩
      have hker : RingHom.ker sk = s.asIdeal := by
        have h1 : (Spec.map (CommRingCat.ofHom sk)).base x0 = s := by
          rw [hsk, Scheme.Hom.comp_apply, hγz, hzs]
        have hx0 : x0.asIdeal = ⊥ := by
          have : x0 = (⊥ : PrimeSpectrum k) := Subsingleton.elim _ _
          rw [this]; rfl
        rw [RingHom.ker_eq_comap_bot, ← hx0]
        exact congrArg PrimeSpectrum.asIdeal h1

      obtain ⟨c, hc'⟩ := h k sk hker (kerPt L n _ γ hsk.symm) (kerPt_torsion L n _ γ hsk.symm)
      have hγeq : γ = γ ≫ L.schemeKerStr n ≫ τ c := by
        have h3 := congrArg Subtype.val hc'
        rw [← finComb_natural, schemeHomOverComp_coe] at h3
        change Spec.map (CommRingCat.ofHom sk) ≫ (σ c).1 = γ ≫ pullback.fst _ _ at h3
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, hτfst c, ← Category.assoc, ← hsk]
          exact h3.symm
        · show γ ≫ L.schemeKerStr n = (γ ≫ L.schemeKerStr n ≫ τ c) ≫ L.schemeKerStr n
          rw [Category.assoc, Category.assoc, hτ c, Category.comp_id]
      have hrange : Set.range γ.base ⊆ V c := (hdictV c γ).mpr hγeq
      exact Set.mem_iUnion.mpr ⟨c, hrange ⟨x0, hγz x0⟩⟩
    ·
      intro h k _ _ sk hk Q hQ
      let γ := liftPt L n (Spec.map (CommRingCat.ofHom sk)) Q hQ
      obtain ⟨x0⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨(default : PrimeSpectrum k)⟩
      have hsub : Subsingleton ↥(Spec (CommRingCat.of k)) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
      have hzs : (L.schemeKerStr n).base (γ.base x0) = s := by
        rw [← Scheme.Hom.comp_apply]
        have : (γ ≫ L.schemeKerStr n).base x0 ∈ Set.range (Spec.map (CommRingCat.ofHom sk)).base := by
          rw [show γ ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom sk) from liftPt_snd L n _ Q hQ]
          exact Set.mem_range_self _
        rwa [range_specMap_eq_singleton sk s hk, Set.mem_singleton_iff] at this
      have hzZ : γ.base x0 ∈ Z := by
        by_contra hzZ
        exact h (γ.base x0) hzZ hzs
      obtain ⟨c, hzc⟩ := Set.mem_iUnion.mp hzZ
      have hrange : Set.range γ.base ⊆ V c := by
        rintro _ ⟨x, rfl⟩
        rwa [@Subsingleton.elim _ hsub x x0]
      have hγeq := (hdictV c γ).mp hrange
      refine ⟨c, ?_⟩
      rw [← finComb_natural]
      apply Subtype.ext
      rw [schemeHomOverComp_coe]
      change Spec.map (CommRingCat.ofHom sk) ≫ (σ c).1 = Q.1
      rw [← liftPt_fst L n _ Q hQ, ← torsLift_fst L n (σ c) (hσ c)]
      change Spec.map (CommRingCat.ofHom sk) ≫ τ c ≫ pullback.fst _ _ = γ ≫ pullback.fst _ _
      rw [hγeq, Category.assoc, Category.assoc, ← Category.assoc (liftPt L n _ Q hQ)]
      show _ = (liftPt L n _ Q hQ ≫ L.schemeKerStr n) ≫ τ c ≫ pullback.fst _ _
      rw [liftPt_snd]
  rw [hset]
  exact himg.compl

end GoodReductionJacobian.LevelL3
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.GoodReductionJacobian.LevelL3"
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.GoodReductionJacobian"

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit.GoodReductionJacobian.LevelL3"

theorem solution
    {S : Type} [CommRing S] {A : Scheme} {f : A ⟶ Spec (CommRingCat.of S)}
    (L : RelativeGroupLaw S f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle S f)
    (g : ℕ) (n : ℕ) (hn : IsUnit ((n : ℕ) : S))
    (P : Fin (2 * g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of S))) f)
    (hP : ∀ i, L.nsmul (𝟙 (Spec (CommRingCat.of S))) n (P i) = L.one (𝟙 (Spec (CommRingCat.of S)))) :
    IsClopen {s : ↥(Spec (CommRingCat.of S)) | ∀ (k : Type) [Field k] [IsAlgClosed k] (sk : S →+* k),
      RingHom.ker sk = s.asIdeal →
      ∀ Q : SchemeHomOver (Spec.map (CommRingCat.ofHom sk)) f,
        L.nsmul (Spec.map (CommRingCat.ofHom sk)) n Q = L.one (Spec.map (CommRingCat.ofHom sk)) →
        ∃ c : Fin (2 * g) → Fin n,
          L.finComb (Spec.map (CommRingCat.ofHom sk))
            (fun i => schemeHomOverComp (Spec.map (CommRingCat.ofHom sk)) (Category.comp_id _) (P i)) (fun i => (c i : ℕ)) = Q} :=
  GoodReductionJacobian.LevelL3.main L hc hA g n hn P hP

end S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_isClopen_setOf_forall_torsion_exists_finComb_eq_of_isUnit (solution)
