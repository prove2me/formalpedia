-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/ccfd8197-c2b3-50cc-8281-6c7c9b476f64

import Mathlib
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension
import Theorems.Thm_AlgebraicGeometry_FormallyUnramified_eq_of_comp_eq_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace TorsHenselTools

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)

theorem pow_eq_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) (n : ℕ) :
    (letI := G.pointGroup t; x ^ n) = G.nsmul t n x := by
  letI := G.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, RelativeGroupLaw.nsmul_succ, ← ih]
      rfl

theorem coe_nsmul_eq_comp_schemeNsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id x.1)
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  rw [hx] at h
  rw [← h]
  rfl

def castBase {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x : SchemeHomOver t f) :
    SchemeHomOver t' f :=
  ⟨x.1, x.2.trans h⟩

@[scoped simp] theorem castBase_coe {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (x : SchemeHomOver t f) :
    (castBase h x).1 = x.1 := rfl

theorem nsmul_castBase {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') (n : ℕ) (x : SchemeHomOver t f) :
    G.nsmul t' n (castBase h x) = castBase h (G.nsmul t n x) := by
  subst h; rfl

theorem one_castBase {T : Scheme.{u}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    castBase h (G.one t) = G.one t' := by
  subst h; rfl

variable {R' : Type u} [CommRing R'] (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))

theorem baseChangePointToBase_nsmul {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (y : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).nsmul t' n y) =
      G.nsmul (t' ≫ ι) n (RelativeGroupLaw.baseChangePointToBase ι y) := by
  induction n with
  | zero => exact RelativeGroupLaw.baseChangePointToBase_one ι G t'
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.baseChangePointToBase_mul, ih]

end TorsHenselTools
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing.TorsHenselTools"

open TorsHenselTools

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} [IsSeparated f]
    (G : RelativeGroupLaw R f) (hc : G.IsCommutative) [Smooth f]
    (n : ℕ) (hn : IsUnit (n : R))
    (O : Type u) [CommRing O] [HenselianLocalRing O] (ρ : R →+* O)
    (κ : Type u) [Field κ] [IsAlgClosed κ] (π : O →+* κ) (hπ : Function.Surjective π)
    (hπu : ∀ x : O, IsUnit x ↔ π x ≠ 0) :
    letI := G.pointGroup (Spec.map (CommRingCat.ofHom ρ))
    letI := G.pointGroup (Spec.map (CommRingCat.ofHom (π.comp ρ)))
    (∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, z ^ n = 1 →
        Spec.map (CommRingCat.ofHom π) ≫ z.1 = (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom (π.comp ρ))) f).1 → z = 1) ∧
    (∀ w : SchemeHomOver (Spec.map (CommRingCat.ofHom (π.comp ρ))) f, w ^ n = 1 →
        ∃ z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f, z ^ n = 1 ∧ w.1 = Spec.map (CommRingCat.ofHom π) ≫ z.1) := by
  classical

  let ι : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of R) := Spec.map (CommRingCat.ofHom ρ)
  let f' := RelativeGroupLaw.baseChangeStr ι f
  let G' : RelativeGroupLaw O f' := G.baseChange ι
  have hc' : G'.IsCommutative := hc.baseChange ι
  haveI : Smooth f' := MorphismProperty.pullback_snd (P := @Smooth) f ι inferInstance
  obtain ⟨d, hd⟩ := GoodReductionJacobian.RelativeGroupLaw.exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing G'
  haveI := hd
  have hnO : IsUnit (n : O) := by simpa using hn.map ρ
  haveI hét : AlgebraicGeometry.Etale (G'.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.etale_schemeNsmul_of_isUnit_of_smoothOfRelativeDimension G' (fun t x y => hc' t x y) d n hnO

  have hker : RingHom.ker π = IsLocalRing.maximalIdeal O := by
    ext x
    rw [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hπu, not_not]
  have hmk : IsLocalRing.maximalIdeal O ≤ RingHom.ker π := hker.ge

  let eh : IsLocalRing.ResidueField O →+* κ := Ideal.Quotient.lift _ π (fun a ha => (RingHom.mem_ker).mp (hmk ha))
  have heh : ∀ a : O, eh (IsLocalRing.residue O a) = π a := fun a => rfl
  have hehbij : Function.Bijective eh := by
    constructor
    · rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
      intro q hq
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective q
      have hq' : π a = 0 := hq
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (hker.le ((RingHom.mem_ker).mpr hq'))
    · intro c
      obtain ⟨a, rfl⟩ := hπ c
      exact ⟨IsLocalRing.residue O a, rfl⟩
  let e : IsLocalRing.ResidueField O ≃+* κ := RingEquiv.ofBijective eh hehbij
  have he : ∀ a : O, e (IsLocalRing.residue O a) = π a := fun a => rfl
  have hπe : π = e.toRingHom.comp (IsLocalRing.residue O) := RingHom.ext fun a => (he a).symm
  have hres : algebraMap O (IsLocalRing.ResidueField O) = IsLocalRing.residue O := rfl

  have hSpecπ : Spec.map (CommRingCat.ofHom π) =
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hπe]
  have hee : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.symm.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : e.toRingHom.comp e.symm.toRingHom = RingHom.id _ := RingHom.ext fun x => e.apply_symm_apply x
    rw [this, CommRingCat.ofHom_id]; exact Spec.map_id _

  have hic : ι = 𝟙 _ ≫ ι := (Category.id_comp ι).symm
  let sec : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) f' :=
    fun y => RelativeGroupLaw.baseChangePointOfBase ι (castBase hic y)
  have hsec_fst : ∀ y, (sec y).1 ≫ pullback.fst f ι = y.1 := fun y => pullback.lift_fst _ _ _
  have hsec_snd : ∀ y, (sec y).1 ≫ pullback.snd f ι = 𝟙 _ := fun y => pullback.lift_snd _ _ _
  have hπρ : Spec.map (CommRingCat.ofHom π) ≫ Spec.map (CommRingCat.ofHom ρ) = Spec.map (CommRingCat.ofHom (π.comp ρ)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : FormallyUnramified (G'.schemeNsmul n) := inferInstance
  haveI : LocallyOfFiniteType (G'.schemeNsmul n) := inferInstance
  have hsec_nsmul : ∀ y, G'.nsmul _ n (sec y) = sec (G.nsmul _ n y) := by
    intro y
    apply (RelativeGroupLaw.baseChangePointEquiv ι (𝟙 _)).injective
    show RelativeGroupLaw.baseChangePointToBase ι (G'.nsmul _ n (sec y)) = RelativeGroupLaw.baseChangePointToBase ι (sec (G.nsmul _ n y))
    rw [baseChangePointToBase_nsmul]
    show G.nsmul (𝟙 _ ≫ ι) n (RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι (castBase hic y))) =
      RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι (castBase hic (G.nsmul _ n y)))
    rw [RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase, nsmul_castBase]
  letI grpO := G.pointGroup (Spec.map (CommRingCat.ofHom ρ))
  letI grpκ := G.pointGroup (Spec.map (CommRingCat.ofHom (π.comp ρ)))
  refine ⟨?_, ?_⟩
  ·
    intro z hz hred
    have hzn : G.nsmul _ n z = G.one _ := by rw [← pow_eq_nsmul, hz]; rfl
    have h1n : G.nsmul _ n (1 : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f) = G.one _ := by
      rw [← pow_eq_nsmul, one_pow]; rfl

    have hf : (sec z).1 ≫ G'.schemeNsmul n = (sec 1).1 ≫ G'.schemeNsmul n := by
      rw [← coe_nsmul_eq_comp_schemeNsmul, ← coe_nsmul_eq_comp_schemeNsmul, hsec_nsmul, hsec_nsmul, hzn, h1n]
    have ht : IsLocalRing.closedPoint O ∈ Set.range (Spec.map (CommRingCat.ofHom π)).base := by
      refine ⟨(⊥ : PrimeSpectrum κ), ?_⟩
      show PrimeSpectrum.comap π ⊥ = IsLocalRing.closedPoint O
      apply PrimeSpectrum.ext
      show Ideal.comap π ⊥ = IsLocalRing.maximalIdeal O
      rw [← RingHom.ker_eq_comap_bot, hker]
    have hab : Spec.map (CommRingCat.ofHom π) ≫ (sec z).1 = Spec.map (CommRingCat.ofHom π) ≫ (sec 1).1 := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, hsec_fst, hsec_fst, hred]
        have h1 := G.one_natural (Spec.map (CommRingCat.ofHom ρ)) (Spec.map (CommRingCat.ofHom (π.comp ρ)))
          (Spec.map (CommRingCat.ofHom π)) hπρ
        exact (congrArg Subtype.val h1).symm
      · rw [Category.assoc, Category.assoc, hsec_snd, hsec_snd]
    have key := AlgebraicGeometry.FormallyUnramified.eq_of_comp_eq_of_isLocalRing (G'.schemeNsmul n) (sec z).1 (sec 1).1 hf
      (Spec.map (CommRingCat.ofHom π)) ht hab
    apply Subtype.ext
    rw [← hsec_fst z, ← hsec_fst 1, key]
  ·
    intro w hw
    have hwn : G.nsmul _ n w = G.one _ := by rw [← pow_eq_nsmul, hw]; rfl

    let sεi := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
    have hψ : sεi ≫ Spec.map (CommRingCat.ofHom (π.comp ρ)) =
        Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O))) ≫ ι := by
      show Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom (π.comp ρ)) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ Spec.map (CommRingCat.ofHom ρ)
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hπe]
      congr 2
      ext a
      show e.symm (e (IsLocalRing.residue O (ρ a))) = IsLocalRing.residue O (ρ a)
      exact e.symm_apply_apply _
    let wt : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O))) ≫ ι) f :=
      GoodReductionJacobian.schemeHomOverComp sεi hψ w
    have hwtn : G.nsmul _ n wt = G.one _ := by
      show G.nsmul _ n (GoodReductionJacobian.schemeHomOverComp sεi hψ w) = G.one _
      rw [← G.nsmul_natural _ _ sεi hψ n w, hwn, G.one_natural]
    let y₀ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O)))) f' :=
      RelativeGroupLaw.baseChangePointOfBase ι wt
    have hy₀ : G'.nsmul _ n y₀ = GoodReductionJacobian.schemeHomOverComp
        (Spec.map (CommRingCat.ofHom (algebraMap O (IsLocalRing.ResidueField O)))) (Category.comp_id _) (G'.one (𝟙 _)) := by
      rw [G'.one_natural]
      apply (RelativeGroupLaw.baseChangePointEquiv ι _).injective
      show RelativeGroupLaw.baseChangePointToBase ι (G'.nsmul _ n y₀) = RelativeGroupLaw.baseChangePointToBase ι (G'.one _)
      rw [baseChangePointToBase_nsmul, RelativeGroupLaw.baseChangePointToBase_one]
      show G.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι wt)) = _
      rw [RelativeGroupLaw.baseChangePointToBase_ofBase, hwtn]
    obtain ⟨y, hyred, hyn⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing G' (fun t x y => hc' t x y)
        d n hnO (G'.one (𝟙 _)) y₀ hy₀

    let z : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) f := castBase hic.symm (RelativeGroupLaw.baseChangePointToBase ι y)
    have hz1 : z.1 = y.1 ≫ pullback.fst f ι := rfl
    refine ⟨z, ?_, ?_⟩
    ·
      rw [pow_eq_nsmul]
      show G.nsmul _ n (castBase hic.symm (RelativeGroupLaw.baseChangePointToBase ι y)) = G.one _
      rw [nsmul_castBase, ← baseChangePointToBase_nsmul, hyn, RelativeGroupLaw.baseChangePointToBase_one, one_castBase]
    ·
      rw [hz1, hSpecπ, Category.assoc, ← Category.assoc (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))]
      have hy1 : Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)) ≫ y.1 = y₀.1 := congrArg Subtype.val hyred
      rw [hy1]
      show w.1 = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (pullback.lift wt.1 _ wt.2) ≫ pullback.fst f ι
      rw [pullback.lift_fst]
      show w.1 = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ sεi ≫ w.1
      rw [← Category.assoc, hee, Category.id_comp]

end S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_pow_eq_one_of_reduction_eq_and_exists_pow_eq_one_reduction_eq_of_isUnit_of_henselianLocalRing (solution)
