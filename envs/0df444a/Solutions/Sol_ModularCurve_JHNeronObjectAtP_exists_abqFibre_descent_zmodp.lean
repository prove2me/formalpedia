-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_abqFibre_descent_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/69f3dcc8-a407-5a25-87b5-02274349b5f5

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_AlgebraicGeometry_exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq
import Theorems.Thm_AlgebraicGeometry_isReduced_of_smooth_over_field
import Theorems.Thm_AlgebraicGeometry_eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_abqFibre_descent_zmodp

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

namespace QABQ22

theorem algebra_isAlgebraic_zmod_residueField
    (K : Type*) [Field K] [Algebra ℚ K] [Algebra.IsAlgebraic ℚ K]
    (A : ValuationSubring K) (p : ℕ) [Fact p.Prime]
    [Algebra (ZMod p) (IsLocalRing.ResidueField ↥A)] :
    Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField ↥A) := by
  classical
  have hp : p.Prime := Fact.out
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ K).injective
  refine ⟨fun r => ?_⟩
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r

  have ha : IsAlgebraic ℤ ((a : ↥A) : K) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr (Algebra.IsAlgebraic.isAlgebraic _)
  obtain ⟨P, hP0, hPa⟩ := ha
  have hQprim : P.primPart.IsPrimitive := P.isPrimitive_primPart
  have hQa : Polynomial.aeval ((a : ↥A) : K) P.primPart = 0 := Polynomial.aeval_primPart_eq_zero hP0 hPa

  have hQaA : Polynomial.aeval (a : ↥A) P.primPart = 0 := by
    have h1 : Polynomial.aeval (algebraMap (↥A) K a) P.primPart = algebraMap (↥A) K (Polynomial.aeval a P.primPart) :=
      Polynomial.aeval_algebraMap_apply K a P.primPart
    have h2 : algebraMap (↥A) K (Polynomial.aeval a P.primPart) = 0 := by rw [← h1]; exact hQa
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (↥A) K)).mp h2
  have hres : Polynomial.aeval (IsLocalRing.residue (↥A) a) (P.primPart.map (algebraMap ℤ (ZMod p))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      RingHom.ext_int ((algebraMap (ZMod p) (IsLocalRing.ResidueField ↥A)).comp (algebraMap ℤ (ZMod p))) (algebraMap ℤ _),
      ← Polynomial.aeval_def]
    have := Polynomial.aeval_algHom_apply ((IsLocalRing.residue ↥A).toIntAlgHom) a P.primPart
    rw [RingHom.toIntAlgHom_apply] at this
    exact this.trans (by rw [hQaA, map_zero])

  have hne : P.primPart.map (algebraMap ℤ (ZMod p)) ≠ 0 := by
    intro h0
    have hdvd : Polynomial.C (p : ℤ) ∣ P.primPart := by
      rw [Polynomial.C_dvd_iff_dvd_coeff]
      intro n
      have hn := congrArg (fun q => q.coeff n) h0
      simp only [Polynomial.coeff_map, Polynomial.coeff_zero, algebraMap_int_eq, Int.coe_castRingHom] at hn
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hn
    have hu := hQprim (p : ℤ) hdvd
    rw [Int.isUnit_iff] at hu
    have h2 := hp.two_le
    omega
  exact ⟨P.primPart.map (algebraMap ℤ (ZMod p)), hne, hres⟩

end QABQ22

open ModularCurve in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    [IsSeparated Λ.f] [LocallyOfFiniteType Λ.f]

    [Algebra (ZMod p) (ResidueField ↥A)]
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A))) ≫ σp = resPt A ≫ Λ.σA) :
    ∃ q : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f),

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i))) ∧

      (∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (resPt A ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (resPt A ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1) := by
  classical

  haveI : Algebra.IsAlgebraic (ZMod p) (ResidueField ↥A) :=
    QABQ22.algebra_isAlgebraic_zmod_residueField (AlgebraicClosure ℚ) A p
  haveI : IsAlgClosure (ZMod p) (ResidueField ↥A) := ⟨inferInstance, inferInstance⟩
  haveI : Normal (ZMod p) (ResidueField ↥A) := IsAlgClosure.normal _ _
  haveI : Algebra.IsSeparable (ZMod p) (ResidueField ↥A) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : IsGalois (ZMod p) (ResidueField ↥A) := {}

  haveI := O.quasiCompact
  haveI := O.separated
  haveI := O.locallyOfFiniteType
  haveI := O.smooth
  let tκ := Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))
  let fX := pullback.snd O.g σp
  let fY := pullback.snd Λ.f σp
  let θX : pullback fX tκ ≅ pullback O.g (resPt A ≫ Λ.σA) :=
    pullbackLeftPullbackSndIso O.g σp tκ ≪≫ pullback.congrHom rfl hfac
  let θY : pullback fY tκ ≅ pullback Λ.f (resPt A ≫ Λ.σA) :=
    pullbackLeftPullbackSndIso Λ.f σp tκ ≪≫ pullback.congrHom rfl hfac
  have hθXsnd : θX.hom ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = pullback.snd fX tκ := by
    show (_ ≫ (pullback.congrHom rfl hfac).hom) ≫ _ = _
    rw [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  have hθYsnd : θY.hom ≫ pullback.snd Λ.f (resPt A ≫ Λ.σA) = pullback.snd fY tκ := by
    show (_ ≫ (pullback.congrHom rfl hfac).hom) ≫ _ = _
    rw [Category.assoc, pullback.congrHom_hom, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  have hθXfst : θX.hom ≫ pullback.fst O.g (resPt A ≫ Λ.σA) = pullback.fst fX tκ ≫ pullback.fst O.g σp := by
    show (_ ≫ (pullback.congrHom rfl hfac).hom) ≫ _ = _
    rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  have hθYfst : θY.hom ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) = pullback.fst fY tκ ≫ pullback.fst Λ.f σp := by
    show (_ ≫ (pullback.congrHom rfl hfac).hom) ≫ _ = _
    rw [Category.assoc, pullback.congrHom_hom, pullback.lift_fst, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]

  let f : Fin 2 → (pullback fX tκ ⟶ pullback fY tκ) := fun i => θX.hom ≫ (O.abqFibre i).1 ≫ θY.inv
  have hf : ∀ i, f i ≫ pullback.snd fY tκ = pullback.snd fX tκ := by
    intro i
    have h2 : (O.abqFibre i).1 ≫ pullback.snd Λ.f (resPt A ≫ Λ.σA) = pullback.snd O.g (resPt A ≫ Λ.σA) := (O.abqFibre i).2
    simp only [f, Category.assoc]
    rw [← hθYsnd, θY.inv_hom_id_assoc, h2, hθXsnd]

  haveI : CompactSpace ↥(pullback O.g σp) := QuasiCompact.compactSpace_of_compactSpace fX
  haveI : QuasiSeparatedSpace ↥(pullback O.g σp) := quasiSeparatedSpace_of_quasiSeparated fX

  haveI hXκred : IsReduced (pullback O.g (resPt A ≫ Λ.σA)) :=
    AlgebraicGeometry.isReduced_of_smooth_over_field (g := pullback.snd O.g (resPt A ≫ Λ.σA)) inferInstance
  have hgal : ∀ (i : Fin 2) (σ : ResidueField ↥A ≃ₐ[ZMod p] ResidueField ↥A)
      (hσ : Spec.map (CommRingCat.ofHom ((σ : ResidueField ↥A →ₐ[ZMod p] ResidueField ↥A) : ResidueField ↥A →+* ResidueField ↥A)) ≫ tκ = tκ),
      pullback.map fX tκ fX tκ (𝟙 _) (Spec.map (CommRingCat.ofHom ((σ : ResidueField ↥A →ₐ[ZMod p] ResidueField ↥A) : ResidueField ↥A →+* ResidueField ↥A))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ f i =
        f i ≫ pullback.map fY tκ fY tκ (𝟙 _) (Spec.map (CommRingCat.ofHom ((σ : ResidueField ↥A →ₐ[ZMod p] ResidueField ↥A) : ResidueField ↥A →+* ResidueField ↥A))) (𝟙 _)
          (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) := by
    intro i σ hσ

    have hofHom : CommRingCat.ofHom ((σ : ResidueField ↥A →ₐ[ZMod p] ResidueField ↥A) : ResidueField ↥A →+* ResidueField ↥A) =
        σ.toRingEquiv.toCommRingCatIso.hom := by
      rw [RingEquiv.toCommRingCatIso_hom]; rfl
    haveI : IsIso (Spec.map (CommRingCat.ofHom ((σ : ResidueField ↥A →ₐ[ZMod p] ResidueField ↥A) : ResidueField ↥A →+* ResidueField ↥A))) := by
      rw [hofHom]; infer_instance
    set s := Spec.map (CommRingCat.ofHom ((σ : ResidueField ↥A →ₐ[ZMod p] ResidueField ↥A) : ResidueField ↥A →+* ResidueField ↥A)) with hsdef
    have hs : s ≫ resPt A ≫ Λ.σA = resPt A ≫ Λ.σA := by rw [← hfac, ← Category.assoc, hσ]

    let TX := pullback.map O.g (resPt A ≫ Λ.σA) O.g (resPt A ≫ Λ.σA) (𝟙 _) s (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hs])
    let TY := pullback.map Λ.f (resPt A ≫ Λ.σA) Λ.f (resPt A ≫ Λ.σA) (𝟙 _) s (𝟙 _)
      (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hs])
    haveI : IsIso TY := by dsimp only [TY]; infer_instance

    have hC : TX ≫ (O.abqFibre i).1 = (O.abqFibre i).1 ≫ TY := by
      have hTXfst : TX ≫ pullback.fst O.g (resPt A ≫ Λ.σA) = pullback.fst O.g (resPt A ≫ Λ.σA) := by
        rw [pullback.lift_fst, Category.comp_id]
      have hTXsnd : TX ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = pullback.snd O.g (resPt A ≫ Λ.σA) ≫ s := pullback.lift_snd _ _ _
      have hTYfst : TY ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) = pullback.fst Λ.f (resPt A ≫ Λ.σA) := by
        rw [pullback.lift_fst, Category.comp_id]
      have hTYsnd : TY ≫ pullback.snd Λ.f (resPt A ≫ Λ.σA) = pullback.snd Λ.f (resPt A ≫ Λ.σA) ≫ s := pullback.lift_snd _ _ _
      have hiTYfst : inv TY ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) = pullback.fst Λ.f (resPt A ≫ Λ.σA) := by
        rw [IsIso.inv_comp_eq, hTYfst]
      have hiTYsnd : inv TY ≫ pullback.snd Λ.f (resPt A ≫ Λ.σA) = pullback.snd Λ.f (resPt A ≫ Λ.σA) ≫ inv s := by
        rw [IsIso.inv_comp_eq, ← Category.assoc, hTYsnd, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      have habq2 : (O.abqFibre i).1 ≫ pullback.snd Λ.f (resPt A ≫ Λ.σA) = pullback.snd O.g (resPt A ≫ Λ.σA) := (O.abqFibre i).2
      suffices hsuff : TX ≫ (O.abqFibre i).1 ≫ inv TY = (O.abqFibre i).1 by
        have := congrArg (· ≫ TY) hsuff
        simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using this
      apply AlgebraicGeometry.eq_of_forall_specMap_comp_eq_of_flat_of_isReduced_of_isSeparated
        (ResidueField ↥A) (ResidueField ↥A) (pullback.snd O.g (resPt A ≫ Λ.σA)) (pullback.snd Λ.f (resPt A ≫ Λ.σA))
      · rw [Category.assoc, Category.assoc, hiTYsnd, ← Category.assoc (O.abqFibre i).1, habq2, ← Category.assoc, hTXsnd,
          Category.assoc, IsIso.hom_inv_id, Category.comp_id]
      · exact habq2
      intro ξ hξ
      have hξ1 : ξ ≫ pullback.snd O.g (resPt A ≫ Λ.σA) = 𝟙 _ := by
        rw [hξ, Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _

      have hx0 : (ξ ≫ pullback.fst O.g (resPt A ≫ Λ.σA)) ≫ O.g = resPt A ≫ Λ.σA := by
        rw [Category.assoc, pullback.condition, ← Category.assoc, hξ1, Category.id_comp]
      let x : SchemeHomOver (resPt A ≫ Λ.σA) O.g := ⟨ξ ≫ pullback.fst O.g (resPt A ≫ Λ.σA), hx0⟩
      have hs' : inv s ≫ resPt A ≫ Λ.σA = resPt A ≫ Λ.σA := by rw [IsIso.inv_comp_eq, hs]
      let x'' : SchemeHomOver (resPt A ≫ Λ.σA) O.g := GoodReductionJacobian.schemeHomOverComp (inv s) hs' x
      have hτx : GoodReductionJacobian.schemeHomOverComp s hs x'' = x := by
        apply Subtype.ext
        simp only [GoodReductionJacobian.schemeHomOverComp_coe, x'', IsIso.hom_inv_id_assoc]
      have htw := O.abqFibre_twist ⟨s, hs⟩ i x''
      rw [hτx] at htw
      have htw1 := congrArg Subtype.val htw
      simp only [fibreMap, ofFibrePt, toFibrePt, overId, RelativeGroupLaw.baseChangePointToBase_coe,
        RelativeGroupLaw.baseChangePointOfBase_coe, NeronModelInfra.schemeHomOverComp_coe,
        GoodReductionJacobian.schemeHomOverComp_coe, Category.assoc] at htw1

      have hξeq : pullback.lift x.1 (𝟙 _) (by rw [Category.id_comp]; exact x.2) = ξ := by
        apply pullback.hom_ext
        · rw [pullback.lift_fst]
        · rw [pullback.lift_snd, hξ1]
      have hξTX : ξ ≫ TX = s ≫ pullback.lift x''.1 (𝟙 _) (by rw [Category.id_comp]; exact x''.2) := by
        apply pullback.hom_ext
        · rw [Category.assoc, hTXfst, Category.assoc, pullback.lift_fst]
          show ξ ≫ pullback.fst O.g (resPt A ≫ Λ.σA) = s ≫ inv s ≫ (ξ ≫ pullback.fst O.g (resPt A ≫ Λ.σA))
          rw [IsIso.hom_inv_id_assoc]
        · rw [Category.assoc, hTXsnd, ← Category.assoc, hξ1, Category.id_comp, Category.assoc, pullback.lift_snd,
            Category.comp_id]
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, Category.assoc, hiTYfst, ← Category.assoc ξ, hξTX, Category.assoc, Category.assoc,
          ← hξeq, htw1]
      · rw [Category.assoc, Category.assoc, Category.assoc, hiTYsnd, ← Category.assoc (O.abqFibre i).1, habq2,
          ← Category.assoc ξ, hξTX, Category.assoc, Category.assoc, pullback.lift_snd_assoc, Category.id_comp, IsIso.hom_inv_id,
          habq2, hξ1]

    have hθXT : θX.hom ≫ TX = pullback.map fX tκ fX tκ (𝟙 _) s (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ θX.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, hθXfst, Category.assoc, hθXfst, pullback.lift_fst_assoc,
          Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hθXsnd, Category.assoc, hθXsnd, pullback.lift_snd]
    have hθYT : θY.hom ≫ TY = pullback.map fY tκ fY tκ (𝟙 _) s (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) ≫ θY.hom := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, hθYfst, Category.assoc, hθYfst, pullback.lift_fst_assoc,
          Category.comp_id]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hθYsnd, Category.assoc, hθYsnd, pullback.lift_snd]
    have hθYT' : TY ≫ θY.inv = θY.inv ≫ pullback.map fY tκ fY tκ (𝟙 _) s (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id, hσ]) := by
      rw [Iso.eq_inv_comp, ← Category.assoc, hθYT, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    show _ ≫ (θX.hom ≫ (O.abqFibre i).1 ≫ θY.inv) = (θX.hom ≫ (O.abqFibre i).1 ≫ θY.inv) ≫ _
    rw [← Category.assoc, ← hθXT, Category.assoc, Category.assoc, ← Category.assoc TX, hC, Category.assoc, hθYT',
      Category.assoc]

  have hdesc := fun i => AlgebraicGeometry.exists_unique_eq_pullback_map_of_forall_galois_twist_comp_eq (ZMod p) (ResidueField ↥A)
    (pullback O.g σp) (pullback Λ.f σp) fX fY (f i) (hf i) (hgal i)
  choose g hg hfg huniq using hdesc
  refine ⟨fun i => ⟨g i, hg i⟩, ?_, ?_⟩
  ·
    intro i T s x y
    apply Subtype.ext

    have mul_coe_congr : ∀ {T' : Scheme.{0}} {t t' : T' ⟶ base p} (htt : t = t')
        (u v : SchemeHomOver t Λ.f) (u' v' : SchemeHomOver t' Λ.f), u.1 = u'.1 → v.1 = v'.1 →
        (Λ.L.mul t u v).1 = (Λ.L.mul t' u' v').1 := by
      intro T' t t' htt u v u' v' hu hv
      subst htt
      cases Subtype.ext hu
      cases Subtype.ext hv
      rfl

    let Tκ := pullback s tκ
    let pr := pullback.fst s tκ
    let sκ := pullback.snd s tκ
    haveI : Epi pr := by
      haveI : Surjective tκ := ⟨fun z => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
      haveI : Surjective pr := MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance
      haveI : Flat pr := MorphismProperty.pullback_fst (P := @Flat) _ _ inferInstance
      haveI : QuasiCompact pr := MorphismProperty.pullback_fst (P := @QuasiCompact) _ _ inferInstance
      infer_instance
    rw [← cancel_epi pr]
    have hsκ : sκ ≫ resPt A ≫ Λ.σA = pr ≫ s ≫ σp := by
      rw [← hfac, ← Category.assoc, ← pullback.condition, Category.assoc]

    have liftX : ∀ u : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g),
        (pullback.lift (pr ≫ u.1) sκ (by rw [Category.assoc, u.2, pullback.condition]) ≫ θX.hom) ≫
          pullback.snd O.g (resPt A ≫ Λ.σA) = sκ := by
      intro u; rw [Category.assoc, hθXsnd, pullback.lift_snd]
    let hat : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g) → SchemeHomOver sκ (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
      fun u => ⟨pullback.lift (pr ≫ u.1) sκ (by rw [Category.assoc, u.2, pullback.condition]) ≫ θX.hom, liftX u⟩
    have hat_fst : ∀ u, (hat u).1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) = pr ≫ u.1 ≫ pullback.fst O.g σp := by
      intro u
      show (pullback.lift (pr ≫ u.1) sκ _ ≫ θX.hom) ≫ _ = _
      rw [Category.assoc, hθXfst, pullback.lift_fst_assoc, Category.assoc]

    have hat_abq : ∀ u, (hat u).1 ≫ (O.abqFibre i).1 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) = pr ≫ u.1 ≫ g i ≫ pullback.fst Λ.f σp := by
      intro u
      have e1 : (O.abqFibre i).1 = θX.inv ≫ f i ≫ θY.hom := by
        simp only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
      show (pullback.lift (pr ≫ u.1) sκ _ ≫ θX.hom) ≫ _ ≫ _ = _
      rw [e1]
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [hθYfst, hfg i, pullback.lift_fst_assoc]
      simp only [Category.assoc]
      erw [pullback.lift_fst_assoc]
      rw [Category.assoc]

    have hat_mul : (hat ((O.L.baseChange σp).mul s x y)).1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) =
        ((O.L.baseChange (resPt A ≫ Λ.σA)).mul sκ (hat x) (hat y)).1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) := by
      rw [hat_fst]
      have l1 : ((O.L.baseChange σp).mul s x y).1 ≫ pullback.fst O.g σp =
          (O.L.mul (s ≫ σp) (RelativeGroupLaw.baseChangePointToBase σp x) (RelativeGroupLaw.baseChangePointToBase σp y)).1 := by
        rw [← RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_mul]
      have l2 : ((O.L.baseChange (resPt A ≫ Λ.σA)).mul sκ (hat x) (hat y)).1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) =
          (O.L.mul (sκ ≫ resPt A ≫ Λ.σA) (RelativeGroupLaw.baseChangePointToBase _ (hat x)) (RelativeGroupLaw.baseChangePointToBase _ (hat y))).1 := by
        rw [← RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_mul]
      rw [l1, l2]
      have mn : pr ≫ (O.L.mul (s ≫ σp) (RelativeGroupLaw.baseChangePointToBase σp x) (RelativeGroupLaw.baseChangePointToBase σp y)).1 =
          (O.L.mul (pr ≫ s ≫ σp) (GoodReductionJacobian.schemeHomOverComp pr rfl (RelativeGroupLaw.baseChangePointToBase σp x))
            (GoodReductionJacobian.schemeHomOverComp pr rfl (RelativeGroupLaw.baseChangePointToBase σp y))).1 :=
        congrArg Subtype.val (O.L.mul_natural (s ≫ σp) (pr ≫ s ≫ σp) pr rfl _ _)
      rw [mn]
      have mcg : ∀ {T' : Scheme.{0}} {t t' : T' ⟶ base p} (htt : t = t')
          (u v : SchemeHomOver t O.g) (u' v' : SchemeHomOver t' O.g), u.1 = u'.1 → v.1 = v'.1 →
          (O.L.mul t u v).1 = (O.L.mul t' u' v').1 := by
        intro T' t t' htt u v u' v' hu hv; subst htt; cases Subtype.ext hu; cases Subtype.ext hv; rfl
      apply mcg hsκ.symm
      · rw [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
          hat_fst]
      · rw [GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_coe,
          hat_fst]

    have hat_mul' : hat ((O.L.baseChange σp).mul s x y) = (O.L.baseChange (resPt A ≫ Λ.σA)).mul sκ (hat x) (hat y) := by
      apply Subtype.ext
      apply pullback.hom_ext
      · exact hat_mul
      · rw [(hat _).2, ((O.L.baseChange (resPt A ≫ Λ.σA)).mul sκ (hat x) (hat y)).2]
    apply pullback.hom_ext
    ·
      rw [Category.assoc, Category.assoc, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, ← hat_abq, hat_mul']
      have r1 : ((O.L.baseChange (resPt A ≫ Λ.σA)).mul sκ (hat x) (hat y)).1 ≫ (O.abqFibre i).1 ≫ pullback.fst Λ.f (resPt A ≫ Λ.σA) =
          (Λ.L.mul (sκ ≫ resPt A ≫ Λ.σA)
            (RelativeGroupLaw.baseChangePointToBase _ (NeronModelInfra.schemeHomOverComp (hat x) (O.abqFibre i)))
            (RelativeGroupLaw.baseChangePointToBase _ (NeronModelInfra.schemeHomOverComp (hat y) (O.abqFibre i)))).1 := by
        rw [← Category.assoc, ← NeronModelInfra.schemeHomOverComp_coe, O.abqFibre_mul i sκ (hat x) (hat y),
          ← RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_mul]
      rw [r1]
      have r2 : pr ≫ ((Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x ⟨g i, hg i⟩)
          (NeronModelInfra.schemeHomOverComp y ⟨g i, hg i⟩)).1 ≫ pullback.fst Λ.f σp =
          (Λ.L.mul (pr ≫ s ≫ σp)
            (GoodReductionJacobian.schemeHomOverComp pr rfl (RelativeGroupLaw.baseChangePointToBase σp (NeronModelInfra.schemeHomOverComp x ⟨g i, hg i⟩)))
            (GoodReductionJacobian.schemeHomOverComp pr rfl (RelativeGroupLaw.baseChangePointToBase σp (NeronModelInfra.schemeHomOverComp y ⟨g i, hg i⟩)))).1 := by
        rw [← RelativeGroupLaw.baseChangePointToBase_coe, RelativeGroupLaw.baseChangePointToBase_mul]
        exact congrArg Subtype.val (Λ.L.mul_natural (s ≫ σp) (pr ≫ s ≫ σp) pr rfl _ _)
      rw [r2]
      apply mul_coe_congr hsκ
      · rw [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hat_abq,
          GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
          Category.assoc]
      · rw [RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc, hat_abq,
          GoodReductionJacobian.schemeHomOverComp_coe, RelativeGroupLaw.baseChangePointToBase_coe, NeronModelInfra.schemeHomOverComp_coe,
          Category.assoc]
    ·
      rw [Category.assoc, Category.assoc, NeronModelInfra.schemeHomOverComp_coe, Category.assoc,
        show g i ≫ pullback.snd Λ.f σp = fX from hg i, ((O.L.baseChange σp).mul s x y).2,
        ((Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x ⟨g i, hg i⟩) (NeronModelInfra.schemeHomOverComp y ⟨g i, hg i⟩)).2]
  ·
    intro i
    have hπY : θY.hom ≫ pullback.map Λ.f (resPt A ≫ Λ.σA) Λ.f σp (𝟙 _) tκ (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) = pullback.fst fY tκ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, hθYfst]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hθYsnd, pullback.condition]
    have hπX : θX.hom ≫ pullback.map O.g (resPt A ≫ Λ.σA) O.g σp (𝟙 _) tκ (𝟙 _)
        (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) = pullback.fst fX tκ := by
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.comp_id, hθXfst]
      · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, hθXsnd, pullback.condition]
    have habq : (O.abqFibre i).1 = θX.inv ≫ f i ≫ θY.hom := by
      simp only [f, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]
    rw [habq, Category.assoc, Category.assoc, hπY, ← cancel_epi θX.hom, θX.hom_inv_id_assoc, ← Category.assoc θX.hom, hπX,
      hfg i, pullback.lift_fst]

end S_ModularCurve_JHNeronObjectAtP_exists_abqFibre_descent_zmodp
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_abqFibre_descent_zmodp (solution)
