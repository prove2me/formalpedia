-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d6795566-cfe5-5ac4-b8d5-54d6c91c45dc

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod"
p2m_attr_erase "simp" "AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

namespace ATPSkel

open ModularCurve.JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

omit [IsAlgClosed (ResidueField ↥A)] in

theorem exists_algHom_valuationSubring_of_muCoord {t m : ℕ} (hm : 0 < m)
    (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ χA : muCoord ↥A t m →ₐ[↥A] ↥A, χ = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA := by
  classical
  have hroot : ∀ g : Fin t → ZMod m, (χ (AddMonoidAlgebra.single g 1)) ^ m = 1 := by
    intro g
    rw [← map_pow, AddMonoidAlgebra.single_pow, one_pow]
    have hg : m • g = 0 := by
      funext i
      show m • g i = 0
      rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rw [hg]
    exact map_one χ
  have hmem : ∀ g : Fin t → ZMod m, χ (AddMonoidAlgebra.single g 1) ∈ A := by
    intro g
    have hint : IsIntegral ↥A (χ (AddMonoidAlgebra.single g 1)) := by
      refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hroot g, sub_self]
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ↥A) (K := AlgebraicClosure ℚ)).mp hint
    rw [← hy]
    exact y.2
  let φ : Multiplicative (Fin t → ZMod m) →* ↥A :=
    { toFun := fun g => ⟨χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1), hmem _⟩
      map_one' := Subtype.ext (by
        show χ (AddMonoidAlgebra.single (0 : Fin t → ZMod m) 1) = 1
        exact map_one χ)
      map_mul' := fun g h => Subtype.ext (by
        show χ (AddMonoidAlgebra.single (Multiplicative.toAdd (g * h)) 1) =
          χ (AddMonoidAlgebra.single (Multiplicative.toAdd g) 1) * χ (AddMonoidAlgebra.single (Multiplicative.toAdd h) 1)
        rw [← map_mul, AddMonoidAlgebra.single_mul_single, one_mul]
        rfl) }
  refine ⟨AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod m) φ, ?_⟩
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  rw [AlgHom.comp_apply, AddMonoidAlgebra.lift_single, one_smul]
  rfl

omit [Fact p.Prime] in
theorem specMap_comp_genPt' (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) s) = algebraMap (baseRing p) (AlgebraicClosure ℚ) s
  rw [IsScalarTower.algebraMap_apply (baseRing p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

omit [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

theorem specMap_decRestrict_comp_σA (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (dE : ↥A ≃+* ↥A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hdE : ∀ a : ↥A, ((dE a : ↥A) : AlgebraicClosure ℚ) = σ a) :
    Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA = Λ.σA := by
  have hsub : A.subtype.comp dE.toRingHom = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
    RingHom.ext fun a => hdE a
  have hbar : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A =
      barPt A ≫ Spec.map (CommRingCat.ofHom dE.toRingHom) := by
    rw [barPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hsub]
  have h : barPt A ≫ (Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, ← hbar, Category.assoc, Λ.hσA, specMap_comp_genPt']
  set a := Spec.preimage (Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA) with ha
  set b := Spec.preimage Λ.σA with hb
  have ha' : Spec.map a = Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA := Spec.map_preimage _
  have hb' : Spec.map b = Λ.σA := Spec.map_preimage _
  rw [← ha', ← hb'] at h ⊢
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom A.subtype) := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  rw [cancel_mono] at h2
  rw [h2]

section conv
variable {S' : Type} [CommRing S'] {L' : Type} [CommRing L'] [Algebra S' L'] {G' : Type} [AddMonoid G']

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (v : G') :
    (c * c') (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G') :
    (1 : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S' G' →ₐ[S'] L')) (n : ℕ) (v : G') :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, pow_succ, convMul_apply_single, ih]

end conv

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

theorem hasEnoughRootsOfUnity_algebraicClosure (n : ℕ) [NeZero n] : HasEnoughRootsOfUnity (AlgebraicClosure ℚ) n := by
  refine ⟨?_, rootsOfUnity.isCyclic _ _⟩
  have hdeg : (Polynomial.cyclotomic n (AlgebraicClosure ℚ)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos n)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

theorem tate_of_levelwise' (O : JHNeronObjectAtP p M H hpM A hA Λ) (S : Set ℕ) (g : CohCarrier.Gen M S)
    (Tt : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTt : ∀ x : TateModule p (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.toricPts (p ^ n))
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℤ_[p])
    (hlev : ∀ (n : ℕ) (y : JH M H), y ∈ O.toricPts (p ^ n) →
      φ • y ∈ O.toricPts (p ^ n) ∧ genOpH M H S g (φ • y) = ((a.appr n : ℕ) : ℤ) • y ∧
        φ • (genOpH M H S g y) = ((a.appr n : ℕ) : ℤ) • y) :
    ∀ x ∈ Tt,
      JH.tateGaloisRep M H p φ x ∈ Tt ∧
      tateGenOpH M H S p g (JH.tateGaloisRep M H p φ x) = a • x ∧
      JH.tateGaloisRep M H p φ (tateGenOpH M H S p g x) = a • x := by
  intro x hx
  rw [hTt] at hx
  refine ⟨?_, ?_, ?_⟩
  · rw [hTt]
    intro n
    exact (hlev n _ (hx n)).1
  · refine Subtype.ext (funext fun n => ?_)
    rw [TateModule.smul_apply]
    exact (hlev n _ (hx n)).2.1
  · refine Subtype.ext (funext fun n => ?_)
    rw [TateModule.smul_apply]
    exact (hlev n _ (hx n)).2.2

end ATPSkel

open ModularCurve.JHNeronObjectAtP
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (S : Set ℕ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = p)
    (Tt : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n))

    (hTOR : ∀ (perm : Equiv.Perm ↥O.ssFinset)
      (hperm : ∀ t : ↥O.ssFinset,
        ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
            (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
              Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
        ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
            (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
              Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2)
      (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
      (x : JH M H) (s s' : SchemeHomOver Λ.σA O.g)
      (hs : (O.pts x).1 = barPt A ≫ s.1) (hs' : (O.pts (φ • x)).1 = barPt A ≫ s'.1)
      (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
      (hw : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset w),
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s') = GluedPic0.nodeUnit O.ssFinset (fun t => p • w (perm.symm t)))

    (σN : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσN : ∀ n : ↥O.ssFinset, (σN n).1.2 = n.1.1)
    (hUPtor : ∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w))
          (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
        GluedPic0.nodeUnit O.ssFinset (w ∘ σN))

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ) :
    ∀ x ∈ Tt,
      JH.tateGaloisRep M H ℓ φ x ∈ Tt ∧
      tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) (JH.tateGaloisRep M H ℓ φ x) =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ φ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x ∧
      JH.tateGaloisRep M H ℓ φ (tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) x) =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ φ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x := by
  classical
  subst ℓ
  haveI : PerfectField (ResidueField ↥A) := IsAlgClosed.perfectField (ResidueField ↥A)

  have hdE : ∃ dE : ↥A ≃+* ↥A, (∀ a : ↥A, dE a = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • a) :=
    ⟨MulSemiringAction.toRingEquiv _ _ (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)), fun a => rfl⟩
  obtain ⟨dE, hdEa⟩ := hdE
  have hres : (IsLocalRing.residue ↥A).comp dE.toRingHom = (frobenius (ResidueField ↥A) p).comp (IsLocalRing.residue ↥A) := by
    refine RingHom.ext fun a => ?_
    show IsLocalRing.residue ↥A (dE a) = (IsLocalRing.residue ↥A a) ^ p
    rw [hdEa, IsLocalRing.ResidueField.residue_smul]
    exact hφ.smul_residue_eq _
  have hdσ : Spec.map (CommRingCat.ofHom dE.toRingHom) ≫ Λ.σA = Λ.σA :=
    ATPSkel.specMap_decRestrict_comp_σA Λ dE φ (fun a => by rw [hdEa]; rfl)
  have hbase : Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ resPt A ≫ Λ.σA = resPt A ≫ Λ.σA := by
    have h1 : resPt A ≫ Spec.map (CommRingCat.ofHom dE.toRingHom) = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ resPt A := by
      rw [resPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hres]
    rw [← Category.assoc, ← h1, Category.assoc, hdσ]

  have hΞE : ∃ ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA),
      ΞG ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) := by
    refine ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [pullback.condition, Category.assoc, hbase]
  obtain ⟨ΞG, hΞ₁, hΞ₂⟩ := hΞE

  have hψ : (frobeniusEquiv (ResidueField ↥A) p).toRingHom = frobenius (ResidueField ↥A) p := rfl
  have hLA := ModularCurve.JHNeronObjectAtP.exists_mapRingHom_comp_torusFibre_eq_mapDomain_comp_torusFibre_comp_baseTwist
    p M H hpM A hA Λ hΛ O (frobeniusEquiv (ResidueField ↥A) p) ΞG hΞ₁ hΞ₂
  obtain ⟨P₀, hP₀⟩ := hLA

  have hTS := ModularCurve.JHNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
    p M H hpM A hA Λ hΛ O (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)) (fun s x y => O.hecke_mul S _ s x y)
  obtain ⟨M₀, hM₀⟩ := hTS

  have hLB := ModularCurve.JHNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
    p M H hpM A hA Λ O ΞG hΞ₁ hΞ₂ P₀ hP₀ S M₀ hM₀ hTOR σN hσN hUPtor φ hφ hφD
  obtain ⟨hPM, hMP⟩ := hLB

  refine ATPSkel.tate_of_levelwise' O S (CohCarrier.Gen.U p (Fact.out) hpM) Tt hTt φ
    (((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p])) ?_
  intro n y hy
  have hm : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n

  have hLD := ModularCurve.JHNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
    p M H hpM A hA Λ O ΞG hΞ₁ hΞ₂ P₀ hP₀ φ hφ hφD (p ^ n) hm
  obtain ⟨Pbar, hPbar, hLDχ⟩ := hLD

  have hTM := ModularCurve.JHNeronObjectAtP.exists_comp_toricLift_fibreRestrictAlong_eq_toricLift_comp_mapDomainAlgHom
    p M H hpM A hA Λ hΛ O (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)) (fun s x y => O.hecke_mul S _ s x y) M₀ hM₀ (p ^ n) hm
  obtain ⟨Mbar, hMbar, hTMχ⟩ := hTM

  have hH1 := ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
    p M H hpM A hA Λ O (p ^ n) hm
  obtain ⟨hconv, -, hmem, -⟩ := hH1

  have hPMbar : Pbar.comp Mbar = AddMonoidHom.id _ ∧ Mbar.comp Pbar = AddMonoidHom.id _ := by
    haveI : NeZero (p ^ n) := ⟨hm.ne'⟩
    have hsurj : ∀ v : Fin O.toricRank → ZMod (p ^ n), ∃ z : Fin O.toricRank → ℤ,
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod (p ^ n))).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)) z = v :=
      fun v => ⟨fun i => ((v i).cast : ℤ), funext fun i => by
        show (((v i).cast : ℤ) : ZMod (p ^ n)) = v i
        exact ZMod.intCast_zmod_cast (v i)⟩
    have hPbar' := fun z => DFunLike.congr_fun hPbar z
    have hMbar' := fun z => DFunLike.congr_fun hMbar z
    have hPM' := fun z => DFunLike.congr_fun hPM z
    have hMP' := fun z => DFunLike.congr_fun hMP z
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at hPbar' hMbar' hPM' hMP'
    constructor
    · refine AddMonoidHom.ext fun v => ?_
      obtain ⟨z, rfl⟩ := hsurj v
      rw [AddMonoidHom.comp_apply, hMbar', hPbar', hPM', AddMonoidHom.id_apply]
    · refine AddMonoidHom.ext fun v => ?_
      obtain ⟨z, rfl⟩ := hsurj v
      rw [AddMonoidHom.comp_apply, hPbar', hMbar', hMP', AddMonoidHom.id_apply]

  have hUtor : ∀ χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) (O.toricPoint (p ^ n) hm χ) =
        O.toricPoint (p ^ n) hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := by
    intro χ
    apply O.pts.injective
    apply Subtype.ext
    rw [O.hecke_pts]
    show (O.pts (O.pts.symm _)).1 ≫ _ = (O.pts (O.pts.symm _)).1
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    have h := congrArg (fun w => w.1 ≫ pullback.fst O.g Λ.σA) (hTMχ χ)
    simp only [NeronModelInfra.schemeHomOverComp_coe, Category.assoc, NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst] at h
    show (((muPt A O.toricRank (p ^ n) χ).1 ≫ (O.toricLift (p ^ n) hm).1) ≫ pullback.fst O.g Λ.σA) ≫
        (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)).1 =
      ((muPt A O.toricRank (p ^ n) (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))).1 ≫ (O.toricLift (p ^ n) hm).1) ≫
        pullback.fst O.g Λ.σA
    simpa only [Category.assoc] using h

  have hcyc : ∀ (χ χφ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] ↥A),
      (∀ g : Fin O.toricRank → ZMod (p ^ n),
        χφ (AddMonoidAlgebra.single g 1) = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • χ (AddMonoidAlgebra.single g 1)) →
      χφ = χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
        ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)) := by
    intro χ χφ hχφ
    haveI hEn : ∀ i, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i =>
      haveI : NeZero (p ^ i) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
      ATPSkel.hasEnoughRootsOfUnity_algebraicClosure _
    refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
    intro g
    rw [hχφ, AlgHom.comp_apply]
    have hmd : AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
        ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)
        (AddMonoidAlgebra.single g (1 : ↥A)) =
        AddMonoidAlgebra.single ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • g) 1 := by
      show AddMonoidAlgebra.mapDomainRingHom ↥A _ (AddMonoidAlgebra.single g 1) = _
      rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
      rfl
    have hsp : AddMonoidAlgebra.single ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • g) (1 : ↥A) =
        (AddMonoidAlgebra.single g (1 : ↥A)) ^ (((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) := by
      rw [AddMonoidAlgebra.single_pow, one_pow]
    rw [hmd, hsp, map_pow]

    set u : ↥A := χ (AddMonoidAlgebra.single g 1) with hu
    have hupow : u ^ (p ^ n) = 1 := by
      rw [hu, ← map_pow, AddMonoidAlgebra.single_pow, one_pow]
      have hg : (p ^ n) • g = 0 := by
        funext i
        show (p ^ n) • g i = 0
        rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
      rw [hg]
      exact map_one χ
    apply Subtype.ext
    show φ (u : AlgebraicClosure ℚ) = ((u ^ _ : ↥A) : AlgebraicClosure ℚ)
    rw [SubmonoidClass.coe_pow]
    have hval : ((u : AlgebraicClosure ℚ)) ^ p ^ n = 1 := by
      rw [← SubmonoidClass.coe_pow, hupow]; rfl
    have hspec := cyclotomicCharacter.spec p (L := AlgebraicClosure ℚ) (n := n) φ.toRingEquiv (u : AlgebraicClosure ℚ) hval
    rw [show (φ.toRingEquiv : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (u : AlgebraicClosure ℚ) = φ (u : AlgebraicClosure ℚ) from rfl] at hspec
    rw [hspec]
    congr 1
    show (PadicInt.toZModPow n _).val = _
    rw [TateModule.toZModPow_eq_appr, ZMod.val_natCast, Nat.mod_eq_of_lt (PadicInt.appr_lt _ _)]

  have hhom : ∀ (c : ℕ) (χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ),
      O.toricPoint (p ^ n) hm (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _))) =
        ((c : ℕ) : ℤ) • O.toricPoint (p ^ n) hm χ := by
    intro c χ
    have hpow : χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _)) = ((WithConv.toConv χ) ^ c).ofConv := by
      refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
      intro g
      rw [AlgHom.comp_apply]
      have hmd : AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (c • AddMonoidHom.id _) (AddMonoidAlgebra.single g (1 : ↥A)) =
          AddMonoidAlgebra.single (c • g) 1 := by
        show AddMonoidAlgebra.mapDomainRingHom ↥A _ (AddMonoidAlgebra.single g 1) = _
        rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
        rfl
      rw [hmd, ← one_pow c, ← AddMonoidAlgebra.single_pow, map_pow, one_pow]
      exact (ATPSkel.convPow_apply_single (WithConv.toConv χ) c g).symm
    rw [hpow]
    have h1 : O.toricPoint (p ^ n) hm (1 : WithConv (muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
      have h := hconv 1 1
      rw [mul_one] at h
      exact left_eq_add.mp h
    have key : ∀ k : ℕ, O.toricPoint (p ^ n) hm ((WithConv.toConv χ) ^ k).ofConv = ((k : ℕ) : ℤ) • O.toricPoint (p ^ n) hm χ := by
      intro k
      induction k with
      | zero => rw [pow_zero, h1, Nat.cast_zero, zero_zsmul]
      | succ k ih =>
        rw [pow_succ, hconv, ih, Nat.cast_succ, add_zsmul, one_zsmul]
    exact key c

  have hcomp : ∀ (χ : muCoord ↥A O.toricRank (p ^ n) →ₐ[↥A] ↥A) (f g : (Fin O.toricRank → ZMod (p ^ n)) →+ (Fin O.toricRank → ZMod (p ^ n))),
      ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A f))).comp
          (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A g) =
        (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A (f.comp g))) := by
    intro χ f g
    rw [AddMonoidAlgebra.mapDomainAlgHom_comp]
    rfl

  obtain ⟨χ, rfl⟩ := (hmem y).mp hy
  obtain ⟨χA, hχA⟩ := ATPSkel.exists_algHom_valuationSubring_of_muCoord (A := A) hm χ
  subst hχA
  obtain ⟨χφ, hχφ, hφι⟩ := hLDχ χA
  refine ⟨?_, ?_, ?_⟩
  ·
    rw [hφι]
    exact (hmem _).mpr ⟨_, rfl⟩
  ·
    rw [hφι, hUtor, hcomp, hPMbar.1, hcyc χA χφ hχφ, AddMonoidAlgebra.mapDomainAlgHom_id, AlgHom.comp_id]
    exact hhom _ ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)
  ·
    rw [hUtor]
    obtain ⟨χφ', hχφ', hφι'⟩ := hLDχ (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar))
    have h3 : ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar) =
        (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)) := rfl
    rw [h3, hφι', hcyc _ χφ' hχφ']
    have hcm : ((χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Mbar)).comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
        ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _))).comp
        (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pbar) =
        χA.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A
          ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _)) := by
      have hsw : Mbar.comp ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _) =
          ((((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]).appr n) • AddMonoidHom.id _).comp Mbar := by
        refine AddMonoidHom.ext fun v => ?_
        simp only [AddMonoidHom.comp_apply, AddMonoidHom.smul_apply, AddMonoidHom.id_apply, map_nsmul]
      rw [AlgHom.comp_assoc, AlgHom.comp_assoc, ← AddMonoidAlgebra.mapDomainAlgHom_comp, ← AddMonoidAlgebra.mapDomainAlgHom_comp,
        ← AddMonoidHom.comp_assoc, hsw, AddMonoidHom.comp_assoc, hPMbar.2, AddMonoidHom.comp_id]
    rw [hcm]
    exact hhom _ ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA)

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq (solution)
