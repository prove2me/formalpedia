-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/2131cfc1-aafb-5be0-85cb-1710c3ef161b

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
p2m_attr_erase "instance" "MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

namespace KToricStable

abbrev red (t m : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem red_apply (t m : ℕ) (z : Fin t → ℤ) (i : Fin t) : red t m z i = (z i : ZMod m) := rfl

private def _root_.KToricStable.lift (t m : ℕ) (g : Fin t → ZMod m) : Fin t → ℤ := fun i => ((g i).cast : ℤ)

p2m_export "KToricStable" "lift"
theorem red_lift (t m : ℕ) [NeZero m] (g : Fin t → ZMod m) : red t m (lift t m g) = g := by
  funext i
  simp [red_apply, lift, ZMod.intCast_zmod_cast]

theorem red_map_eq_of_red_eq (t m : ℕ) (M₀ : (Fin t → ℤ) →+ (Fin t → ℤ)) (z z' : Fin t → ℤ)
    (h : red t m z = red t m z') : red t m (M₀ z) = red t m (M₀ z') := by
  have hd : ∀ i, (m : ℤ) ∣ z i - z' i := by
    intro i
    have hi := congrFun h i
    rw [red_apply, red_apply] at hi
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (z' i) (z i) m).mp hi.symm
  choose w hw using hd
  have hz : z = z' + (m : ℤ) • (fun i => w i) := by
    funext i; simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; have := hw i; omega
  funext i
  rw [red_apply, red_apply, hz, map_add, map_zsmul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Int.cast_add,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, add_zero]

def redEnd (t m : ℕ) [NeZero m] (M₀ : (Fin t → ℤ) →+ (Fin t → ℤ)) : (Fin t → ZMod m) →+ (Fin t → ZMod m) where
  toFun g := red t m (M₀ (lift t m g))
  map_zero' := by
    have h : red t m (lift t m 0) = red t m 0 := by rw [red_lift, map_zero]
    rw [red_map_eq_of_red_eq t m M₀ _ _ h, map_zero, map_zero]
  map_add' g g' := by
    have h : red t m (lift t m (g + g')) = red t m (lift t m g + lift t m g') := by
      rw [red_lift, map_add, red_lift, red_lift]
    rw [red_map_eq_of_red_eq t m M₀ _ _ h, map_add, map_add]

theorem redEnd_red (t m : ℕ) [NeZero m] (M₀ : (Fin t → ℤ) →+ (Fin t → ℤ)) (z : Fin t → ℤ) :
    redEnd t m M₀ (red t m z) = red t m (M₀ z) := by
  show red t m (M₀ (lift t m (red t m z))) = red t m (M₀ z)
  apply red_map_eq_of_red_eq
  rw [red_lift]

theorem conv_single {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M : Type} [AddCommMonoid M]
    (χ ψ : WithConv (AddMonoidAlgebra S M →ₐ[S] T)) (g : M) :
    (χ * ψ).ofConv (AddMonoidAlgebra.single g 1) = χ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
  rw [AlgHom.convMul_def]
  simp [AddMonoidAlgebra.comul_single, Algebra.TensorProduct.lmul'_apply_tmul]

theorem conv_comp_mapDomain {S T : Type} [CommRing S] [CommRing T] [Algebra S T] {M N : Type} [AddCommMonoid M] [AddCommMonoid N]
    (f : M →+ N) (χ ψ : WithConv (AddMonoidAlgebra S N →ₐ[S] T)) :
    (χ * ψ).ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f) =
      (WithConv.toConv (χ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f)) *
        WithConv.toConv (ψ.ofConv.comp (AddMonoidAlgebra.mapDomainAlgHom S S f))).ofConv := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro g
  rw [AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single, conv_single, conv_single]
  simp only [WithConv.ofConv_toConv, AlgHom.comp_apply, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]

end KToricStable

noncomputable section

namespace LDTwist

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

def decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) : ↥A →+* ↥A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) ↥A ⟨σ, hσ⟩

theorem subtype_comp_decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    A.subtype.comp (decAut σ hσ) = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
  RingHom.ext fun _ => rfl

theorem specMap_comp_barPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A =
      barPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) := by
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, subtype_comp_decAut]

theorem specMap_comp_genPt {p : ℕ} (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) s) = algebraMap (baseRing p) (AlgebraicClosure ℚ) s
  rw [IsScalarTower.algebraMap_apply (baseRing p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

theorem specMap_decAut_comp_σA {p : ℕ} {σA : Spec (CommRingCat.of ↥A) ⟶ base p} (hσA : barPt A ≫ σA = genPt p)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ σA = σA := by
  have h : barPt A ≫ (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ σA) = barPt A ≫ σA := by
    rw [← Category.assoc, ← specMap_comp_barPt, Category.assoc, hσA, specMap_comp_genPt]
  set a := Spec.preimage (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ σA) with ha
  set b := Spec.preimage σA with hb
  have ha' : Spec.map a = Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ σA := Spec.map_preimage _
  have hb' : Spec.map b = σA := Spec.map_preimage _
  rw [← ha', ← hb'] at h ⊢
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom A.subtype) := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  rw [cancel_mono] at h2
  rw [h2]

noncomputable def twist (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {G : Type} [AddCommMonoid G]
    (θ : AddMonoidAlgebra ↥A G →ₐ[↥A] AlgebraicClosure ℚ) : AddMonoidAlgebra ↥A G →ₐ[↥A] AlgebraicClosure ℚ :=
  AddMonoidAlgebra.lift ↥A (AlgebraicClosure ℚ) G
    ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ).toRingEquiv.toMonoidHom.comp
      (θ.toRingHom.toMonoidHom.comp (AddMonoidAlgebra.of ↥A G)))

theorem twist_single (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {G : Type} [AddCommMonoid G]
    (θ : AddMonoidAlgebra ↥A G →ₐ[↥A] AlgebraicClosure ℚ) (g : G) :
    twist τ θ (AddMonoidAlgebra.single g 1) = τ (θ (AddMonoidAlgebra.single g 1)) := by
  rw [twist, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem twist_single' (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {G : Type} [AddCommMonoid G]
    (θ : AddMonoidAlgebra ↥A G →ₐ[↥A] AlgebraicClosure ℚ) (g : G) (a : ↥A) :
    twist τ θ (AddMonoidAlgebra.single g a) = (a : AlgebraicClosure ℚ) * τ (θ (AddMonoidAlgebra.single g 1)) := by
  rw [show AddMonoidAlgebra.single g a = a • AddMonoidAlgebra.single g (1 : ↥A) by
    rw [AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one], map_smul, twist_single, Algebra.smul_def]
  rfl

theorem comp_mapRingHom_decAut_eq (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ)
    {G : Type} [AddCommMonoid G] (θ : AddMonoidAlgebra ↥A G →ₐ[↥A] AlgebraicClosure ℚ) :
    θ.toRingHom.comp (AddMonoidAlgebra.mapRingHom G (decAut σ hσ)) =
      (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp (twist σ.symm θ).toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single]
    show θ (algebraMap ↥A _ (decAut σ hσ b)) = σ (twist σ.symm θ (algebraMap ↥A _ b))
    rw [AlgHom.commutes, AlgHom.commutes]
    rfl
  · intro g
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, map_one]
    show θ (AddMonoidAlgebra.single g 1) = σ (twist σ.symm θ (AddMonoidAlgebra.single g 1))
    rw [twist_single, AlgEquiv.apply_symm_apply]

theorem twist_conv (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) {G : Type} [AddCommMonoid G]
    (χ ψ : WithConv (AddMonoidAlgebra ↥A G →ₐ[↥A] AlgebraicClosure ℚ)) :
    twist τ (χ * ψ).ofConv = (WithConv.toConv (twist τ χ.ofConv) * WithConv.toConv (twist τ ψ.ofConv)).ofConv := by
  refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
  intro g
  rw [twist_single, KToricStable.conv_single, KToricStable.conv_single, map_mul]
  simp only [WithConv.ofConv_toConv, twist_single]

end LDTwist

end

open KToricStable LDTwist in
set_option maxHeartbeats 6400000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)))
    (P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hP₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius (ResidueField ↥A) p))) ≫ O.torusFibre.1 =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
    (m : ℕ) (hm : 0 < m) :
    ∃ Pbar : (Fin O.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m),
      Pbar.comp (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)) =
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i)).comp P₀ ∧
      ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
        ∃ χφ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
          (∀ g : Fin O.toricRank → ZMod m,
            χφ (AddMonoidAlgebra.single g 1) = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • χ (AddMonoidAlgebra.single g 1)) ∧
          φ • O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ) =
            O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χφ.comp (AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pbar))) := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  set LA := O.L.baseChange Λ.σA with hLA
  set κ := ResidueField ↥A with hκ

  have hres : (IsLocalRing.residue ↥A).comp (decAut φ hφD) = (frobenius κ p).comp (IsLocalRing.residue ↥A) := by
    refine RingHom.ext fun a => ?_
    show IsLocalRing.residue ↥A ((⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = (IsLocalRing.residue ↥A a) ^ p
    rw [IsLocalRing.ResidueField.residue_smul]
    exact hφ.smul_residue_eq _
  have hdσ : Spec.map (CommRingCat.ofHom (decAut φ hφD)) ≫ Λ.σA = Λ.σA := specMap_decAut_comp_σA Λ.hσA φ hφD
  have hdσ' : Spec.map (CommRingCat.ofHom (decAut φ⁻¹ (inv_mem hφD))) ≫ Λ.σA = Λ.σA :=
    specMap_decAut_comp_σA Λ.hσA φ⁻¹ (inv_mem hφD)
  have hφbase : Spec.map (CommRingCat.ofHom (φ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A ≫ Λ.σA = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, specMap_comp_barPt φ hφD, Category.assoc, hdσ]

  have hΘE : ∃ Θ : pullback O.g Λ.σA ⟶ pullback O.g Λ.σA,
      Θ ≫ pullback.fst _ _ = pullback.fst _ _ ∧
      Θ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (decAut φ⁻¹ (inv_mem hφD))) := by
    refine ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (decAut φ⁻¹ (inv_mem hφD)))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    rw [pullback.condition, Category.assoc, hdσ']
  obtain ⟨Θ, hΘ₁, hΘ₂⟩ := hΘE
  have hdd : Spec.map (CommRingCat.ofHom (decAut φ hφD)) ≫ Spec.map (CommRingCat.ofHom (decAut φ⁻¹ (inv_mem hφD))) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : (decAut φ hφD).comp (decAut φ⁻¹ (inv_mem hφD)) = RingHom.id ↥A := by
      refine RingHom.ext fun a => Subtype.ext ?_
      show φ (φ⁻¹ (a : AlgebraicClosure ℚ)) = a
      exact φ.apply_symm_apply _
    rw [h, CommRingCat.ofHom_id]
    exact Spec.map_id _

  let Pb : (Fin O.toricRank → ZMod m) →+ (Fin O.toricRank → ZMod m) := redEnd O.toricRank m P₀
  let ψP : muCoord ↥A O.toricRank m →ₐ[↥A] muCoord ↥A O.toricRank m := AddMonoidAlgebra.mapDomainAlgHom ↥A ↥A Pb

  have hmu : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (decAut φ hφD))) ≫
      muStr ↥A O.toricRank m = muStr ↥A O.toricRank m ≫ Spec.map (CommRingCat.ofHom (decAut φ hφD)) := by
    rw [muStr, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => ?_
    show AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (decAut φ hφD) (AddMonoidAlgebra.single 0 a) =
      AddMonoidAlgebra.single 0 (decAut φ hφD a)
    rw [AddMonoidAlgebra.mapRingHom_single]
  let u : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
    ⟨Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (decAut φ hφD))) ≫
        (O.toricLift m hm).1 ≫ Θ, by
      show (_ ≫ _ ≫ Θ) ≫ pullback.snd O.g Λ.σA = muStr ↥A O.toricRank m
      rw [Category.assoc, Category.assoc, hΘ₂, ← Category.assoc (O.toricLift m hm).1,
        show (O.toricLift m hm).1 ≫ pullback.snd O.g Λ.σA = muStr ↥A O.toricRank m from (O.toricLift m hm).2,
        ← Category.assoc, hmu, Category.assoc, hdd, Category.comp_id]⟩
  let v : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g) :=
    ⟨Spec.map (CommRingCat.ofHom ψP.toRingHom) ≫ (O.toricLift m hm).1, by
      rw [Category.assoc, (O.toricLift m hm).2, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2; exact ψP.comp_algebraMap⟩
  have hu1 : u.1 = Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (decAut φ hφD))) ≫
      (O.toricLift m hm).1 ≫ Θ := rfl
  have hv1 : v.1 = Spec.map (CommRingCat.ofHom ψP.toRingHom) ≫ (O.toricLift m hm).1 := rfl

  have hpt_u : ∀ θ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      RelativeGroupLaw.baseChangePointToBase Λ.σA (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m θ) u) =
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (φ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) hφbase
          (RelativeGroupLaw.baseChangePointToBase Λ.σA
            (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (twist φ.symm θ)) (O.toricLift m hm))) := by
    intro θ
    apply Subtype.ext
    show ((muPt A O.toricRank m θ).1 ≫ u.1) ≫ pullback.fst O.g Λ.σA =
      Spec.map (CommRingCat.ofHom (φ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
        ((muPt A O.toricRank m (twist φ.symm θ)).1 ≫ (O.toricLift m hm).1) ≫ pullback.fst O.g Λ.σA
    have hsq : (muPt A O.toricRank m θ).1 ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (decAut φ hφD))) =
        Spec.map (CommRingCat.ofHom (φ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (muPt A O.toricRank m (twist φ.symm θ)).1 := by
      show Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ _ = _ ≫ Spec.map (CommRingCat.ofHom (twist φ.symm θ).toRingHom)
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, comp_mapRingHom_decAut_eq]
    rw [hu1, Category.assoc, Category.assoc, Category.assoc, hΘ₁, ← Category.assoc, hsq, Category.assoc, Category.assoc]
  have hpt_v : ∀ θ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m θ) v =
        NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (θ.comp ψP)) (O.toricLift m hm) := by
    intro θ
    apply Subtype.ext
    show Spec.map (CommRingCat.ofHom θ.toRingHom) ≫ Spec.map (CommRingCat.ofHom ψP.toRingHom) ≫ (O.toricLift m hm).1 =
      Spec.map (CommRingCat.ofHom (θ.comp ψP).toRingHom) ≫ (O.toricLift m hm).1
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl

  have hu : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) u =
        LA.mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) u)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) u) := by
    intro χ χ'
    apply (RelativeGroupLaw.baseChangePointEquiv Λ.σA (barPt A)).injective
    show RelativeGroupLaw.baseChangePointToBase Λ.σA _ = RelativeGroupLaw.baseChangePointToBase Λ.σA _
    rw [RelativeGroupLaw.baseChangePointToBase_mul, hpt_u, hpt_u, hpt_u, twist_conv, O.toricLift_mul m hm,
      RelativeGroupLaw.baseChangePointToBase_mul]
    exact O.L.mul_natural _ _ _ hφbase _ _
  have hv : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) v =
        LA.mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) v)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) v) := by
    intro χ χ'
    rw [hpt_v, hpt_v, hpt_v, conv_comp_mapDomain]
    exact O.toricLift_mul m hm _ _

  have hI0 : muBaseChange (residue ↥A) O.toricRank m ≫
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (decAut φ hφD))) =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (frobenius κ p))) ≫
        muBaseChange (residue ↥A) O.toricRank m := by
    rw [muBaseChange, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      ← AddMonoidAlgebra.mapRingHom_comp, ← AddMonoidAlgebra.mapRingHom_comp, hres]

  have hI1 : muBaseChange (residue ↥A) O.toricRank m ≫ Spec.map (CommRingCat.ofHom ψP.toRingHom) =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Pb)) ≫ muBaseChange (residue ↥A) O.toricRank m := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      simp [ψP, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single]
    · intro g
      simp [ψP, AddMonoidAlgebra.mapRingHom_single, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomainAlgHom_apply,
        AddMonoidAlgebra.mapDomain_single]
  have hI2 : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ Pb)) ≫ muToTorus κ O.toricRank m =
      muToTorus κ O.toricRank m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ P₀)) := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
    congr 2
    apply AddMonoidAlgebra.ringHom_ext
    · intro b
      simp [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
    · intro g
      simp only [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]
      congr 1
      exact redEnd_red O.toricRank m P₀ g

  have hI3 : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (frobenius κ p))) ≫ muToTorus κ O.toricRank m =
      muToTorus κ O.toricRank m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius κ p))) := by
    rw [muToTorus, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      AddMonoidAlgebra.mapRingHom_comp_mapDomainRingHom]

  have hsp' : ∀ {W : Scheme.{0}} (k : O.G ⟶ W),
      muBaseChange (residue ↥A) O.toricRank m ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA ≫ k =
        muToTorus κ O.toricRank m ≫ O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) ≫ k := by
    intro W k
    simpa only [Category.assoc] using congrArg (· ≫ k) (O.toricLift_special m hm)
  have hP₀' : ∀ {W : Scheme.{0}} (k : _ ⟶ W),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius κ p))) ≫ O.torusFibre.1 ≫ k =
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ P₀)) ≫ O.torusFibre.1 ≫ ΞG ≫ k := by
    intro W k
    simpa only [Category.assoc] using congrArg (· ≫ k) hP₀
  have re : ∀ {X Y Y' Z W : Scheme.{0}} {a : X ⟶ Y} {c : Y ⟶ Z} {b : X ⟶ Y'} {d : Y' ⟶ Z} (h : a ≫ c = b ≫ d) (k : Z ⟶ W),
      a ≫ c ≫ k = b ≫ d ≫ k := by
    intro X Y Y' Z W a c b d h k
    simpa only [Category.assoc] using congrArg (· ≫ k) h
  have huv : muBaseChange (residue ↥A) O.toricRank m ≫ u.1 = muBaseChange (residue ↥A) O.toricRank m ≫ v.1 := by
    apply pullback.hom_ext
    · have lhs : (muBaseChange (residue ↥A) O.toricRank m ≫ u.1) ≫ pullback.fst O.g Λ.σA =
          muToTorus κ O.toricRank m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ P₀)) ≫ O.torusFibre.1 ≫
            pullback.fst O.g (resPt A ≫ Λ.σA) := by
        rw [hu1]; simp only [Category.assoc]
        rw [hΘ₁, re hI0, O.toricLift_special m hm, re hI3, hP₀', hΞ₁]
      have rhs : (muBaseChange (residue ↥A) O.toricRank m ≫ v.1) ≫ pullback.fst O.g Λ.σA =
          muToTorus κ O.toricRank m ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ P₀)) ≫ O.torusFibre.1 ≫
            pullback.fst O.g (resPt A ≫ Λ.σA) := by
        rw [hv1]; simp only [Category.assoc]
        rw [re hI1, O.toricLift_special m hm, re hI2]
      rw [lhs, rhs]
    · have h2 : ∀ w : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g),
          (muBaseChange (residue ↥A) O.toricRank m ≫ w.1) ≫ pullback.snd O.g Λ.σA =
            muBaseChange (residue ↥A) O.toricRank m ≫ muStr ↥A O.toricRank m := by
        intro w; rw [Category.assoc, show w.1 ≫ pullback.snd O.g Λ.σA = muStr ↥A O.toricRank m from w.2]
      rw [h2 u, h2 v]

  have huv' := ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq p M H hpM A hA Λ O m hm u v hu hv huv

  refine ⟨Pb, AddMonoidHom.ext fun z => redEnd_red O.toricRank m P₀ z, fun χ => ?_⟩

  let Fφ : Multiplicative (Fin O.toricRank → ZMod m) →* ↥A :=
    (decAut φ hφD).toMonoidHom.comp (χ.toRingHom.toMonoidHom.comp (AddMonoidAlgebra.of ↥A (Fin O.toricRank → ZMod m)))
  let χφ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A := AddMonoidAlgebra.lift ↥A ↥A (Fin O.toricRank → ZMod m) Fφ
  have hχφ : ∀ g : Fin O.toricRank → ZMod m,
      χφ (AddMonoidAlgebra.single g 1) = (⟨φ, hφD⟩ : ↥(A.decompositionSubgroup ℚ)) • χ (AddMonoidAlgebra.single g 1) := by
    intro g
    show AddMonoidAlgebra.lift ↥A ↥A (Fin O.toricRank → ZMod m) Fφ (AddMonoidAlgebra.single g 1) = _
    rw [AddMonoidAlgebra.lift_single, one_smul]
    rfl
  refine ⟨χφ, hχφ, ?_⟩

  have htw : twist φ.symm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χφ) = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ := by
    refine AddMonoidAlgebra.algHom_ext ?_ (Subsingleton.elim _ _)
    intro g
    rw [twist_single, AlgHom.comp_apply, AlgHom.comp_apply, hχφ]
    show φ.symm (φ ((χ (AddMonoidAlgebra.single g 1) : ↥A) : AlgebraicClosure ℚ)) = _
    rw [AlgEquiv.symm_apply_apply]
    rfl

  apply O.pts.injective
  apply Subtype.ext
  rw [O.pts_galois]
  show Spec.map (CommRingCat.ofHom (φ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (O.pts (O.pts.symm _)).1 = (O.pts (O.pts.symm _)).1
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  show Spec.map (CommRingCat.ofHom (φ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
      ((muPt A O.toricRank m ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χ)).1 ≫ (O.toricLift m hm).1) ≫ pullback.fst O.g Λ.σA =
    ((muPt A O.toricRank m ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χφ.comp ψP))).1 ≫ (O.toricLift m hm).1) ≫ pullback.fst O.g Λ.σA
  have h1 := congrArg Subtype.val (hpt_u ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χφ))
  rw [htw] at h1

  have h2 := congrArg Subtype.val (hpt_v ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χφ))

  have h3 : ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χφ).comp ψP = (Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp (χφ.comp ψP) := rfl
  rw [h3] at h2
  rw [huv'] at h1

  exact h1.symm.trans (congrArg (· ≫ pullback.fst O.g Λ.σA) h2)

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_smul_toricPoint_eq_toricPoint_galoisValues_comp_mapDomainAlgHom (solution)
