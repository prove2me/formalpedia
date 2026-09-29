-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/18f28e16-f917-502d-b4d7-e94d0586ff4f

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_torusPt_residue_toricLift_and_torusFibre_injective
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
import Theorems.Thm_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_hecke_U

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

open scoped MatrixGroups

noncomputable section

namespace TwistCancel

section conv

variable {S : Type} [CommRing S] {L : Type} [CommRing L] [Algebra S L] {G : Type} [AddMonoid G]

theorem convMul_apply_single (c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (v : G) :
    (c * c') (AddMonoidAlgebra.single v 1) =
      c (AddMonoidAlgebra.single v 1) * c' (AddMonoidAlgebra.single v 1) := by
  rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single, CommSemiring.comul_apply, TensorProduct.map_tmul,
    Algebra.TensorProduct.lift_tmul]
  simp

theorem convOne_apply_single (v : G) :
    (1 : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (AddMonoidAlgebra.single v 1) = 1 := by
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single, CommSemiring.counit_apply, map_one]

theorem convPow_apply_single (c : WithConv (AddMonoidAlgebra S G →ₐ[S] L)) (n : ℕ) (v : G) :
    (c ^ n) (AddMonoidAlgebra.single v 1) = c (AddMonoidAlgebra.single v 1) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, convOne_apply_single]
  | succ n ih => rw [pow_succ, pow_succ, convMul_apply_single, ih]

end conv

section relpts

variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}

theorem eq_of_coe_fst_eq (z z' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (RelativeGroupLaw.baseChangeStr ι f))
    (h : z.1 ≫ pullback.fst f ι = z'.1 ≫ pullback.fst f ι) : z = z' := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact h
  · rw [z.2, z'.2]

end relpts

section torus

variable (κ : Type) [Field κ] (t : ℕ)

theorem torusPt_comp_mapDomain_coe (ψ : torusCoord κ t →ₐ[κ] κ) (N : (Fin t → ℤ) →+ (Fin t → ℤ)) :
    (torusPt κ t (ψ.comp (AddMonoidAlgebra.mapDomainAlgHom κ κ N))).1 =
      (torusPt κ t ψ).1 ≫ Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom κ N)) := by
  change Spec.map (CommRingCat.ofHom (ψ.comp (AddMonoidAlgebra.mapDomainAlgHom κ κ N)).toRingHom) =
    Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

theorem mapDomainAlgHom_single (N : (Fin t → ℤ) →+ (Fin t → ℤ)) (v : Fin t → ℤ) :
    AddMonoidAlgebra.mapDomainAlgHom κ κ N (AddMonoidAlgebra.single v (1 : κ)) = AddMonoidAlgebra.single (N v) 1 := by
  change AddMonoidAlgebra.mapDomainRingHom κ N (AddMonoidAlgebra.single v 1) = _
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single]

theorem mapDomainAlgHom_comp (N N' : (Fin t → ℤ) →+ (Fin t → ℤ)) :
    (AddMonoidAlgebra.mapDomainAlgHom κ κ N).comp (AddMonoidAlgebra.mapDomainAlgHom κ κ N') =
      AddMonoidAlgebra.mapDomainAlgHom κ κ (N.comp N') :=
  AddMonoidAlgebra.algHom_ext (fun v => by
    rw [AlgHom.comp_apply, mapDomainAlgHom_single, mapDomainAlgHom_single, mapDomainAlgHom_single]; rfl) (Subsingleton.elim _ _)

abbrev powChar (n : ℕ) (ψ : torusCoord κ t →ₐ[κ] κ) : torusCoord κ t →ₐ[κ] κ :=
  ((WithConv.toConv ψ) ^ n).ofConv

theorem powChar_single (n : ℕ) (ψ : torusCoord κ t →ₐ[κ] κ) (v : Fin t → ℤ) :
    powChar κ t n ψ (AddMonoidAlgebra.single v 1) = ψ (AddMonoidAlgebra.single v 1) ^ n :=
  convPow_apply_single (WithConv.toConv ψ) n v

theorem powChar_comp_mapDomain (n : ℕ) (ψ : torusCoord κ t →ₐ[κ] κ) (N : (Fin t → ℤ) →+ (Fin t → ℤ)) :
    powChar κ t n (ψ.comp (AddMonoidAlgebra.mapDomainAlgHom κ κ N)) =
      (powChar κ t n ψ).comp (AddMonoidAlgebra.mapDomainAlgHom κ κ N) :=
  AddMonoidAlgebra.algHom_ext (fun v => by
    rw [powChar_single, AlgHom.comp_apply, AlgHom.comp_apply, mapDomainAlgHom_single, powChar_single]) (Subsingleton.elim _ _)

theorem specMap_frobenius_comp_torusPt (p : ℕ) [Fact p.Prime] [CharP κ p] (ψ : torusCoord κ t →ₐ[κ] κ) :
    Spec.map (CommRingCat.ofHom (frobenius κ p)) ≫ (torusPt κ t ψ).1 =
      (torusPt κ t (powChar κ t p ψ)).1 ≫
        Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) (frobenius κ p))) := by
  change Spec.map (CommRingCat.ofHom (frobenius κ p)) ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) =
    Spec.map (CommRingCat.ofHom (powChar κ t p ψ).toRingHom) ≫ _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_)
  · change frobenius κ p (ψ (AddMonoidAlgebra.single 0 b)) =
      powChar κ t p ψ (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) (frobenius κ p) (AddMonoidAlgebra.single 0 b))
    rw [AddMonoidAlgebra.mapRingHom_single]
    have e1 : AddMonoidAlgebra.single (0 : Fin t → ℤ) b = algebraMap κ (torusCoord κ t) b := rfl
    have e2 : AddMonoidAlgebra.single (0 : Fin t → ℤ) (frobenius κ p b) = algebraMap κ (torusCoord κ t) (frobenius κ p b) := rfl
    rw [e1, e2, AlgHom.commutes, AlgHom.commutes]
    rfl
  · change frobenius κ p (ψ (AddMonoidAlgebra.single v 1)) =
      powChar κ t p ψ (AddMonoidAlgebra.mapRingHom (Fin t → ℤ) (frobenius κ p) (AddMonoidAlgebra.single v 1))
    rw [AddMonoidAlgebra.mapRingHom_single, map_one, powChar_single, frobenius_def]

end torus

section A4Tor

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem nodeShift_fst_snd (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (σN : ↥O.ssFinset ≃ ↥O.ssFinset) (hσN : ∀ n : ↥O.ssFinset, (σN n).1.2 = n.1.1) (t : ↥O.ssFinset) :
    ((σN t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
        Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
    ((σN t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
        Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 =
      qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
        (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
          Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 := by
  have hnode : ∀ n : ↥O.ssFinset,
      (n : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
        qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p n.1.2 := fun n =>
    (mem_ssNodePairsQExp_iff _).mp ((O.mem_ssFinset_iff _).mp n.2) |>.2
  refine ⟨?_, ?_⟩
  · rw [hnode (σN t), hσN]
  · rw [hσN, ← hnode t]

def decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) : ↥A →+* ↥A :=
  MulSemiringAction.toRingHom (A.decompositionSubgroup ℚ) ↥A ⟨σ, hσ⟩

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem subtype_comp_decAut (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    A.subtype.comp (decAut σ hσ) = (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype :=
  RingHom.ext fun _ => rfl

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_comp_barPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A =
      barPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) := by
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, subtype_comp_decAut]

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_comp_genPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  rw [genPt, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext s
  show σ (algebraMap (baseRing p) (AlgebraicClosure ℚ) s) = algebraMap (baseRing p) (AlgebraicClosure ℚ) s
  rw [IsScalarTower.algebraMap_apply (baseRing p) ℚ (AlgebraicClosure ℚ), AlgEquiv.commutes]

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
theorem specMap_decAut_comp_σA (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.decompositionSubgroup ℚ) :
    Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA = Λ.σA := by
  have h : barPt A ≫ (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA) = barPt A ≫ Λ.σA := by
    rw [← Category.assoc, ← specMap_comp_barPt, Category.assoc, Λ.hσA, specMap_comp_genPt]
  set a := Spec.preimage (Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA) with ha
  set b := Spec.preimage Λ.σA with hb
  have ha' : Spec.map a = Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ Λ.σA := Spec.map_preimage _
  have hb' : Spec.map b = Λ.σA := Spec.map_preimage _
  rw [← ha', ← hb'] at h ⊢
  rw [barPt, ← Spec.map_comp, ← Spec.map_comp] at h
  have h2 := Spec.map_injective h
  haveI : Mono (CommRingCat.ofHom A.subtype) := ConcreteCategory.mono_of_injective _ Subtype.val_injective
  rw [cancel_mono] at h2
  rw [h2]

def smulPt (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) (s : SchemeHomOver Λ.σA O.g) : SchemeHomOver Λ.σA O.g :=
  ⟨Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ s.1, by rw [Category.assoc, s.2, specMap_decAut_comp_σA]⟩

theorem pts_smul_eq (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : σ ∈ A.decompositionSubgroup ℚ) {x : JH M H} {s : SchemeHomOver Λ.σA O.g} (hs : (O.pts x).1 = barPt A ≫ s.1) :
    (O.pts (σ • x)).1 = barPt A ≫ (smulPt O hσ s).1 := by
  show _ = barPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσ)) ≫ s.1
  rw [O.pts_galois, hs, ← Category.assoc, specMap_comp_barPt, Category.assoc]

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in
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

theorem exists_toricSection (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (χA : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    ∃ s : SchemeHomOver Λ.σA O.g,
      (O.pts (O.toricPoint m hm ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA))).1 = barPt A ≫ s.1 ∧
      (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s).1 =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χA.toRingHom)) ≫ (O.toricLift m hm).1 ≫
          pullback.fst O.g Λ.σA := by
  have hbase : Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ muStr ↥A O.toricRank m = 𝟙 _ := by
    rw [muStr, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have h : χA.toRingHom.comp (algebraMap ↥A (muCoord ↥A O.toricRank m)) = RingHom.id ↥A := by
      rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
    rw [h, CommRingCat.ofHom_id, Spec.map_id]
  refine ⟨⟨Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (O.toricLift m hm).1]
    have h2 : (O.toricLift m hm).1 ≫ pullback.snd O.g Λ.σA = muStr ↥A O.toricRank m := (O.toricLift m hm).2
    rw [h2, ← Category.assoc, hbase, Category.id_comp]
  · show (O.pts (O.pts.symm _)).1 = _
    rw [Equiv.apply_symm_apply]
    show ((Spec.map (CommRingCat.ofHom ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).toRingHom) ≫ (O.toricLift m hm).1) ≫
      pullback.fst O.g Λ.σA) = barPt A ≫ Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA
    have h3 : ((Algebra.ofId ↥A (AlgebraicClosure ℚ)).comp χA).toRingHom = (algebraMap ↥A (AlgebraicClosure ℚ)).comp χA.toRingHom := rfl
    rw [h3, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc]
    rfl
  · show resPt A ≫ Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA = _
    rw [resPt, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem ptsSp_symm_eq_nodeUnit_of_coe_eq (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (y : SchemeHomOver (resPt A ≫ Λ.σA) O.g) (wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (h : y.1 = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1) :
    O.ptsSp.symm y = GluedPic0.nodeUnit O.ssFinset wb := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext h

theorem residue_comp_decAut {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : A.IsFrobeniusAt σ p)
    (hσD : σ ∈ A.decompositionSubgroup ℚ) :
    (IsLocalRing.residue ↥A).comp (decAut σ hσD) = (frobenius (ResidueField ↥A) p).comp (IsLocalRing.residue ↥A) := by
  refine RingHom.ext fun a => ?_
  change IsLocalRing.residue ↥A ((⟨σ, hσD⟩ : ↥(A.decompositionSubgroup ℚ)) • a) = (IsLocalRing.residue ↥A a) ^ p
  rw [IsLocalRing.ResidueField.residue_smul]
  exact hσ.smul_residue_eq _

theorem coe_comp_smulPt (O : JHNeronObjectAtP p M H hpM A hA Λ) {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : A.IsFrobeniusAt σ p) (hσD : σ ∈ A.decompositionSubgroup ℚ) (s : SchemeHomOver Λ.σA O.g) :
    (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (smulPt O hσD s)).1 =
      Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s).1 := by
  change resPt A ≫ Spec.map (CommRingCat.ofHom (decAut σ hσD)) ≫ s.1 = Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)) ≫ resPt A ≫ s.1
  rw [resPt, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, residue_comp_decAut hσ hσD]

def translSec (O : JHNeronObjectAtP p M H hpM A hA Λ) (s : SchemeHomOver Λ.σA O.g) (U : SchemeHomOver O.g O.g) :
    SchemeHomOver Λ.σA O.g :=
  ⟨s.1 ≫ U.1, by rw [Category.assoc, U.2]; exact s.2⟩

theorem pts_transl (O : JHNeronObjectAtP p M H hpM A hA Λ) {x : JH M H} {s : SchemeHomOver Λ.σA O.g}
    (hs : (O.pts x).1 = barPt A ≫ s.1) (U : SchemeHomOver O.g O.g) :
    (O.pts (O.pts.symm (NeronModelInfra.schemeHomOverComp (O.pts x) U))).1 = barPt A ≫ (translSec O s U).1 := by
  rw [Equiv.apply_symm_apply]
  change (O.pts x).1 ≫ U.1 = barPt A ≫ s.1 ≫ U.1
  rw [hs, Category.assoc]

theorem coe_comp_translSec (O : JHNeronObjectAtP p M H hpM A hA Λ) (s : SchemeHomOver Λ.σA O.g) (U : SchemeHomOver O.g O.g) :
    (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ (translSec O s U)).1 =
      (NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s) U).1 := by
  change resPt A ≫ s.1 ≫ U.1 = (resPt A ≫ s.1) ≫ U.1
  rw [Category.assoc]

end A4Tor

section Pair

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

def Pair (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A) : Prop :=
  (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)).1 =
    (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre).1 ≫
      pullback.fst O.g (resPt A ≫ Λ.σA)

abbrev SP {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ O.G :=
  Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA

variable (h3ii : ∀ ψ ψ' : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
    NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre =
      NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ') O.torusFibre → ψ = ψ')

include h3ii in

theorem pair_fun {w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ}
    {ψ ψ' : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A}
    (h : Pair O w ψ) (h' : Pair O w ψ') : ψ = ψ' :=
  h3ii ψ ψ' (eq_of_coe_fst_eq _ _ (h.symm.trans h'))

theorem pair_U (S : Set ℕ) (M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
      O.torusFibre.1 ≫ (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))).1)
    (σN : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hUPtor : ∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w))
          (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
        GluedPic0.nodeUnit O.ssFinset (w ∘ σN))
    {w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ}
    {ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A} (h : Pair O w ψ) :
    Pair O (w ∘ σN) (ψ.comp (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) M₀)) := by
  have e1 : (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (w ∘ σN))).1 =
      (schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))).1 :=
    congrArg (fun z => (O.ptsSp z).1) (hUPtor w).symm |>.trans (congrArg Subtype.val (O.ptsSp.apply_symm_apply _))
  unfold Pair
  rw [e1, NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, torusPt_comp_mapDomain_coe, h,
    NeronModelInfra.schemeHomOverComp_coe]
  simp only [Category.assoc]
  rw [← NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst (resPt A ≫ Λ.σA) O.g O.g, ← Category.assoc O.torusFibre.1, ← hM₀,
    Category.assoc]

theorem pair_frob
    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hP₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius (ResidueField ↥A) p))) ≫ O.torusFibre.1 =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG)
    (σN : ↥O.ssFinset ≃ ↥O.ssFinset)
    (htor : ∀ (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
      (x : JH M H) (s s' : SchemeHomOver Λ.σA O.g)
      (hs : (O.pts x).1 = barPt A ≫ s.1) (hs' : (O.pts (φ • x)).1 = barPt A ≫ s'.1)
      (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
      (hw : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset w),
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s') = GluedPic0.nodeUnit O.ssFinset (fun t => p • w (σN.symm t)))
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
    (x : JH M H) (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts x).1 = barPt A ≫ s.1)
    (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (hw : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset w)
    (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A) (h : Pair O w ψ) :
    Pair O (fun t => p • w (σN.symm t))
      ((powChar (ResidueField ↥A) O.toricRank p ψ).comp (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) P₀)) := by
  have hs' := pts_smul_eq O hφD hs
  have hw' := htor φ hφ hφD x s (smulPt O hφD s) hs hs' w hw

  have e1 : (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (fun t => p • w (σN.symm t)))).1 =
      (schemeHomOverComp ⟨resPt A, rfl⟩ (smulPt O hφD s)).1 :=
    (congrArg (fun z => (O.ptsSp z).1) hw'.symm).trans (congrArg Subtype.val (O.ptsSp.apply_symm_apply _))
  have e0 : (schemeHomOverComp ⟨resPt A, rfl⟩ s).1 = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)).1 :=
    (congrArg (fun z => (O.ptsSp z).1) hw.symm).trans (congrArg Subtype.val (O.ptsSp.apply_symm_apply _)) |>.symm
  unfold Pair
  rw [e1, coe_comp_smulPt O hφ hφD s, e0, h, NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe,
    torusPt_comp_mapDomain_coe]

  rw [← Category.assoc, ← Category.assoc, specMap_frobenius_comp_torusPt]
  simp only [Category.assoc]
  rw [reassoc_of% hP₀, hΞ₁]

theorem pair_toric {m : ℕ} (hm : 0 < m)
    (h3i : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
      ∃ ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
        (∀ v : Fin O.toricRank → ℤ, ψ (AddMonoidAlgebra.single v 1) =
            IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1))) ∧
        SP O hm χ = (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre).1 ≫
            pullback.fst O.g (resPt A ≫ Λ.σA))
    (h4i : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A, ∃ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
        SP O hm χ = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    ∃ (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ) (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      (∀ v : Fin O.toricRank → ℤ, ψ (AddMonoidAlgebra.single v 1) =
          IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1))) ∧
      SP O hm χ = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)).1 ∧ Pair O w ψ := by
  obtain ⟨wb, hwb⟩ := h4i χ
  obtain ⟨ψ, hψv, hSP⟩ := h3i χ
  exact ⟨wb, ψ, hψv, hwb, hwb.symm.trans hSP⟩

theorem pair_pow {m : ℕ} (hm : 0 < m)
    (h3i : ∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A,
      ∃ ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A,
        (∀ v : Fin O.toricRank → ℤ, ψ (AddMonoidAlgebra.single v 1) =
            IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1))) ∧
        SP O hm χ = (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ) O.torusFibre).1 ≫
            pullback.fst O.g (resPt A ≫ Λ.σA))
    (h4ii : ∀ (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] ↥A)) (wb wb' : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        SP O hm χ.ofConv = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 →
        SP O hm χ'.ofConv = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb')).1 →
        SP O hm (χ * χ').ofConv = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (wb + wb'))).1)
    (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)
    (hψv : ∀ v : Fin O.toricRank → ℤ, ψ (AddMonoidAlgebra.single v 1) =
        IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1)))
    (hSP : SP O hm χ = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w)).1) (k : ℕ) (hk : 0 < k) :
    Pair O (fun t => k • w t) (powChar (ResidueField ↥A) O.toricRank k ψ) := by

  have hind : ∀ n : ℕ, SP O hm ((WithConv.toConv χ) ^ (n + 1)).ofConv =
      (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (fun t => (n + 1) • w t))).1 := by
    intro n
    induction n with
    | zero =>
      have e : (fun t => (0 + 1) • w t) = w := funext fun t => by rw [zero_add, one_nsmul]
      rw [zero_add, pow_one, e]
      exact hSP
    | succ n ih =>
      have e : (fun t => (n + 1 + 1) • w t) = (fun t => (n + 1) • w t) + w := funext fun t => by
        rw [Pi.add_apply, succ_nsmul]
      rw [pow_succ, e]
      exact h4ii _ _ _ _ ih hSP
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.sub_add_cancel hk).symm⟩

  obtain ⟨ψk, hψkv, hSPk⟩ := h3i ((WithConv.toConv χ) ^ (n + 1)).ofConv
  have hψk : ψk = powChar (ResidueField ↥A) O.toricRank (n + 1) ψ := by
    refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
    rw [hψkv, powChar_single, hψv, ← map_pow]
    exact congrArg _ (convPow_apply_single (WithConv.toConv χ) (n + 1) _)
  rw [← hψk]
  exact (hind n).symm.trans hSPk

end Pair

section Test

variable {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] {t : ℕ}

theorem exists_isPrimitiveRoot (ℓ : ℕ) [NeZero (ℓ : ResidueField ↥A)] : ∃ ζ : ResidueField ↥A, IsPrimitiveRoot ζ ℓ := by
  haveI : NeZero ℓ := ⟨fun h => NeZero.ne (ℓ : ResidueField ↥A) (by rw [h, Nat.cast_zero])⟩
  have hdeg : (Polynomial.cyclotomic ℓ (ResidueField ↥A)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos ℓ)).ne'
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
  exact ⟨ζ, (Polynomial.isRoot_cyclotomic_iff).mp hζ⟩

theorem pow_val_add {R : Type*} [Monoid R] {ℓ : ℕ} [NeZero ℓ] (a : R) (ha : a ^ ℓ = 1) (x y : ZMod ℓ) :
    a ^ (x + y).val = a ^ x.val * a ^ y.val := by
  rw [← pow_add, ZMod.val_add]
  conv_rhs => rw [← Nat.div_add_mod (x.val + y.val) ℓ, pow_add, pow_mul, ha, one_pow, one_mul]

def testChar (ℓ : ℕ) [NeZero ℓ] (ζA : ↥A) (hζA : ζA ^ ℓ = 1) (i : Fin t) : muCoord ↥A t ℓ →ₐ[↥A] ↥A :=
  AddMonoidAlgebra.lift ↥A ↥A (Fin t → ZMod ℓ)
    { toFun := fun g => ζA ^ ((Multiplicative.toAdd g) i).val
      map_one' := by
        change ζA ^ ((0 : Fin t → ZMod ℓ) i).val = 1
        rw [Pi.zero_apply, ZMod.val_zero, pow_zero]
      map_mul' := fun g h => by
        change ζA ^ ((Multiplicative.toAdd g + Multiplicative.toAdd h) i).val = ζA ^ ((Multiplicative.toAdd g) i).val * ζA ^ ((Multiplicative.toAdd h) i).val
        rw [Pi.add_apply, pow_val_add ζA hζA] }

theorem testChar_single (ℓ : ℕ) [NeZero ℓ] (ζA : ↥A) (hζA : ζA ^ ℓ = 1) (i : Fin t) (g : Fin t → ZMod ℓ) :
    testChar ℓ ζA hζA i (AddMonoidAlgebra.single g 1) = ζA ^ (g i).val := by
  rw [testChar, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem eq_id_of_forall_powChar_comp_eq (N : (Fin t → ℤ) →+ (Fin t → ℤ))
    (hN : ∀ (m : ℕ) (hm : 0 < m) (χ : muCoord ↥A t m →ₐ[↥A] ↥A)
      (ψ : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A),
      (∀ v : Fin t → ℤ, ψ (AddMonoidAlgebra.single v 1) =
          IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1))) →
      (powChar (ResidueField ↥A) t p ψ).comp (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) N) =
        powChar (ResidueField ↥A) t p ψ) :
    N = AddMonoidHom.id _ := by
  classical

  suffices key : ∀ j i : Fin t, N (Pi.single j 1) i = (Pi.single j 1 : Fin t → ℤ) i by
    refine AddMonoidHom.functions_ext _ _ _ fun j x => ?_
    have e : (Pi.single j x : Fin t → ℤ) = x • Pi.single j 1 := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [e, map_zsmul, AddMonoidHom.id_apply]
    exact congrArg (fun u => x • u) (funext (key j))
  intro j i
  set a := N (Pi.single j 1) i with ha
  set b := (Pi.single j 1 : Fin t → ℤ) i with hb

  obtain ⟨ℓ, hℓge, hℓ⟩ := Nat.exists_infinite_primes (max p (a - b).natAbs + 1)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓp : ℓ ≠ p := by omega
  have hℓab : (a - b).natAbs < ℓ := by omega
  haveI : NeZero (ℓ : ResidueField ↥A) := ⟨fun h => hℓp
    (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).mp ((CharP.cast_eq_zero_iff (ResidueField ↥A) p ℓ).mp h)).symm)⟩
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩

  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (A := A) ℓ
  obtain ⟨-, hlift⟩ := ValuationSubring.residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed
    (AlgebraicClosure ℚ) A ℓ (NeZero.ne _)
  obtain ⟨ζA, hζAℓ, hζA⟩ := hlift ζ hζ.pow_eq_one

  let χ := testChar ℓ ζA hζAℓ i
  let φv : Multiplicative (Fin t → ℤ) →* ResidueField ↥A :=
    { toFun := fun v => ζ ^ (((Multiplicative.toAdd v) i : ℤ) : ZMod ℓ).val
      map_one' := by
        change ζ ^ ((((0 : Fin t → ℤ) i : ℤ) : ZMod ℓ)).val = 1
        rw [Pi.zero_apply, Int.cast_zero, ZMod.val_zero, pow_zero]
      map_mul' := fun v v' => by
        change ζ ^ ((((Multiplicative.toAdd v + Multiplicative.toAdd v') i : ℤ) : ZMod ℓ)).val =
          ζ ^ ((((Multiplicative.toAdd v) i : ℤ) : ZMod ℓ)).val * ζ ^ ((((Multiplicative.toAdd v') i : ℤ) : ZMod ℓ)).val
        rw [Pi.add_apply, Int.cast_add, pow_val_add ζ hζ.pow_eq_one] }
  let ψ : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A :=
    AddMonoidAlgebra.lift _ _ _ φv
  have hψ : ∀ v : Fin t → ℤ, ψ (AddMonoidAlgebra.single v 1) = ζ ^ (((v i : ℤ) : ZMod ℓ)).val := fun v => by
    change AddMonoidAlgebra.lift _ _ _ φv (AddMonoidAlgebra.single v 1) = _
    rw [AddMonoidAlgebra.lift_single, one_smul]
    rfl
  have hψv : ∀ v : Fin t → ℤ, ψ (AddMonoidAlgebra.single v 1) =
      IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod ℓ)) 1)) := fun v => by
    rw [hψ, testChar_single, map_pow, hζA]

  have h := congrArg (fun F : torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A =>
    F (AddMonoidAlgebra.single (Pi.single j 1) 1)) (hN ℓ hℓ.pos χ ψ hψv)
  simp only [AlgHom.comp_apply, mapDomainAlgHom_single, powChar_single, hψ] at h

  rw [← pow_mul, ← pow_mul] at h
  obtain ⟨u, hu⟩ : ∃ u : (ResidueField ↥A)ˣ, (u : ResidueField ↥A) = ζ := ⟨(hζ.isUnit hℓ.ne_zero).unit, IsUnit.unit_spec _⟩
  have huℓ : IsPrimitiveRoot u ℓ := IsPrimitiveRoot.coe_units_iff.mp (by rw [hu]; exact hζ)
  have h' : u ^ (((a : ZMod ℓ)).val * p) = u ^ (((b : ZMod ℓ)).val * p) :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu]; exact h)
  rw [pow_eq_pow_iff_modEq, ← huℓ.eq_orderOf] at h'
  have hx : ((a : ZMod ℓ)).val ≡ ((b : ZMod ℓ)).val [MOD ℓ] :=
    Nat.ModEq.cancel_right_of_coprime
      (Nat.Coprime.symm ((Nat.coprime_primes (Fact.out : p.Prime) hℓ).mpr hℓp.symm)) h'
  have hab : (a : ZMod ℓ) = (b : ZMod ℓ) :=
    ZMod.val_injective ℓ (Nat.ModEq.eq_of_lt_of_lt hx (ZMod.val_lt _) (ZMod.val_lt _))
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hab
  have h0 : b - a = 0 := Int.eq_zero_of_abs_lt_dvd hab (by
    rw [← Int.natAbs_neg, neg_sub] at hℓab
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hℓab)
  omega

end Test

end TwistCancel

end

open TwistCancel in
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

    (S : Set ℕ)
    (M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
      O.torusFibre.1 ≫ (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))).1)

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
    P₀.comp M₀ = AddMonoidHom.id _ ∧ M₀.comp P₀ = AddMonoidHom.id _ := by
  classical

  have H3 := fun (m : ℕ) (hm : 0 < m) =>
    ModularCurve.JHNeronObjectAtP.exists_torusPt_residue_toricLift_and_torusFibre_injective p M H hpM A hA Λ O m hm
  have H4 := fun (m : ℕ) (hm : 0 < m) =>
    ModularCurve.JHNeronObjectAtP.exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one p M H hpM A hA Λ O m hm
  have h3ii := (H3 1 one_pos).2.1

  have hpermσ := fun t => nodeShift_fst_snd O σN hσN t
  have htor := hTOR σN hpermσ

  have main : ∀ (m : ℕ) (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A)
      (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A),
      (∀ v : Fin O.toricRank → ℤ, ψ (AddMonoidAlgebra.single v 1) =
          IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1))) →
      (powChar (ResidueField ↥A) O.toricRank p ψ).comp
          (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) (P₀.comp M₀)) =
        powChar (ResidueField ↥A) O.toricRank p ψ ∧
      (powChar (ResidueField ↥A) O.toricRank p ψ).comp
          (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) (M₀.comp P₀)) =
        powChar (ResidueField ↥A) O.toricRank p ψ := by
    intro m hm χ ψ₀ hψ₀v
    obtain ⟨h3i, -, -, -⟩ := H3 m hm
    obtain ⟨h4i, h4ii, -⟩ := H4 m hm

    obtain ⟨w, ψ, hψv, hSPw, hpair⟩ := pair_toric O hm h3i h4i χ
    have hψeq : ψ₀ = ψ := AddMonoidAlgebra.algHom_ext (fun v => by rw [hψ₀v, hψv]) (Subsingleton.elim _ _)
    subst hψeq
    obtain ⟨s, hs, hsp⟩ := exists_toricSection O m hm χ
    have hw : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset w :=
      ptsSp_symm_eq_nodeUnit_of_coe_eq O _ w (hsp.trans hSPw)
    have hpow := pair_pow O hm h3i h4ii χ w ψ₀ hψ₀v hSPw p (Fact.out : p.Prime).pos
    have hpU := fun {w' : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ}
      {ψ' : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A} (h' : Pair O w' ψ') =>
      pair_U O S M₀ hM₀ σN hUPtor h'

    have hA1 := pair_frob O ΞG hΞ₁ P₀ hP₀ σN htor φ hφ hφD _ s hs w hw ψ₀ hpair
    have hA2 := hpU hA1
    have eA : ((fun t => p • w (σN.symm t)) ∘ σN) = fun t => p • w t := funext fun t => by
      show p • w (σN.symm (σN t)) = p • w t
      rw [Equiv.symm_apply_apply]
    rw [eA] at hA2
    have EA := pair_fun O h3ii hA2 hpow

    have hB1 := hpU hpair
    have hsU := pts_transl O hs (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))
    have hwU : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ (translSec O s (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) =
        GluedPic0.nodeUnit O.ssFinset (w ∘ σN) := by
      refine ptsSp_symm_eq_nodeUnit_of_coe_eq O _ _ ?_
      rw [coe_comp_translSec]
      have e : schemeHomOverComp ⟨resPt A, rfl⟩ s = O.ptsSp (GluedPic0.nodeUnit O.ssFinset w) := O.ptsSp.symm_apply_eq.mp hw
      rw [e, ← hUPtor w, Equiv.apply_symm_apply]
    have hB2 := pair_frob O ΞG hΞ₁ P₀ hP₀ σN htor φ hφ hφD _ _ hsU (w ∘ σN) hwU _ hB1
    have eB : (fun t => p • (w ∘ σN) (σN.symm t)) = fun t => p • w t := funext fun t => by
      show p • w (σN (σN.symm t)) = p • w t
      rw [Equiv.apply_symm_apply]
    rw [eB, powChar_comp_mapDomain] at hB2
    have EB := pair_fun O h3ii hB2 hpow

    refine ⟨?_, ?_⟩
    · rw [← mapDomainAlgHom_comp, ← AlgHom.comp_assoc]
      exact EA
    · rw [← mapDomainAlgHom_comp, ← AlgHom.comp_assoc]
      exact EB
  exact ⟨eq_id_of_forall_powChar_comp_eq (P₀.comp M₀) fun m hm χ ψ hψv => (main m hm χ ψ hψv).1,
    eq_id_of_forall_powChar_comp_eq (M₀.comp P₀) fun m hm χ ψ hψv => (main m hm χ ψ hψv).2⟩

end S_ModularCurve_JHNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_hecke_U (solution)
