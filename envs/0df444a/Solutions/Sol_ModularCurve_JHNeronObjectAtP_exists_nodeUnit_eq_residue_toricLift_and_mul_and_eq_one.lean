-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/d009cbda-1678-544b-a572-73048f33a841

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

noncomputable section

namespace ToricReadH4

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

theorem conv_ext {c c' : WithConv (AddMonoidAlgebra S G →ₐ[S] L)}
    (h : ∀ v, c (AddMonoidAlgebra.single v 1) = c' (AddMonoidAlgebra.single v 1)) : c = c' := by
  have : c.ofConv = c'.ofConv := AddMonoidAlgebra.algHom_ext h (Subsingleton.elim _ _)
  exact congrArg WithConv.toConv this

end conv

section fibre

variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}

theorem toFibrePt_coe_fst (w : SchemeHomOver ι f) : (toFibrePt w).1 ≫ pullback.fst f ι = w.1 := by
  unfold toFibrePt
  rw [RelativeGroupLaw.baseChangePointOfBase_coe, pullback.lift_fst]
  rfl

theorem ofFibrePt_coe (z : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) :
    (ofFibrePt z).1 = z.1 ≫ pullback.fst f ι := rfl

theorem toFibrePt_eq_of (w : SchemeHomOver ι f) (z : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f))
    (h : z.1 ≫ pullback.fst f ι = w.1) : toFibrePt w = z := by
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [toFibrePt_coe_fst, h]
  · rw [(toFibrePt w).2, z.2]

theorem toFibrePt_ofFibrePt (z : SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f)) :
    toFibrePt (ofFibrePt z) = z :=
  toFibrePt_eq_of _ _ rfl

end fibre

section torusPts

variable (κ : Type) [Field κ] (t : ℕ)

theorem exists_eq_torusPt (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (torusStr κ t)) :
    ∃ ψ : torusCoord κ t →ₐ[κ] κ, y = torusPt κ t ψ := by
  have hy : Spec.map (Spec.preimage y.1) = y.1 := Spec.map_preimage y.1
  have hcomp : CommRingCat.ofHom (algebraMap κ (torusCoord κ t)) ≫ Spec.preimage y.1 = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_id, hy]
    exact y.2
  let ψ : torusCoord κ t →ₐ[κ] κ :=
    { (Spec.preimage y.1).hom with
      commutes' := fun c => by
        have := congrArg (fun g => (CommRingCat.Hom.hom g) c) hcomp
        simpa using this }
  refine ⟨ψ, Subtype.ext ?_⟩
  change y.1 = Spec.map (CommRingCat.ofHom ψ.toRingHom)
  rw [← hy]
  rfl

theorem torusPt_injective_of_mono {X : Scheme.{0}} {g : X ⟶ Spec (CommRingCat.of κ)}
    (T : SchemeHomOver (torusStr κ t) g) [Mono T.1] (ψ ψ' : torusCoord κ t →ₐ[κ] κ)
    (h : NeronModelInfra.schemeHomOverComp (torusPt κ t ψ) T =
      NeronModelInfra.schemeHomOverComp (torusPt κ t ψ') T) : ψ = ψ' := by
  have h2 := congrArg Subtype.val h
  rw [NeronModelInfra.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe] at h2
  have h3 : (torusPt κ t ψ).1 = (torusPt κ t ψ').1 := (cancel_mono T.1).mp h2
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) = Spec.map (CommRingCat.ofHom ψ'.toRingHom) at h3
  exact AlgHom.coe_ringHom_injective (congrArg CommRingCat.Hom.hom (Spec.map_injective h3))

end torusPts

section chars

variable (A : ValuationSubring (AlgebraicClosure ℚ)) (t m : ℕ)

abbrev proj : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem proj_apply (v : Fin t → ℤ) : proj t m v = fun i => (v i : ZMod m) := rfl

variable {t m}

def charRed (χ : muCoord ↥A t m →ₐ[↥A] ↥A) : Multiplicative (Fin t → ZMod m) →* ResidueField ↥A :=
  ((residue ↥A).toMonoidHom.comp (χ : muCoord ↥A t m →* ↥A)).comp (AddMonoidAlgebra.of ↥A (Fin t → ZMod m))

theorem charRed_apply (χ : muCoord ↥A t m →ₐ[↥A] ↥A) (v : Fin t → ZMod m) :
    charRed A χ (Multiplicative.ofAdd v) = residue ↥A (χ (AddMonoidAlgebra.single v 1)) := by
  simp [charRed, AddMonoidAlgebra.of_apply]

def chiRes (χ : muCoord ↥A t m →ₐ[↥A] ↥A) :
    muCoord (ResidueField ↥A) t m →ₐ[ResidueField ↥A] ResidueField ↥A :=
  AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) (Fin t → ZMod m) (charRed A χ)

theorem chiRes_single (χ : muCoord ↥A t m →ₐ[↥A] ↥A) (v : Fin t → ZMod m) (b : ResidueField ↥A) :
    chiRes A χ (AddMonoidAlgebra.single v b) = b * residue ↥A (χ (AddMonoidAlgebra.single v 1)) := by
  rw [chiRes, AddMonoidAlgebra.lift_single, charRed_apply, smul_eq_mul]

theorem chiRes_comp_mapRingHom (χ : muCoord ↥A t m →ₐ[↥A] ↥A) :
    (chiRes A χ).toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin t → ZMod m) (residue ↥A)) =
      (residue ↥A).comp χ.toRingHom := by
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) (fun v => ?_)
  · rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, chiRes_single]
    have h1 : χ (AddMonoidAlgebra.single 0 b) = b := by
      have : AddMonoidAlgebra.single (0 : Fin t → ZMod m) b = algebraMap ↥A (muCoord ↥A t m) b := by
        rw [AddMonoidAlgebra.coe_algebraMap]; rfl
      rw [this, AlgHom.commutes]; rfl
    have h0 : χ (AddMonoidAlgebra.single 0 1) = 1 := by
      rw [← AddMonoidAlgebra.one_def, map_one]
    rw [h0, map_one, mul_one, h1]
  · rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, map_one, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, chiRes_single, one_mul]

def psiOf (χ : muCoord ↥A t m →ₐ[↥A] ↥A) :
    torusCoord (ResidueField ↥A) t →ₐ[ResidueField ↥A] ResidueField ↥A :=
  (chiRes A χ).comp (AddMonoidAlgebra.mapDomainAlgHom (ResidueField ↥A) (ResidueField ↥A) (proj t m))

theorem psiOf_single (χ : muCoord ↥A t m →ₐ[↥A] ↥A) (v : Fin t → ℤ) :
    psiOf A χ (AddMonoidAlgebra.single v 1) =
      residue ↥A (χ (AddMonoidAlgebra.single (fun i => (v i : ZMod m)) 1)) := by
  rw [psiOf, AlgHom.comp_apply]
  change chiRes A χ (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (proj t m) (AddMonoidAlgebra.single v 1)) = _
  rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, chiRes_single, one_mul]
  rfl

theorem psiOf_toRingHom (χ : muCoord ↥A t m →ₐ[↥A] ↥A) :
    (psiOf A χ).toRingHom =
      (chiRes A χ).toRingHom.comp (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (proj t m)) := rfl

end chars

section neron

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

theorem residue_toricLift_eq {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
        pullback.fst O.g Λ.σA =
      (NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank (psiOf A χ)) O.torusFibre).1 ≫
        pullback.fst O.g (resPt A ≫ Λ.σA) := by
  have hs : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (residue ↥A))) ≫
      (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (proj O.toricRank m))) ≫
        O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) :=
    O.toricLift_special m hm
  rw [← chiRes_comp_mapRingHom A χ, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hs,
    NeronModelInfra.schemeHomOverComp_coe, Category.assoc]
  change _ = Spec.map (CommRingCat.ofHom (psiOf A χ).toRingHom) ≫ _
  rw [psiOf_toRingHom, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

theorem torusFibre_one :
    NeronModelInfra.schemeHomOverComp
        (torusPt (ResidueField ↥A) O.toricRank
          (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)).ofConv)
        O.torusFibre = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
  have h := O.torusFibre_mul 1 1
  rw [mul_one] at h
  letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup
    (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  exact mul_eq_right.mp h.symm

end neron

section reading

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

abbrev zOf {m : ℕ} (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank (psiOf A χ)) O.torusFibre

theorem exists_nodeUnit {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) :
    ∃ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
          pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 := by
  have hx : O.ptsSp.symm (ofFibrePt (zOf O χ)) ∈ (GluedPic0.nodeUnit O.ssFinset).range := by
    rw [← O.torus_ptsSp]
    refine ⟨torusPt (ResidueField ↥A) O.toricRank (psiOf A χ), ?_⟩
    rw [Equiv.apply_symm_apply, toFibrePt_ofFibrePt]
  obtain ⟨wb, hwb⟩ := hx
  refine ⟨wb, ?_⟩
  rw [residue_toricLift_eq O hm χ, hwb, Equiv.apply_symm_apply, ofFibrePt_coe]

theorem toFibrePt_ptsSp_eq {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A)
    (x : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset)
    (h : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
          pullback.fst O.g Λ.σA = (O.ptsSp x).1) :
    toFibrePt (O.ptsSp x) = zOf O χ := by
  refine toFibrePt_eq_of _ _ ?_
  rw [← h, residue_toricLift_eq O hm χ]

theorem psiOf_convMul {m : ℕ} (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] ↥A)) :
    psiOf A (χ * χ').ofConv = (WithConv.toConv (psiOf A χ.ofConv) * WithConv.toConv (psiOf A χ'.ofConv)).ofConv := by
  refine AddMonoidAlgebra.algHom_ext (fun v => ?_) (Subsingleton.elim _ _)
  rw [psiOf_single]
  change residue ↥A ((χ * χ') (AddMonoidAlgebra.single _ 1)) =
    (WithConv.toConv (psiOf A χ.ofConv) * WithConv.toConv (psiOf A χ'.ofConv)) (AddMonoidAlgebra.single v 1)
  rw [convMul_apply_single, convMul_apply_single, map_mul]
  change _ = psiOf A χ.ofConv (AddMonoidAlgebra.single v 1) * psiOf A χ'.ofConv (AddMonoidAlgebra.single v 1)
  rw [psiOf_single, psiOf_single]

theorem reading_mul {m : ℕ} (hm : 0 < m) (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] ↥A))
    (wb wb' : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (h : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
          pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1)
    (h' : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ'.ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
          pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb')).1) :
    Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (χ * χ').ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
        pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (wb + wb'))).1 := by
  have hz := toFibrePt_ptsSp_eq O hm χ.ofConv _ h
  have hz' := toFibrePt_ptsSp_eq O hm χ'.ofConv _ h'
  have hmul := O.torusFibre_mul (WithConv.toConv (psiOf A χ.ofConv)) (WithConv.toConv (psiOf A χ'.ofConv))
  rw [map_add, O.ptsSp_add, hz, hz', residue_toricLift_eq O hm, psiOf_convMul, ofFibrePt_coe, hmul]

theorem map_zero_of_map_add {Gp : Type*} [AddGroup Gp] {Pt : Type*} [Group Pt] (F : Gp → Pt)
    (hF : ∀ x y, F (x + y) = F x * F y) : F 0 = 1 := by
  have h := hF 0 0
  rw [add_zero] at h
  exact mul_eq_right.mp h.symm

theorem toFibrePt_ptsSp_zero :
    toFibrePt (O.ptsSp 0) = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
  letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup
    (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
  refine map_zero_of_map_add (fun x => toFibrePt (O.ptsSp x)) (fun x y => ?_)
  change toFibrePt (O.ptsSp (x + y)) = (O.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (O.ptsSp x))
    (toFibrePt (O.ptsSp y))
  rw [O.ptsSp_add, toFibrePt_ofFibrePt]

theorem residue_eq_one_of_nodeUnit_eq_zero {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A)
    (wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
    (h : Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
          pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1)
    (h0 : GluedPic0.nodeUnit O.ssFinset wb = 0) (v : Fin O.toricRank → ZMod m) :
    IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single v 1)) = 1 := by
  haveI : IsClosedImmersion O.torusFibre.1 := O.torusFibre_isClosedImmersion
  have hz := toFibrePt_ptsSp_eq O hm χ _ h
  rw [h0, toFibrePt_ptsSp_zero, ← torusFibre_one O] at hz

  have hψ : psiOf A χ = (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A]
      ResidueField ↥A)).ofConv :=
    torusPt_injective_of_mono (ResidueField ↥A) O.toricRank O.torusFibre _ _ hz.symm

  have hv : (fun i => (((v i).cast : ℤ) : ZMod m)) = v := funext fun i => ZMod.intCast_zmod_cast (v i)
  have := psiOf_single A χ (fun i => ((v i).cast : ℤ))
  rw [hv, hψ] at this
  rw [← this]
  exact convOne_apply_single _

end reading

end ToricReadH4

end

open ToricReadH4 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) :

    (∀ χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A, ∃ wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1) ∧

    (∀ (χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] ↥A)) (wb wb' : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 →
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ'.ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb')).1 →
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp (χ * χ').ofConv.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA =
          (O.ptsSp (GluedPic0.nodeUnit O.ssFinset (wb + wb'))).1) ∧

    (∀ (χ : muCoord ↥A O.toricRank m →ₐ[↥A] ↥A) (wb : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ),
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp χ.toRingHom)) ≫ (O.toricLift m hm).1 ≫
            pullback.fst O.g Λ.σA = (O.ptsSp (GluedPic0.nodeUnit O.ssFinset wb)).1 →
        GluedPic0.nodeUnit O.ssFinset wb = 0 →
        ∀ v : Fin O.toricRank → ZMod m, IsLocalRing.residue ↥A (χ (AddMonoidAlgebra.single v 1)) = 1) := by
  exact ⟨exists_nodeUnit O hm, fun χ χ' wb wb' h h' => reading_mul O hm χ χ' wb wb' h h',
    fun χ wb h h0 v => residue_eq_one_of_nodeUnit_eq_zero O hm χ wb h h0 v⟩

end S_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_nodeUnit_eq_residue_toricLift_and_mul_and_eq_one (solution)
