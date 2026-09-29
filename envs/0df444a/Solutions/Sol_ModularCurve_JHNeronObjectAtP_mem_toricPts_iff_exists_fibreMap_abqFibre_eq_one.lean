-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/04b53c22-62bc-5245-8ac0-31f4f3353efc

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPts_le_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one
p2m_attr_erase "simp" "GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP GoodReductionJacobian NeronModelInfra IsLocalRing

open scoped MatrixGroups

namespace MemToric

open ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

variable {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem mem_of_pow_eq_one {m : ℕ} (hm : 0 < m) {ζ : AlgebraicClosure ℚ} (h : ζ ^ m = 1) : ζ ∈ A := by
  apply A.mem_of_valuation_le_one
  have hv : A.valuation ζ ^ m = 1 := by rw [← map_pow, h, map_one]
  exact ((pow_eq_one_iff.mp hv).resolve_right hm.ne').le

theorem apply_mem {t m : ℕ} (hm : 0 < m) (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) (a : muCoord ↥A t m) :
    χ a ∈ A := by
  classical
  induction a using AddMonoidAlgebra.induction_on with
  | of v =>
    refine mem_of_pow_eq_one hm ?_
    rw [← map_pow, AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_pow, one_pow]
    have : m • (Multiplicative.toAdd (Multiplicative.ofAdd v)) = 0 := by ext i; simp
    rw [this]
    exact map_one χ
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | smul r a ha => rw [map_smul, Algebra.smul_def]; exact mul_mem (by simp) ha

noncomputable def charA {t m : ℕ} (hm : 0 < m) (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    muCoord ↥A t m →ₐ[↥A] ↥A where
  toFun a := ⟨χ a, apply_mem hm χ a⟩
  map_one' := Subtype.ext (map_one χ)
  map_mul' a b := Subtype.ext (map_mul χ a b)
  map_zero' := Subtype.ext (map_zero χ)
  map_add' a b := Subtype.ext (map_add χ a b)
  commutes' r := Subtype.ext (χ.commutes r)

@[scoped simp] theorem subtype_comp_charA {t m : ℕ} (hm : 0 < m) (χ : muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ) :
    A.subtype.comp (charA hm χ).toRingHom = χ.toRingHom := rfl

section APoint

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)
  {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)

noncomputable def muPtA : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥A))) (muStr ↥A O.toricRank m) :=
  ⟨Spec.map (CommRingCat.ofHom (charA hm χ).toRingHom), by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id, ← CommRingCat.ofHom_id]
    congr 2
    exact (charA hm χ).comp_algebraMap⟩

theorem barPt_comp_muPtA : barPt A ≫ (muPtA O hm χ).1 = (muPt A O.toricRank m χ).1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rfl

noncomputable def sChar : SchemeHomOver Λ.σA O.g :=
  ⟨(muPtA O hm χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA, by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc ((O.toricLift m hm).1), (O.toricLift m hm).2,
      ← Category.assoc, (muPtA O hm χ).2, Category.id_comp]⟩

theorem pts_toricPoint_eq : (O.pts (O.toricPoint m hm χ)).1 = barPt A ≫ (sChar O hm χ).1 := by
  rw [JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply]
  change ((muPt A O.toricRank m χ).1 ≫ (O.toricLift m hm).1) ≫ pullback.fst O.g Λ.σA = barPt A ≫ (muPtA O hm χ).1 ≫ _
  rw [← barPt_comp_muPtA O hm χ]
  simp only [Category.assoc]

theorem extendsToPlace_toricPoint : ExtendsToPlace A Λ.σA (O.pts (O.toricPoint m hm χ)) :=
  ⟨sChar O hm χ, pts_toricPoint_eq O hm χ⟩

end APoint

section FibreRead

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

theorem one_coe_id_comp {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : GoodReductionJacobian.RelativeGroupLaw R f) (ι : T ⟶ Spec (CommRingCat.of R)) :
    (L.one (𝟙 T ≫ ι)).1 = (L.one ι).1 := by
  have := L.one_natural ι (𝟙 T ≫ ι) (𝟙 T) rfl
  rw [← this, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

theorem fibreMap_eq_one_iff {ι : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Spec (CommRingCat.of (baseRing p))}
    (φ : SchemeHomOver (GoodReductionJacobian.RelativeGroupLaw.baseChangeStr ι O.g)
      (GoodReductionJacobian.RelativeGroupLaw.baseChangeStr ι Λ.f))
    (x : SchemeHomOver ι O.g) :
    fibreMap φ x = Λ.L.one ι ↔
      NeronModelInfra.schemeHomOverComp (toFibrePt x) φ = (Λ.L.baseChange ι).one (𝟙 _) := by
  set z := NeronModelInfra.schemeHomOverComp (toFibrePt x) φ with hz
  have hz2 : z.1 ≫ pullback.snd Λ.f ι = 𝟙 _ := z.2
  constructor
  · intro h
    have h1 : (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase ι z).1 = (Λ.L.one ι).1 := congrArg Subtype.val h
    rw [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe] at h1
    apply Subtype.ext
    rw [GoodReductionJacobian.RelativeGroupLaw.baseChange_one, GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, h1, one_coe_id_comp]
    · rw [pullback.lift_snd, hz2]
  · intro h
    apply Subtype.ext
    change (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase ι z).1 = (Λ.L.one ι).1
    rw [h, GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_one, one_coe_id_comp]

end FibreRead

section Reduction

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)
  {m : ℕ} (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)

noncomputable def charK : muCoord (ResidueField ↥A) O.toricRank m →ₐ[ResidueField ↥A] ResidueField ↥A :=
  AddMonoidAlgebra.lift (ResidueField ↥A) (ResidueField ↥A) (Fin O.toricRank → ZMod m)
    ((residue ↥A).toMonoidHom.comp (((charA hm χ) : muCoord ↥A O.toricRank m →* ↥A).comp
      (AddMonoidAlgebra.of ↥A (Fin O.toricRank → ZMod m))))

theorem charK_single (v : Fin O.toricRank → ZMod m) (s : ResidueField ↥A) :
    charK O hm χ (AddMonoidAlgebra.single v s) = s * residue ↥A (charA hm χ (AddMonoidAlgebra.single v 1)) := by
  rw [charK, AddMonoidAlgebra.lift_single]
  rfl

theorem charK_comp_mapRingHom :
    (charK O hm χ).toRingHom.comp (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ZMod m) (residue ↥A)) =
      (residue ↥A).comp (charA hm χ).toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, charK_single, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    have h1 : AddMonoidAlgebra.single (0 : Fin O.toricRank → ZMod m) (1 : ↥A) = 1 := rfl
    have hb : AddMonoidAlgebra.single (0 : Fin O.toricRank → ZMod m) b = algebraMap ↥A _ b := rfl
    rw [h1, map_one, map_one, mul_one, hb, AlgHom.commutes]
    rfl
  · intro v
    rw [RingHom.comp_apply, RingHom.comp_apply, AddMonoidAlgebra.mapRingHom_single, map_one, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, charK_single, one_mul]
    rfl

theorem specMap_charK_comp_muBaseChange :
    Spec.map (CommRingCat.ofHom (charK O hm χ).toRingHom) ≫ muBaseChange (residue ↥A) O.toricRank m =
      resPt A ≫ (muPtA O hm χ).1 := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, charK_comp_mapRingHom]

noncomputable def torusPtK : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (torusStr (ResidueField ↥A) O.toricRank) :=
  ⟨Spec.map (CommRingCat.ofHom (charK O hm χ).toRingHom) ≫ muToTorus (ResidueField ↥A) O.toricRank m, by
    rw [Category.assoc]
    change Spec.map _ ≫ Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id,
      ← CommRingCat.ofHom_id]
    congr 2
    apply RingHom.ext
    intro a
    change (charK O hm χ) (AddMonoidAlgebra.mapDomainRingHom _ _ (algebraMap (ResidueField ↥A) _ a)) = a
    have : AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A)
        (AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin O.toricRank => ℤ) i))
        (algebraMap (ResidueField ↥A) _ a) = algebraMap (ResidueField ↥A) _ a := by
      change AddMonoidAlgebra.mapDomainRingHom _ _ (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a
      rw [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero]
    rw [this, AlgHom.commutes]
    rfl⟩

theorem torusPtK_comp_torusFibre :
    NeronModelInfra.schemeHomOverComp (torusPtK O hm χ) O.torusFibre =
      toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (sChar O hm χ)) := by
  apply Subtype.ext
  rw [NeronModelInfra.schemeHomOverComp_coe]
  change _ = pullback.lift (resPt A ≫ (sChar O hm χ).1) (𝟙 _) _
  apply pullback.hom_ext
  · rw [pullback.lift_fst, Category.assoc]
    change (Spec.map (CommRingCat.ofHom (charK O hm χ).toRingHom) ≫ muToTorus (ResidueField ↥A) O.toricRank m) ≫
        O.torusFibre.1 ≫ pullback.fst O.g (resPt A ≫ Λ.σA) =
      resPt A ≫ (muPtA O hm χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA
    rw [Category.assoc, ← O.toricLift_special m hm, ← Category.assoc, specMap_charK_comp_muBaseChange, Category.assoc]
  · rw [pullback.lift_snd, Category.assoc, O.torusFibre.2]
    exact (torusPtK O hm χ).2

theorem fibreMap_abqFibre_sChar (i : Fin 2) :
    fibreMap (O.abqFibre i) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (sChar O hm χ)) = Λ.L.one (resPt A ≫ Λ.σA) := by
  rw [fibreMap_eq_one_iff]
  exact (O.abqFibre_eq_one_iff (𝟙 _) _).mpr ⟨torusPtK O hm χ, torusPtK_comp_torusFibre O hm χ⟩ i

end Reduction

section Generic

variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)}
  (G : GoodReductionJacobian.RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x) =
      G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  exact inv_eq_of_mul_eq_one_left h |>.symm

theorem toFibrePt_one {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} :
    toFibrePt (G.one ι) = (G.baseChange ι).one (𝟙 _) := by
  rw [GoodReductionJacobian.RelativeGroupLaw.baseChange_one]
  change GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId (G.one ι)) = _
  congr 1

theorem overId_eq_comp {T : Scheme.{0}} {ι : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver ι f) :
    overId x = GoodReductionJacobian.schemeHomOverComp (𝟙 T) rfl x := by
  apply Subtype.ext
  change x.1 = 𝟙 T ≫ x.1
  rw [Category.id_comp]

theorem toFibrePt_mul {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (a b : SchemeHomOver ι f) :
    toFibrePt (G.mul ι a b) = (G.baseChange ι).mul (𝟙 _) (toFibrePt a) (toFibrePt b) := by
  rw [GoodReductionJacobian.RelativeGroupLaw.baseChange_mul]
  change GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId (G.mul ι a b)) = _
  congr 1
  change overId (G.mul ι a b) =
    G.mul _ (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase ι
      (GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId a)))
      (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase ι
      (GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId b)))
  rw [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase,
    GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, overId_eq_comp, overId_eq_comp, overId_eq_comp,
    G.mul_natural]

theorem toFibrePt_inv {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} (a : SchemeHomOver ι f) :
    toFibrePt (G.inv ι a) = (G.baseChange ι).inv (𝟙 _) (toFibrePt a) := by
  rw [GoodReductionJacobian.RelativeGroupLaw.baseChange_inv]
  change GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId (G.inv ι a)) = _
  congr 1
  change overId (G.inv ι a) = G.inv _ (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase ι
      (GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId a)))
  rw [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase, overId_eq_comp, overId_eq_comp, inv_natural]

end Generic

section Hom

variable {R : Type} [CommRing R] {X Y T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of R)}
  (GX : GoodReductionJacobian.RelativeGroupLaw R f) (GY : GoodReductionJacobian.RelativeGroupLaw R g)
  (φ : SchemeHomOver f g) (t : T ⟶ Spec (CommRingCat.of R))
  (hφ : ∀ x y : SchemeHomOver t f,
    NeronModelInfra.schemeHomOverComp (GX.mul t x y) φ =
      GY.mul t (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))

include hφ

theorem comp_one_eq_one : NeronModelInfra.schemeHomOverComp (GX.one t) φ = GY.one t := by
  letI := GY.pointGroup t
  have h := hφ (GX.one t) (GX.one t)
  rw [GX.one_mul] at h

  have h' : (NeronModelInfra.schemeHomOverComp (GX.one t) φ : SchemeHomOver t g) =
      (NeronModelInfra.schemeHomOverComp (GX.one t) φ) * (NeronModelInfra.schemeHomOverComp (GX.one t) φ) := h
  exact left_eq_mul.mp h'

end Hom

section Forward

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

def Good (x : JH M H) : Prop :=
  ∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
    ∀ i : Fin 2, fibreMap (O.abqFibre i) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) =
      Λ.L.one (resPt A ≫ Λ.σA)

theorem good_iff (x : JH M H) : Good O x ↔
    ∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
      ∀ i : Fin 2, NeronModelInfra.schemeHomOverComp
        (toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) (O.abqFibre i) =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
  simp only [Good, fibreMap_eq_one_iff]

theorem pts_zero : O.pts 0 = O.L.one (genPt p) := by
  letI := O.L.pointGroup (genPt p)
  have h := O.pts_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem pts_neg (x : JH M H) : O.pts (-x) = O.L.inv (genPt p) (O.pts x) := by
  letI := O.L.pointGroup (genPt p)
  have h := O.pts_add (-x) x
  rw [neg_add_cancel, pts_zero] at h
  exact (inv_eq_of_mul_eq_one_left h.symm).symm

theorem red_mul (a b : SchemeHomOver Λ.σA O.g) :
    GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (O.L.mul Λ.σA a b) =
      O.L.mul (resPt A ≫ Λ.σA) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl a)
        (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl b) :=
  O.L.mul_natural _ _ _ _ a b

theorem good_zero : Good O 0 := by
  refine (good_iff O 0).mpr ⟨O.L.one Λ.σA, ?_, ?_⟩
  · rw [pts_zero, ← O.L.one_natural Λ.σA (genPt p) (barPt A) Λ.hσA, GoodReductionJacobian.schemeHomOverComp_coe]
  · intro i
    rw [O.L.one_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl, toFibrePt_one]
    exact comp_one_eq_one (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) (O.abqFibre i) (𝟙 _)
      (O.abqFibre_mul i (𝟙 _))

theorem good_add {x y : JH M H} (hx : Good O x) (hy : Good O y) : Good O (x + y) := by
  rw [good_iff] at hx hy ⊢
  obtain ⟨s, hs, hs'⟩ := hx
  obtain ⟨s', hs2, hs2'⟩ := hy
  refine ⟨O.L.mul Λ.σA s s', ?_, ?_⟩
  · rw [O.pts_add]
    have e1 : O.pts x = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s := Subtype.ext hs
    have e2 : O.pts y = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s' := Subtype.ext hs2
    rw [e1, e2, ← O.L.mul_natural, GoodReductionJacobian.schemeHomOverComp_coe]
  · intro i
    rw [red_mul, toFibrePt_mul, O.abqFibre_mul i (𝟙 _), hs' i, hs2' i]
    letI := (Λ.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
    exact mul_one _

theorem good_neg {x : JH M H} (hx : Good O x) : Good O (-x) := by
  rw [good_iff] at hx ⊢
  obtain ⟨s, hs, hs'⟩ := hx
  refine ⟨O.L.inv Λ.σA s, ?_, ?_⟩
  · rw [pts_neg]
    have e1 : O.pts x = GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s := Subtype.ext hs
    rw [e1, ← inv_natural, GoodReductionJacobian.schemeHomOverComp_coe]
  · intro i
    rw [inv_natural, toFibrePt_inv]
    letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
    letI := (Λ.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)

    set φ := O.abqFibre i
    set z := toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) with hz
    have hmul := O.abqFibre_mul i (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))
    have h1 : NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)) φ =
        (Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) :=
      comp_one_eq_one (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) φ (𝟙 _) hmul
    have h2 := hmul ((O.L.baseChange (resPt A ≫ Λ.σA)).inv (𝟙 _) z) z
    rw [(O.L.baseChange (resPt A ≫ Λ.σA)).inv_mul_cancel, h1, hs' i] at h2

    change _ = (1 : SchemeHomOver (𝟙 _) (GoodReductionJacobian.RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f))
    have h3 : (1 : SchemeHomOver (𝟙 _) (GoodReductionJacobian.RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) Λ.f)) =
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange (resPt A ≫ Λ.σA)).inv (𝟙 _) z) φ * 1 := h2
    rw [mul_one] at h3
    exact h3.symm

theorem good_of_mem_toricPts {m : ℕ} (hm : 0 < m) {x : JH M H} (hx : x ∈ O.toricPts m) : Good O x := by
  rw [JHNeronObjectAtP.toricPts, dif_pos hm] at hx
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨χ, rfl⟩ := hy
    exact ⟨sChar O hm χ, pts_toricPoint_eq O hm χ, fibreMap_abqFibre_sChar O hm χ⟩
  | zero => exact good_zero O
  | add a b _ _ ha hb => exact good_add O ha hb
  | neg a _ ha => exact good_neg O ha

end Forward

section Torus

variable (κ : Type) [Field κ] (t : ℕ)

theorem exists_torusPt_eq (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of κ))) (torusStr κ t)) :
    ∃ ψ : torusCoord κ t →ₐ[κ] κ, torusPt κ t ψ = y := by
  let φ := Spec.preimage y.1
  have hφ : CommRingCat.ofHom (algebraMap κ (torusCoord κ t)) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id]
    exact y.2
  let ψ : torusCoord κ t →ₐ[κ] κ :=
    { φ.hom with
      commutes' := fun a => by
        have := congrArg (fun f : CommRingCat.of κ ⟶ CommRingCat.of κ => f.hom a) hφ
        simpa using this }
  refine ⟨ψ, Subtype.ext ?_⟩
  change Spec.map (CommRingCat.ofHom ψ.toRingHom) = y.1
  have : CommRingCat.ofHom ψ.toRingHom = φ := CommRingCat.hom_ext (RingHom.ext fun a => rfl)
  rw [this, Spec.map_preimage]

theorem torusPt_injective : Function.Injective (torusPt κ t) := by
  intro ψ ψ' h
  have h1 : Spec.map (CommRingCat.ofHom ψ.toRingHom) = Spec.map (CommRingCat.ofHom ψ'.toRingHom) := congrArg Subtype.val h
  have h2 := Spec.map_injective h1
  apply AlgHom.ext
  intro a
  exact congrArg (fun f : CommRingCat.of (torusCoord κ t) ⟶ CommRingCat.of κ => f.hom a) h2

theorem convPow_apply_single (ψ : WithConv (torusCoord κ t →ₐ[κ] κ)) (v : Fin t → ℤ) (n : ℕ) :
    (ψ ^ n).ofConv (AddMonoidAlgebra.single v 1) = (ψ.ofConv (AddMonoidAlgebra.single v 1)) ^ n := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    change (1 : WithConv (torusCoord κ t →ₐ[κ] κ)) (AddMonoidAlgebra.single v 1) = 1
    rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single]
    simp
  | succ n ih =>
    rw [pow_succ, pow_succ, ← ih]
    change (ψ ^ n * ψ) (AddMonoidAlgebra.single v 1) = _
    rw [AlgHom.convMul_apply, AddMonoidAlgebra.comul_single]
    simp [Algebra.TensorProduct.lift_tmul]

end Torus

section SpecialFibre

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

noncomputable def w (ψ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    SchemeHomOver (𝟙 _) (GoodReductionJacobian.RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  NeronModelInfra.schemeHomOverComp (torusPt (ResidueField ↥A) O.toricRank ψ.ofConv) O.torusFibre

theorem w_mul (ψ ψ' : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) :
    w O (ψ * ψ') = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _) (w O ψ) (w O ψ') :=
  O.torusFibre_mul ψ ψ'

theorem w_one : w O 1 = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
  letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
  have h := w_mul O 1 1
  rw [one_mul] at h
  exact left_eq_mul.mp h

theorem w_pow (ψ : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)) (n : ℕ) :
    letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
    w O (ψ ^ n) = (w O ψ) ^ n := by
  letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact w_one O
  | succ n ih => rw [pow_succ, pow_succ, w_mul, ih]; rfl

theorem w_injective : Function.Injective (w O) := by
  intro ψ ψ' h
  have h1 : (torusPt (ResidueField ↥A) O.toricRank ψ.ofConv).1 ≫ O.torusFibre.1 =
      (torusPt (ResidueField ↥A) O.toricRank ψ'.ofConv).1 ≫ O.torusFibre.1 := congrArg Subtype.val h
  haveI := O.torusFibre_isClosedImmersion
  rw [cancel_mono] at h1
  exact WithConv.ofConv_injective (torusPt_injective _ _ (Subtype.ext h1))

theorem ofFibrePt_toFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver ι f) : ofFibrePt (toFibrePt x) = x := by
  apply Subtype.ext
  change (GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase ι
    (GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId x))).1 = x.1
  rw [GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase]
  rfl

theorem toFibrePt_ofFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (y : SchemeHomOver (𝟙 _) (GoodReductionJacobian.RelativeGroupLaw.baseChangeStr ι f)) : toFibrePt (ofFibrePt y) = y := by
  change GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase ι (overId (ofFibrePt y)) = y
  have : overId (ofFibrePt y) = GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase ι y := Subtype.ext rfl
  rw [this, GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase]

noncomputable def u (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :
    SchemeHomOver (𝟙 _) (GoodReductionJacobian.RelativeGroupLaw.baseChangeStr (resPt A ≫ Λ.σA) O.g) :=
  toFibrePt (O.ptsSp z)

theorem u_add (a b : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) :
    u O (a + b) = (O.L.baseChange (resPt A ≫ Λ.σA)).mul (𝟙 _) (u O a) (u O b) := by
  rw [u, O.ptsSp_add, toFibrePt_ofFibrePt]
  rfl

theorem u_zero : u O 0 = (O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _) := by
  letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
  have h := u_add O 0 0
  have e0 : (0 : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) + 0 = 0 := by abel
  have e : u O ((0 : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) + 0) = u O 0 :=
    congrArg (u O) e0
  exact left_eq_mul.mp (e.symm.trans h)

theorem u_nsmul (z : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset) (n : ℕ) :
    letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
    u O (n • z) = (u O z) ^ n := by
  letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
  induction n with
  | zero => rw [zero_nsmul, pow_zero]; exact u_zero O
  | succ n ih => rw [succ_nsmul, pow_succ, u_add, ih]; rfl

end SpecialFibre

section RootsLift

variable (hA : ∃ p : ℕ, p.Prime ∧ A.LiesOverPrime p)

omit hA in

theorem restrictRootsOfUnity_residue_injective {m : ℕ} [NeZero m] (hmκ : (m : ResidueField ↥A) ≠ 0) :
    Function.Injective (restrictRootsOfUnity (residue ↥A) m) := by
  intro ζ ζ' h

  rw [← mul_inv_eq_one]
  have h1 : restrictRootsOfUnity (residue ↥A) m (ζ * ζ'⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  set ξ := ζ * ζ'⁻¹ with hξ

  have ha : ((ξ : (↥A)ˣ) : ↥A) ^ m = 1 := by
    have := ξ.2
    rw [mem_rootsOfUnity] at this
    have h2 := congrArg Units.val this
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at h2
  have hres : residue ↥A ((ξ : (↥A)ˣ) : ↥A) = 1 := by
    have := congrArg (fun u : rootsOfUnity m (ResidueField ↥A) => ((u : (ResidueField ↥A)ˣ) : ResidueField ↥A)) h1
    simpa [restrictRootsOfUnity_coe_apply] using this
  by_contra hne
  have hne' : ((ξ : (↥A)ˣ) : ↥A) ≠ 1 := by
    intro e; apply hne
    apply Subtype.ext
    exact Units.val_eq_one.mp e
  have hgeom : (Finset.range m).sum (fun i => ((ξ : (↥A)ˣ) : ↥A) ^ i) = 0 := by
    have := geom_sum_mul ((ξ : (↥A)ˣ) : ↥A) m
    rw [ha, sub_self, mul_eq_zero] at this
    exact this.resolve_right (sub_ne_zero.mpr hne')
  have := congrArg (residue ↥A) hgeom
  rw [map_sum, map_zero] at this
  simp only [map_pow, hres, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at this
  exact hmκ this

omit hA in

theorem restrictRootsOfUnity_residue_bijective {m : ℕ} [NeZero m] (hmκ : (m : ResidueField ↥A) ≠ 0) :
    Function.Bijective (restrictRootsOfUnity (residue ↥A) m) := by
  classical
  have hinj := restrictRootsOfUnity_residue_injective (A := A) hmκ

  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) m
  have hmem : ζ₀ ∈ A := mem_of_pow_eq_one (NeZero.pos m) hζ₀.pow_eq_one
  have hprim : IsPrimitiveRoot (⟨ζ₀, hmem⟩ : ↥A) m := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ₀
  have hcardA : Nat.card (rootsOfUnity m ↥A) = m := hprim.card_rootsOfUnity
  have hcardκ : Nat.card (rootsOfUnity m (ResidueField ↥A)) ≤ m := card_rootsOfUnity _ _
  have hle := Nat.card_le_card_of_injective _ hinj
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, ?_⟩
  omega

noncomputable def rootsLift {m : ℕ} [NeZero m] (hmκ : (m : ResidueField ↥A) ≠ 0) :
    rootsOfUnity m (ResidueField ↥A) ≃* rootsOfUnity m ↥A :=
  (MulEquiv.ofBijective _ (restrictRootsOfUnity_residue_bijective (A := A) hmκ)).symm

theorem residue_rootsLift {m : ℕ} [NeZero m] (hmκ : (m : ResidueField ↥A) ≠ 0) (η : rootsOfUnity m (ResidueField ↥A)) :
    residue ↥A (((rootsLift (A := A) hmκ η : rootsOfUnity m ↥A) : (↥A)ˣ) : ↥A) = ((η : (ResidueField ↥A)ˣ) : ResidueField ↥A) := by
  have h : restrictRootsOfUnity (residue ↥A) m (rootsLift (A := A) hmκ η) = η :=
    MulEquiv.apply_symm_apply (MulEquiv.ofBijective _ (restrictRootsOfUnity_residue_bijective (A := A) hmκ)) η
  have := congrArg (fun u : rootsOfUnity m (ResidueField ↥A) => ((u : (ResidueField ↥A)ˣ) : ResidueField ↥A)) h
  simpa [restrictRootsOfUnity_coe_apply] using this

end RootsLift

section Descent

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)
  {m : ℕ} [NeZero m] (hm : 0 < m) (hmκ : (m : ResidueField ↥A) ≠ 0)
  (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A)
  (hψ : (WithConv.toConv ψ) ^ m = 1)

abbrev piCast (t m : ℕ) : (Fin t → ℤ) →+ (Fin t → ZMod m) :=
  AddMonoidHom.pi fun i => (Int.castAddHom (ZMod m)).comp (Pi.evalAddMonoidHom (fun _ : Fin t => ℤ) i)

theorem piCast_apply (t m : ℕ) (v : Fin t → ℤ) (i : Fin t) : piCast t m v i = (v i : ZMod m) := rfl

theorem piCast_surjective (t m : ℕ) : Function.Surjective (piCast t m) := by
  intro w
  refine ⟨fun i => ((w i).cast : ℤ), ?_⟩
  ext i
  rw [piCast_apply, ZMod.intCast_zmod_cast]

noncomputable def Fψ : Multiplicative (Fin O.toricRank → ℤ) →* (ResidueField ↥A)ˣ :=
  (((ψ : torusCoord (ResidueField ↥A) O.toricRank →* ResidueField ↥A).comp
    (AddMonoidAlgebra.of (ResidueField ↥A) (Fin O.toricRank → ℤ))).toHomUnits)

theorem Fψ_apply (v : Fin O.toricRank → ℤ) :
    ((Fψ O ψ (Multiplicative.ofAdd v) : (ResidueField ↥A)ˣ) : ResidueField ↥A) = ψ (AddMonoidAlgebra.single v 1) := rfl

omit [NeZero m] in
include hψ in
theorem ψ_single_pow (v : Fin O.toricRank → ℤ) : ψ (AddMonoidAlgebra.single v 1) ^ m = 1 := by
  have := convPow_apply_single (ResidueField ↥A) O.toricRank (WithConv.toConv ψ) v m
  rw [hψ] at this
  change (1 : WithConv (torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A))
    (AddMonoidAlgebra.single v 1) = _ at this
  rw [AlgHom.convOne_apply, AddMonoidAlgebra.counit_single] at this
  simp only [CoalgebraStruct.counit, LinearMap.id_coe, id_eq, map_one] at this
  exact this.symm

include hψ in
theorem ker_le : (piCast O.toricRank m).toMultiplicative.ker ≤ (Fψ O ψ).ker := by
  intro v hv
  rw [MonoidHom.mem_ker] at hv ⊢

  have hdiv : ∀ i, (m : ℤ) ∣ (Multiplicative.toAdd v) i := by
    intro i
    have := congrFun (congrArg Multiplicative.toAdd hv) i
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  choose w hw using hdiv
  have hvw : Multiplicative.toAdd v = m • (w : Fin O.toricRank → ℤ) := by
    ext i; simp [hw i]
  apply Units.ext
  rw [show v = Multiplicative.ofAdd (Multiplicative.toAdd v) from rfl, hvw, Fψ_apply, Units.val_one]
  have : AddMonoidAlgebra.single (m • (w : Fin O.toricRank → ℤ)) (1 : ResidueField ↥A) =
      (AddMonoidAlgebra.single w 1) ^ m := by
    rw [AddMonoidAlgebra.single_pow, one_pow]
  rw [this, map_pow]
  exact ψ_single_pow O ψ hψ w

noncomputable def gψ : Multiplicative (Fin O.toricRank → ZMod m) →* (ResidueField ↥A)ˣ :=
  MonoidHom.liftOfSurjective (piCast O.toricRank m).toMultiplicative (piCast_surjective _ _) ⟨Fψ O ψ, ker_le O ψ hψ⟩

theorem gψ_piCast (v : Fin O.toricRank → ℤ) :
    gψ O ψ hψ (Multiplicative.ofAdd (piCast O.toricRank m v)) = Fψ O ψ (Multiplicative.ofAdd v) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem gψ_mem (w : Multiplicative (Fin O.toricRank → ZMod m)) : gψ O ψ hψ w ∈ rootsOfUnity m (ResidueField ↥A) := by
  rw [mem_rootsOfUnity, ← map_pow]
  have : w ^ m = 1 := by
    change Multiplicative.ofAdd (m • Multiplicative.toAdd w) = Multiplicative.ofAdd 0
    congr 1; ext i; simp
  rw [this, map_one]

noncomputable def gμ : Multiplicative (Fin O.toricRank → ZMod m) →* rootsOfUnity m (ResidueField ↥A) :=
  (gψ O ψ hψ).codRestrict _ (gψ_mem O ψ hψ)

noncomputable def χLift : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ :=
  AddMonoidAlgebra.lift ↥A (AlgebraicClosure ℚ) (Fin O.toricRank → ZMod m)
    (A.subtype.toMonoidHom.comp ((Units.coeHom ↥A).comp ((rootsOfUnity m ↥A).subtype.comp
      ((rootsLift (A := A) hmκ).toMonoidHom.comp (gμ O ψ hψ)))))

theorem χLift_single (w : Fin O.toricRank → ZMod m) :
    χLift O hmκ ψ hψ (AddMonoidAlgebra.single w 1) =
      ((((rootsLift (A := A) hmκ (gμ O ψ hψ (Multiplicative.ofAdd w)) : rootsOfUnity m ↥A) : (↥A)ˣ) : ↥A) : AlgebraicClosure ℚ) := by
  rw [χLift, AddMonoidAlgebra.lift_single, one_smul]
  rfl

theorem charA_χLift_single (w : Fin O.toricRank → ZMod m) :
    (charA hm (χLift O hmκ ψ hψ) (AddMonoidAlgebra.single w 1) : ↥A) =
      (((rootsLift (A := A) hmκ (gμ O ψ hψ (Multiplicative.ofAdd w)) : rootsOfUnity m ↥A) : (↥A)ˣ) : ↥A) :=
  Subtype.ext (χLift_single O hmκ ψ hψ w)

theorem charK_χLift_comp :
    (charK O hm (χLift O hmκ ψ hψ)).toRingHom.comp
        (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (piCast O.toricRank m)) = ψ.toRingHom := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, map_zero]
    have hb : AddMonoidAlgebra.single (0 : Fin O.toricRank → ZMod m) b = algebraMap (ResidueField ↥A) _ b := rfl
    have hb' : AddMonoidAlgebra.single (0 : Fin O.toricRank → ℤ) b = algebraMap (ResidueField ↥A) _ b := rfl
    rw [hb, hb', AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe, AlgHom.commutes,
      AlgHom.commutes]
  · intro v
    rw [RingHom.comp_apply, AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      AlgHom.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, RingHom.coe_coe, charK_single, one_mul,
      charA_χLift_single, residue_rootsLift]
    change ((gψ O ψ hψ (Multiplicative.ofAdd (piCast O.toricRank m v)) : (ResidueField ↥A)ˣ) : ResidueField ↥A) = _
    rw [gψ_piCast, Fψ_apply]

theorem torusPtK_χLift : torusPtK O hm (χLift O hmκ ψ hψ) = torusPt (ResidueField ↥A) O.toricRank ψ := by
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, charK_χLift_comp]

end Descent

section Backward

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)

theorem exists_char_red_eq {m : ℕ} [NeZero m] (hm : 0 < m) (hmκ : (m : ResidueField ↥A) ≠ 0)
    (s : SchemeHomOver Λ.σA O.g)
    (ψ : torusCoord (ResidueField ↥A) O.toricRank →ₐ[ResidueField ↥A] ResidueField ↥A) (hψ : (WithConv.toConv ψ) ^ m = 1)
    (hw : w O (WithConv.toConv ψ) = toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) :
    ∃ χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (sChar O hm χ) =
        GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s := by
  refine ⟨χLift O hmκ ψ hψ, ?_⟩
  have h1 := torusPtK_comp_torusFibre O hm (χLift O hmκ ψ hψ)
  rw [torusPtK_χLift] at h1
  have h2 : toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl (sChar O hm (χLift O hmκ ψ hψ))) =
      toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) := h1.symm.trans hw
  have h3 := congrArg ofFibrePt h2
  rwa [ofFibrePt_toFibrePt, ofFibrePt_toFibrePt] at h3

theorem mem_toricPts_of_good {m : ℕ} (hm : 0 < m) (hpm : m.Coprime p) {x : JH M H}
    (hx : x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m) (hgood : Good O x) :
    x ∈ O.toricPts m := by
  classical
  haveI : NeZero m := ⟨hm.ne'⟩
  have hmκ : (m : ResidueField ↥A) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff (ResidueField ↥A) p m).mp h
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hpm.symm this
  obtain ⟨s, hs, habq⟩ := (good_iff O x).mp hgood

  obtain ⟨y, hy⟩ := (O.abqFibre_eq_one_iff (𝟙 _) _).mp habq
  obtain ⟨ψ, rfl⟩ := exists_torusPt_eq (ResidueField ↥A) O.toricRank y
  have hw : w O (WithConv.toConv ψ) = toFibrePt (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) := hy

  obtain ⟨dom, sp, hdom, hsp, -, -, hinj, -⟩ :=
    ModularCurve.JHNeronObjectAtP.exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm p M H hpM A hA Λ O
  have hxdom : x ∈ dom := (hdom x).mpr ⟨s, hs⟩
  have hz : sp ⟨x, hxdom⟩ = O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) := hsp ⟨x, hxdom⟩ s hs
  have huz : u O (sp ⟨x, hxdom⟩) = w O (WithConv.toConv ψ) := by
    rw [hz, u, Equiv.apply_symm_apply, hw]

  have hmx : (m : ℤ) • x = 0 := Pic0.mem_torsion.mp hx
  have hmx' : m • (⟨x, hxdom⟩ : ↥dom) = 0 := by
    apply Subtype.ext
    change m • x = 0
    exact_mod_cast (natCast_zsmul x m).symm.trans hmx
  letI := (O.L.baseChange (resPt A ≫ Λ.σA)).pointGroup (𝟙 _)
  have hpow : (w O (WithConv.toConv ψ)) ^ m = 1 := by
    rw [← huz, ← u_nsmul, ← map_nsmul, hmx', map_zero]
    exact u_zero O
  have hψ : (WithConv.toConv ψ) ^ m = 1 := by
    apply w_injective O
    rw [w_pow, hpow]
    exact (w_one O).symm

  obtain ⟨χ, hred⟩ := exists_char_red_eq O hm hmκ s ψ hψ hw
  clear hw hy hpow hψ huz
  have htp_dom : O.toricPoint m hm χ ∈ dom := (hdom _).mpr (extendsToPlace_toricPoint O hm χ)
  have hsp_eq : sp ⟨O.toricPoint m hm χ, htp_dom⟩ = sp ⟨x, hxdom⟩ := by
    have e := hsp ⟨O.toricPoint m hm χ, htp_dom⟩ (sChar O hm χ) (pts_toricPoint_eq O hm χ)
    exact e.trans ((congrArg O.ptsSp.symm hred).trans hz.symm)

  have htor : O.toricPoint m hm χ ∈ O.toricPts m := by
    rw [JHNeronObjectAtP.toricPts, dif_pos hm]
    exact AddSubgroup.subset_closure ⟨χ, rfl⟩
  have hdiff : (⟨x, hxdom⟩ : ↥dom) - ⟨O.toricPoint m hm χ, htp_dom⟩ = 0 := by
    apply hinj
    · refine ⟨m, hm, fun h => (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hpm.symm h, ?_⟩
      have h1 : m • x = 0 := by exact_mod_cast (natCast_zsmul x m).symm.trans hmx
      have h2 : m • O.toricPoint m hm χ = 0 := by
        have := ModularCurve.JHNeronObjectAtP.toricPts_le_torsion p M H hpM A hA Λ O m htor
        rw [Pic0.mem_torsion] at this
        exact_mod_cast (natCast_zsmul _ m).symm.trans this
      rw [AddSubgroupClass.coe_sub]
      change m • (x - O.toricPoint m hm χ) = 0
      rw [nsmul_sub, h1, h2, sub_zero]
    · rw [map_sub, hsp_eq, sub_self]
  have : x = O.toricPoint m hm χ := by
    have := congrArg Subtype.val hdiff
    exact sub_eq_zero.mp this
  rw [this]
  exact htor

end Backward

end MemToric
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one.MemToric"

open MemToric in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (m : ℕ) (hm : 0 < m) (hpm : m.Coprime p)
    (x : JH M H) (hx : x ∈ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) m) :
    x ∈ O.toricPts m ↔
      ∃ s : SchemeHomOver Λ.σA O.g, (O.pts x).1 = barPt A ≫ s.1 ∧
        ∀ i : Fin 2, fibreMap (O.abqFibre i) (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s) =
          Λ.L.one (resPt A ≫ Λ.σA) := by
  constructor
  · intro h
    exact MemToric.good_of_mem_toricPts O hm h
  · intro h
    exact MemToric.mem_toricPts_of_good O hm hpm hx h

end S_ModularCurve_JHNeronObjectAtP_mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_mem_toricPts_iff_exists_fibreMap_abqFibre_eq_one (solution)
