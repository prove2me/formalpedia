-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.schemeKerStr_baseChange_props
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/61bc979c-04c9-53f6-b3ff-5d9280b62e39

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_schemeKerStr_props_of_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isReduced_pullback_schemeKerStr_residueField_of_isUnit
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

namespace S125

universe u

variable {R : Type u} [CommRing R]

theorem nsmul_coe {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (x : SchemeHomOver t f) : (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have h := G.nsmul_natural f t x.1 x.2 n RelativeGroupLaw.idPoint
  have hx : GoodReductionJacobian.schemeHomOverComp x.1 x.2 (RelativeGroupLaw.idPoint (f := f)) = x :=
    Subtype.ext (Category.comp_id _)
  rw [hx] at h
  rw [← h]
  rfl

theorem nsmul_add {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : ℕ)
    (x : SchemeHomOver t f) : G.nsmul t (a + b) x = G.mul t (G.nsmul t a x) (G.nsmul t b x) := by
  induction b with
  | zero => rw [Nat.add_zero, RelativeGroupLaw.nsmul_zero, G.mul_one]
  | succ b ih => rw [Nat.add_succ, RelativeGroupLaw.nsmul_succ, ih, RelativeGroupLaw.nsmul_succ, G.mul_assoc]

theorem nsmul_mul {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a b : ℕ)
    (x : SchemeHomOver t f) : G.nsmul t (a * b) x = G.nsmul t a (G.nsmul t b x) := by
  induction a with
  | zero => rw [Nat.zero_mul, RelativeGroupLaw.nsmul_zero, RelativeGroupLaw.nsmul_zero]
  | succ a ih => rw [Nat.succ_mul, nsmul_add, ih, RelativeGroupLaw.nsmul_succ]

theorem schemeNsmul_mul {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (a b : ℕ) : G.schemeNsmul (a * b) = G.schemeNsmul b ≫ G.schemeNsmul a := by
  show (G.nsmul f (a * b) RelativeGroupLaw.idPoint).1 = _
  rw [nsmul_mul, nsmul_coe]
  rfl

theorem baseChangePointToBase_nsmul {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f)
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (n : ℕ)
    (x : SchemeHomOver t' (RelativeGroupLaw.baseChangeStr ι f)) :
    RelativeGroupLaw.baseChangePointToBase ι ((G.baseChange ι).nsmul t' n x) =
      G.nsmul _ n (RelativeGroupLaw.baseChangePointToBase ι x) := by
  induction n with
  | zero => exact RelativeGroupLaw.baseChangePointToBase_one ι G t'
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.nsmul_succ, RelativeGroupLaw.baseChangePointToBase_mul, ih]

theorem schemeNsmul_baseChange_fst {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (n : ℕ) :
    (G.baseChange ι).schemeNsmul n ≫ pullback.fst f ι = pullback.fst f ι ≫ G.schemeNsmul n := by
  have h := congrArg Subtype.val (baseChangePointToBase_nsmul ι G (RelativeGroupLaw.baseChangeStr ι f) n
    RelativeGroupLaw.idPoint)
  rw [RelativeGroupLaw.baseChangePointToBase_coe, nsmul_coe, nsmul_coe, RelativeGroupLaw.baseChangePointToBase_coe] at h
  simpa using h

theorem isPullback_schemeNsmul_baseChange {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (n : ℕ) :
    IsPullback ((G.baseChange ι).schemeNsmul n) (pullback.fst f ι) (pullback.fst f ι) (G.schemeNsmul n) := by
  refine IsPullback.of_right ?_ (schemeNsmul_baseChange_fst ι G n) (IsPullback.of_hasPullback f ι).flip
  rw [RelativeGroupLaw.schemeNsmul_over, G.schemeNsmul_over]
  exact (IsPullback.of_hasPullback f ι).flip

theorem fst_comp_eq_schemeKerStr {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) (n : ℕ) :
    pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ f = G.schemeKerStr n := by
  calc pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ f
      = pullback.fst (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ G.schemeNsmul n ≫ f := by rw [G.schemeNsmul_over]
    _ = (pullback.snd (G.schemeNsmul n) (G.one (𝟙 _)).1 ≫ (G.one (𝟙 _)).1) ≫ f := by
          rw [← Category.assoc, pullback.condition]
    _ = G.schemeKerStr n := by rw [Category.assoc, (G.one (𝟙 _)).2, Category.comp_id]

theorem exists_isPullback_schemeKerStr_baseChange₀ {R' : Type u} [CommRing R']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (n : ℕ) :
    ∃ π : (G.baseChange ι).schemeKer n ⟶ G.schemeKer n,
      IsPullback π ((G.baseChange ι).schemeKerStr n) (G.schemeKerStr n) ι := by
  set L₂ := G.baseChange ι with hL₂
  let c := pullback.fst f ι
  let q₂ := pullback.snd f ι
  have hc : IsPullback c q₂ f ι := IsPullback.of_hasPullback f ι
  set N₁ := G.schemeNsmul n with hN₁
  set N₂ := L₂.schemeNsmul n with hN₂
  have hcN : N₂ ≫ c = c ≫ N₁ := schemeNsmul_baseChange_fst ι G n
  have hN₂q : N₂ ≫ q₂ = q₂ := L₂.schemeNsmul_over n
  set e₁ := (G.one (𝟙 _)).1 with he₁
  set e₂ := (L₂.one (𝟙 _)).1 with he₂
  have he₁q : e₁ ≫ f = 𝟙 _ := (G.one (𝟙 _)).2
  have he₂q : e₂ ≫ q₂ = 𝟙 _ := (L₂.one (𝟙 _)).2
  have he₂p : e₂ ≫ c = (G.one (𝟙 _ ≫ ι)).1 :=
    congrArg Subtype.val (RelativeGroupLaw.baseChangePointToBase_one ι G (𝟙 _))
  have he : e₂ ≫ c = ι ≫ e₁ := by
    rw [he₂p]
    exact (congrArg Subtype.val (G.one_natural (𝟙 _) (𝟙 _ ≫ ι) ι (by simp))).symm
  have he_sq : IsPullback e₂ ι c e₁ := by
    refine IsPullback.of_right ?_ he hc.flip
    rw [he₂q, he₁q]
    exact IsPullback.of_horiz_isIso ⟨by simp⟩
  let a₁ := pullback.fst N₁ e₁
  let b₁ := pullback.snd N₁ e₁
  let a₂ := pullback.fst N₂ e₂
  let b₂ := pullback.snd N₂ e₂
  let π : pullback N₂ e₂ ⟶ pullback N₁ e₁ := pullback.lift (a₂ ≫ c) (b₂ ≫ ι) (by
    rw [Category.assoc, ← hcN, ← Category.assoc, pullback.condition, Category.assoc, he, Category.assoc])
  have hπ₁ : π ≫ a₁ = a₂ ≫ c := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ b₁ = b₂ ≫ ι := pullback.lift_snd _ _ _
  have sK₁ : IsPullback b₁ a₁ e₁ N₁ := (IsPullback.of_hasPullback N₁ e₁).flip
  have sK₂ : IsPullback b₂ a₂ e₂ N₂ := (IsPullback.of_hasPullback N₂ e₂).flip
  have BIG : IsPullback (b₂ ≫ ι) a₂ e₁ (N₂ ≫ c) := sK₂.paste_horiz he_sq.flip
  have TOP : IsPullback π a₂ a₁ c := by
    refine IsPullback.of_right ?_ hπ₁ sK₁
    rw [hπ₂, ← hcN]
    exact BIG
  have ALL : IsPullback π (a₂ ≫ q₂) (a₁ ≫ f) ι := TOP.paste_vert hc
  refine ⟨π, ?_⟩
  have h₁ : a₁ ≫ f = G.schemeKerStr n := fst_comp_eq_schemeKerStr G n
  have h₂ : a₂ ≫ q₂ = L₂.schemeKerStr n := fst_comp_eq_schemeKerStr L₂ n
  rw [h₁, h₂] at ALL
  exact ALL

theorem exists_isPullback_schemeKerStr_baseChange {R' R'' : Type u} [CommRing R'] [CommRing R'']
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (ι' : Spec (CommRingCat.of R'') ⟶ Spec (CommRingCat.of R'))
    {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} (G : RelativeGroupLaw R f) (n : ℕ) :
    ∃ π : (G.baseChange (ι' ≫ ι)).schemeKer n ⟶ (G.baseChange ι).schemeKer n,
      IsPullback π ((G.baseChange (ι' ≫ ι)).schemeKerStr n) ((G.baseChange ι).schemeKerStr n) ι' := by
  obtain ⟨π₁, h₁⟩ := exists_isPullback_schemeKerStr_baseChange₀ ι G n
  obtain ⟨π₂, h₂⟩ := exists_isPullback_schemeKerStr_baseChange₀ (ι' ≫ ι) G n

  refine ⟨h₁.lift π₂ ((G.baseChange (ι' ≫ ι)).schemeKerStr n ≫ ι') (by rw [Category.assoc]; exact h₂.w), ?_⟩
  exact IsPullback.of_right (by rw [h₁.lift_fst]; exact h₂) (h₁.lift_snd _ _ _) h₁

end S125

open S125 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m) :
    LocallyOfFiniteType ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    IsSeparated ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    QuasiCompact ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    Flat ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    LocallyQuasiFinite ((O.L.baseChange Λ.σA).schemeKerStr m) ∧
    (∃ π : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶ (O.L.baseChange Λ.σA).schemeKer m,
      IsPullback π ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
        ((O.L.baseChange Λ.σA).schemeKerStr m) (Spec.map (CommRingCat.ofHom (residue ↥A)))) ∧
    (∃ (XK : Scheme.{0}) (qK : XK ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
        (πK : XK ⟶ (O.L.baseChange Λ.σA).schemeKer m),
      IsPullback πK qK ((O.L.baseChange Λ.σA).schemeKerStr m)
        (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) ∧ IsReduced XK) := by
  classical
  set LA := O.L.baseChange Λ.σA with hLA
  haveI := O.separated
  haveI := O.quasiCompact
  haveI := O.locallyOfFiniteType
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr Λ.σA O.g) := by
    unfold RelativeGroupLaw.baseChangeStr; infer_instance
  haveI : QuasiCompact (RelativeGroupLaw.baseChangeStr Λ.σA O.g) := by
    unfold RelativeGroupLaw.baseChangeStr; infer_instance
  haveI : LocallyOfFiniteType (RelativeGroupLaw.baseChangeStr Λ.σA O.g) := by
    unfold RelativeGroupLaw.baseChangeStr; infer_instance
  obtain ⟨hqf, hqcN, hflN⟩ :=
    ModularCurve.JHNeronObjectAtP.locallyQuasiFinite_quasiCompact_flat_schemeNsmul_baseChange p M H hpM A hA Λ O m hm
  obtain ⟨hlqf, hqc, hflat, hsep, hone, -, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.schemeKerStr_props_of_schemeNsmul
      (RelativeGroupLaw.baseChangeStr Λ.σA O.g) LA m hqf hflN
  haveI := hone
  have hlft : LocallyOfFiniteType (LA.schemeKerStr m) := by
    rw [← fst_comp_eq_schemeKerStr LA m]
    infer_instance
  refine ⟨hlft, hsep, hqc, hflat, hlqf, ?_, ?_⟩
  · exact exists_isPullback_schemeKerStr_baseChange Λ.σA (resPt A) O.L m
  · let ιK : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ↥A) :=
      Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))
    set LK := O.L.baseChange (ιK ≫ Λ.σA) with hLK
    obtain ⟨πK, hπK⟩ := exists_isPullback_schemeKerStr_baseChange Λ.σA ιK O.L m
    have hcommK : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (AlgebraicClosure ℚ)))
        (x y : SchemeHomOver t (RelativeGroupLaw.baseChangeStr (ιK ≫ Λ.σA) O.g)), LK.mul t x y = LK.mul t y x :=
      fun t x y => (RelativeGroupLaw.IsCommutative.baseChange (ιK ≫ Λ.σA) (fun t x y => O.comm t x y)) t x y
    have hunitK : IsUnit ((m : ℕ) : AlgebraicClosure ℚ) := (Nat.cast_ne_zero.2 hm.ne').isUnit
    haveI hredK : IsReduced (LK.schemeKer m) := by
      have h := GoodReductionJacobian.RelativeGroupLaw.isReduced_pullback_schemeKerStr_residueField_of_isUnit
        LK hcommK m hunitK
      have hbij : Function.Bijective (algebraMap (AlgebraicClosure ℚ) (IsLocalRing.ResidueField (AlgebraicClosure ℚ))) :=
        ⟨(algebraMap (AlgebraicClosure ℚ) (IsLocalRing.ResidueField (AlgebraicClosure ℚ))).injective,
          IsLocalRing.residue_surjective⟩
      haveI : IsIso (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) (IsLocalRing.ResidueField (AlgebraicClosure ℚ)))) :=
        (RingEquiv.ofBijective _ hbij).toCommRingCatIso.isIso_hom
      exact isReduced_of_isOpenImmersion (inv (pullback.fst (LK.schemeKerStr m)
        (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure ℚ) (IsLocalRing.ResidueField (AlgebraicClosure ℚ)))))))
    exact ⟨_, _, πK, hπK, hredK⟩

end S_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props (solution)
