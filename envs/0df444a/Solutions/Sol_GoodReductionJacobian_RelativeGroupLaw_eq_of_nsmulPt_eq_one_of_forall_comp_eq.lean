-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.eq_of_nsmulPt_eq_one_of_forall_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/218f7173-b6c3-5141-ba2b-98a0a2723946

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

universe u

namespace TorSec13

section PointAlgebra
variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem comp_one (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') : ψ ≫ (L.one t).1 = (L.one t').1 :=
  congrArg Subtype.val (L.one_natural t t' ψ hψ)

theorem nsmulPt_eq_nsmul (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem comp_nsmulPt (L : RelativeGroupLaw R f)
    {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T)
    (hψ : ψ ≫ t = t') (n : ℕ) (P : SchemeHomOver t f) :
    ψ ≫ (nsmulPt L t n P).1 = (nsmulPt L t' n (schemeHomOverComp ψ hψ P)).1 := by
  rw [nsmulPt_eq_nsmul, nsmulPt_eq_nsmul, ← L.nsmul_natural t t' ψ hψ n P]
  rfl

theorem nsmulPt_coe (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : (nsmulPt L t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have h := comp_nsmulPt L f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hid : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := Subtype.ext (by simp)
  rw [hid] at h
  rw [← h, RelativeGroupLaw.schemeNsmul, nsmulPt_eq_nsmul]

theorem coe_comp_schemeNsmul_of_nsmulPt_eq_one (L : RelativeGroupLaw R f) (n : ℕ) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) (hP : nsmulPt L t n P = L.one t) :
    P.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  rw [← nsmulPt_coe, hP]
  exact (comp_one L (𝟙 _) t t (Category.comp_id _)).symm

theorem schemeKerStr_eq (L : RelativeGroupLaw R f) (n : ℕ) :
    L.schemeKerStr n = pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f := by
  show pullback.snd (L.schemeNsmul n) (L.one (𝟙 _)).1 = _
  have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f =
      pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc, (L.one (𝟙 _)).2, Category.comp_id]

end PointAlgebra

section Geom

theorem exists_geomPt (T : Scheme.{u}) (x : T) :
    ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k) (τ : Spec (CommRingCat.of k) ⟶ T), x ∈ Set.range τ.base := by
  refine ⟨AlgebraicClosure (T.residueField x), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x) (AlgebraicClosure (T.residueField x)))) ≫
      T.fromSpecResidueField x, ?_⟩
  have hx : x ∈ Set.range (T.fromSpecResidueField x).base := by
    rw [Scheme.range_fromSpecResidueField]; exact Set.mem_singleton x
  obtain ⟨y, hy⟩ := hx
  refine ⟨default, ?_⟩
  rw [Scheme.Hom.comp_apply]
  have hy' : (Spec.map (CommRingCat.ofHom (algebraMap (T.residueField x)
      (AlgebraicClosure (T.residueField x))))).base default = y := Subsingleton.elim _ _
  rw [hy']
  exact hy

end Geom

end TorSec13

open TorSec13 in

theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) [IsFinite (L.schemeKerStr n)] [Etale (L.schemeKerStr n)]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P Q : SchemeHomOver t f)
    (hP : nsmulPt L t n P = L.one t) (hQ : nsmulPt L t n Q = L.one t)
    (h : ∀ (k : Type u) [Field k] [IsAlgClosed k] (τ : Spec (CommRingCat.of k) ⟶ T), τ ≫ P.1 = τ ≫ Q.1) :
    P = Q := by
  have wP := coe_comp_schemeNsmul_of_nsmulPt_eq_one L n t P hP
  have wQ := coe_comp_schemeNsmul_of_nsmulPt_eq_one L n t Q hQ
  let κP : T ⟶ L.schemeKer n := pullback.lift P.1 t wP
  let κQ : T ⟶ L.schemeKer n := pullback.lift Q.1 t wQ
  have hκP : κP ≫ L.schemeKerStr n = t := pullback.lift_snd _ _ _
  have hκQ : κQ ≫ L.schemeKerStr n = t := pullback.lift_snd _ _ _

  let πT : pullback (L.schemeKerStr n) t ⟶ T := pullback.snd (L.schemeKerStr n) t
  let sP : T ⟶ pullback (L.schemeKerStr n) t := pullback.lift κP (𝟙 T) (by rw [hκP, Category.id_comp])
  let sQ : T ⟶ pullback (L.schemeKerStr n) t := pullback.lift κQ (𝟙 T) (by rw [hκQ, Category.id_comp])
  have hsP : sP ≫ πT = 𝟙 T := pullback.lift_snd _ _ _
  have hsQ : sQ ≫ πT = 𝟙 T := pullback.lift_snd _ _ _
  obtain ⟨-, hO⟩ :=
    AlgebraicGeometry.isClopen_preimage_diagonal_of_formallyUnramified_of_isSeparated πT sP sQ hsP hsQ

  have hall : Set.range (𝟙 T : T ⟶ T).base ⊆
      ((pullback.lift sP sQ (hsP.trans hsQ.symm) ⁻¹ᵁ (pullback.diagonal πT).opensRange : T.Opens) : Set T) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨k, _, _, τ, y, hy⟩ := exists_geomPt T x
    have hτ : τ ≫ sP = τ ≫ sQ := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst]; exact h k τ
        · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
    have hsub := (hO τ).2 hτ
    have : x ∈ Set.range τ.base := ⟨y, hy⟩
    exact hsub this
  have e := (hO (𝟙 T)).1 hall
  rw [Category.id_comp, Category.id_comp] at e
  have e2 : κP = κQ := by
    have := congrArg (fun φ => φ ≫ pullback.fst (L.schemeKerStr n) t) e
    simpa only [sP, sQ, pullback.lift_fst] using this
  apply Subtype.ext
  have := congrArg (fun φ => φ ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) e2
  simpa only [κP, κQ, pullback.lift_fst] using this

end S_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_eq_of_nsmulPt_eq_one_of_forall_comp_eq (solution)
