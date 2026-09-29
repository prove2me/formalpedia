-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_finPts_of_coprime_of_representsRelSubPic
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/c16b94a6-4f9f-5388-a7f3-6eee3a718938

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange

import Theorems.Thm_AlgebraicGeometry_SchemeHomOver_ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_eq_one_of_isTorsionPoint_of_comp_residue_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_finPts_of_coprime_of_representsRelSubPic

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP

noncomputable section

namespace FINFIXEDH

section grp
variable {R : Type} [CommRing R] {X T : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
  (t : T ⟶ Spec (CommRingCat.of R))

theorem eq_one_of_mul_self (a : SchemeHomOver t f) (h : L.mul t a a = a) : a = L.one t := by
  calc a = L.mul t (L.one t) a := (L.one_mul t a).symm
    _ = L.mul t (L.mul t (L.inv t a) a) a := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t a) (L.mul t a a) := by rw [L.mul_assoc]
    _ = L.one t := by rw [h, L.inv_mul_cancel]

theorem one_castOver {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') :
    L.one ι' = castOver h (L.one ι) := by
  subst h; rfl

theorem nsmul_castOver {ι ι' : T ⟶ Spec (CommRingCat.of R)} (h : ι = ι') (n : ℕ) (u : SchemeHomOver ι f) :
    L.nsmul ι' n (castOver h u) = castOver h (L.nsmul ι n u) := by
  subst h; rfl

theorem inv_unique (a b : SchemeHomOver t f) (h : L.mul t b a = L.one t) : b = L.inv t a := by
  calc b = L.mul t b (L.one t) := (L.mul_one t b).symm
    _ = L.mul t b (L.mul t a (L.inv t a)) := by rw [L.mul_inv_cancel]
    _ = L.mul t (L.mul t b a) (L.inv t a) := by rw [L.mul_assoc]
    _ = L.inv t a := by rw [h, L.one_mul]

theorem eq_of_mul_inv_eq_one (a b : SchemeHomOver t f) (h : L.mul t a (L.inv t b) = L.one t) : a = b := by
  calc a = L.mul t a (L.one t) := (L.mul_one t a).symm
    _ = L.mul t a (L.mul t (L.inv t b) b) := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.mul t a (L.inv t b)) b := by rw [L.mul_assoc]
    _ = b := by rw [h, L.one_mul]

theorem inv_one : L.inv t (L.one t) = L.one t :=
  (inv_unique L t _ _ (L.mul_one t _)).symm

theorem nsmul_mul_of_comm (hc : L.IsCommutative) (n : ℕ) (a b : SchemeHomOver t f) :
    L.nsmul t n (L.mul t a b) = L.mul t (L.nsmul t n a) (L.nsmul t n b) := by
  induction n with
  | zero => simp only [RelativeGroupLaw.nsmul_zero, L.one_mul]
  | succ n ih =>
      simp only [RelativeGroupLaw.nsmul_succ, ih]
      rw [L.mul_assoc, ← L.mul_assoc _ (L.nsmul t n b) a b, hc.mul_comm _ (L.nsmul t n b) a, L.mul_assoc, ← L.mul_assoc]

theorem nsmul_inv_of_comm (hc : L.IsCommutative) (n : ℕ) (a : SchemeHomOver t f) :
    L.nsmul t n (L.inv t a) = L.inv t (L.nsmul t n a) := by
  apply inv_unique
  rw [← nsmul_mul_of_comm L t hc, L.inv_mul_cancel, RelativeGroupLaw.nsmul_unit]

theorem inv_natural {T' : Scheme.{0}} (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t')
    (a : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t a) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ a) := by
  apply inv_unique
  rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]

end grp

section ext
variable {p : ℕ} {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem ext_unique_aux {σA : Spec (CommRingCat.of ↥A) ⟶ base p} {X : Scheme.{0}} {f : X ⟶ base p} [IsSeparated f]
    (P Q : SchemeHomOver σA f) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated (RelativeGroupLaw.baseChangeStr σA f) := by
    show IsSeparated (pullback.snd f σA); infer_instance
  have key : toFibrePt P = toFibrePt Q := by
    refine AlgebraicGeometry.SchemeHomOver.ext_of_forall_algebraicClosure_point_of_isReduced_of_flat
      (R := ↥A) (AlgebraicClosure ℚ) (AlgebraicClosure ℚ) (gY := 𝟙 (Spec (CommRingCat.of ↥A)))
      (gX := RelativeGroupLaw.baseChangeStr σA f) (toFibrePt P) (toFibrePt Q) ?_
    intro z
    have hz : z.1 = barPt A := by have h__af := z.2; simp at h__af; exact h__af
    rw [hz]
    show barPt A ≫ pullback.lift P.1 (𝟙 _) _ = barPt A ≫ pullback.lift Q.1 (𝟙 _) _
    apply pullback.hom_ext
    · simpa only [Category.assoc, pullback.lift_fst] using h
    · simp only [Category.assoc, pullback.lift_snd]
  apply Subtype.ext
  have h1 : P.1 = (toFibrePt P).1 ≫ pullback.fst f σA := by
    show P.1 = pullback.lift P.1 (𝟙 _) _ ≫ pullback.fst f σA
    rw [pullback.lift_fst]
  have h2 : Q.1 = (toFibrePt Q).1 ≫ pullback.fst f σA := by
    show Q.1 = pullback.lift Q.1 (𝟙 _) _ ≫ pullback.fst f σA
    rw [pullback.lift_fst]
  rw [h1, h2, key]

theorem hom_ext_barPt {R : CommRingCat.{0}} (u v : Spec (CommRingCat.of ↥A) ⟶ Spec R)
    (h : barPt A ≫ u = barPt A ≫ v) : u = v := by
  obtain ⟨u', rfl⟩ := Spec.map_surjective u
  obtain ⟨v', rfl⟩ := Spec.map_surjective v
  have h' : Spec.map (u' ≫ CommRingCat.ofHom A.subtype) = Spec.map (v' ≫ CommRingCat.ofHom A.subtype) := by
    simpa only [Spec.map_comp] using h
  have h'' := Spec.map_injective h'
  apply congrArg Spec.map
  ext x
  have hx := RingHom.congr_fun (congrArg CommRingCat.Hom.hom h'') x
  simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply] at hx
  exact hx

theorem isUnit_natCast_of_coprime (hA : A.LiesOverPrime p) {m : ℕ} (hmp : m.Coprime p) : IsUnit ((m : ℕ) : ↥A) := by
  have hp : ((p : ↥A) : AlgebraicClosure ℚ) ∈ A.nonunits := by simp at hA ⊢; exact hA
  have hp' : (p : ↥A) ∈ maximalIdeal ↥A := ValuationSubring.coe_mem_nonunits_iff.mp hp
  by_contra hm
  have hm' : (m : ↥A) ∈ maximalIdeal ↥A := (IsLocalRing.mem_maximalIdeal _).mpr hm
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr hmp
  have h1 : (1 : ↥A) ∈ maximalIdeal ↥A := by
    have : ((a : ↥A) * m + (b : ↥A) * p) = 1 := by exact_mod_cast hab
    rw [← this]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hm') (Ideal.mul_mem_left _ _ hp')
  exact (Ideal.ne_top_iff_one _).mp (Ideal.IsMaximal.ne_top inferInstance) h1

section inertia
variable (τ : ↥(A.decompositionSubgroup ℚ))

def actA : ↥A →+* ↥A := MulSemiringAction.toRingHom _ _ τ

def actSpec : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥A) := Spec.map (CommRingCat.ofHom (actA τ))

theorem subtype_comp_actA :
    A.subtype.comp (actA τ) = ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ).comp A.subtype := by
  ext a; rfl

theorem barPt_actSpec :
    barPt A ≫ actSpec τ =
      Spec.map (CommRingCat.ofHom ((τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ barPt A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, subtype_comp_actA]

theorem specMap_galois_genPt (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ genPt p = genPt p := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  show σ (algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ)) = algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ)
  exact AlgEquiv.commutes σ _

theorem actSpec_σA {σA : Spec (CommRingCat.of ↥A) ⟶ base p} (hσA : barPt A ≫ σA = genPt p) :
    actSpec τ ≫ σA = σA := by
  apply hom_ext_barPt
  rw [← Category.assoc, barPt_actSpec, Category.assoc, hσA, specMap_galois_genPt]

theorem residue_comp_actA (hτ : τ ∈ A.inertiaSubgroup ℚ) : (residue ↥A).comp (actA τ) = residue ↥A := by
  ext a
  show residue ↥A (τ • a) = residue ↥A a
  have h1 : residue ↥A (τ • a) = τ • residue ↥A a := rfl
  have h2 : τ • residue ↥A a = residue ↥A a := by
    have h := RingEquiv.congr_fun (MonoidHom.mem_ker.mp hτ) (residue ↥A a)
    simpa using h
  rw [h1, h2]

theorem resPt_actSpec (hτ : τ ∈ A.inertiaSubgroup ℚ) : resPt A ≫ actSpec τ = resPt A := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, residue_comp_actA τ hτ]

end inertia
end ext

section JH
variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem ext_unique (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (P Q : SchemeHomOver Λ.σA O.g) (h : barPt A ≫ P.1 = barPt A ≫ Q.1) : P = Q := by
  haveI : IsSeparated O.g := O.separated
  exact ext_unique_aux P Q h

theorem pts_zero (O : JHNeronObjectAtP p M H hpM A hA Λ) : O.pts 0 = O.L.one (genPt p) :=
  eq_one_of_mul_self O.L _ _ (by rw [← O.pts_add, add_zero])

theorem pts_nsmul (O : JHNeronObjectAtP p M H hpM A hA Λ) (n : ℕ) (x : JH M H) :
    O.pts (n • x) = O.L.nsmul (genPt p) n (O.pts x) := by
  induction n with
  | zero => rw [zero_nsmul, pts_zero, RelativeGroupLaw.nsmul_zero]
  | succ n ih => rw [succ_nsmul, O.pts_add, ih, RelativeGroupLaw.nsmul_succ]

theorem nsmul_eq_one_of_ext (O : JHNeronObjectAtP p M H hpM A hA Λ) {m : ℕ} (x : JH M H) (hx : m • x = 0)
    (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts x).1 = barPt A ≫ s.1) :
    O.L.nsmul Λ.σA m s = O.L.one Λ.σA := by
  apply ext_unique O
  have h1 := congrArg Subtype.val (O.L.nsmul_natural Λ.σA (barPt A ≫ Λ.σA) (barPt A) rfl m s)
  have h2 := congrArg Subtype.val (O.L.one_natural Λ.σA (barPt A ≫ Λ.σA) (barPt A) rfl)
  simp only [GoodReductionJacobian.schemeHomOverComp_coe] at h1 h2
  rw [h1, h2]
  have hx' : O.pts x = castOver Λ.hσA (GoodReductionJacobian.schemeHomOverComp (barPt A) rfl s) := Subtype.ext hs
  have h3 := pts_nsmul O m x
  rw [hx, pts_zero, hx', nsmul_castOver, one_castOver O.L Λ.hσA] at h3
  have h4 := congrArg Subtype.val h3
  exact h4.symm

theorem smul_eq_self_of_ext (O : JHNeronObjectAtP p M H hpM A hA Λ) {m : ℕ} (hmp : m.Coprime p)
    (x : JH M H) (hxm : m • x = 0) (s : SchemeHomOver Λ.σA O.g) (hs : (O.pts x).1 = barPt A ≫ s.1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ A.inertiaSubgroupIn ℚ) : σ • x = x := by
  obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.mp hσ

  let s' : SchemeHomOver Λ.σA O.g := GoodReductionJacobian.schemeHomOverComp (actSpec τ) (actSpec_σA τ Λ.hσA) s
  have hs' : (O.pts (((A.decompositionSubgroup ℚ).subtype τ) • x)).1 = barPt A ≫ s'.1 := by
    rw [O.pts_galois, hs, GoodReductionJacobian.schemeHomOverComp_coe, ← Category.assoc, ← Category.assoc, barPt_actSpec]
    rfl

  have hs_tors : O.L.nsmul Λ.σA m s = O.L.one Λ.σA := nsmul_eq_one_of_ext O x hxm s hs
  have hs'_tors : O.L.nsmul Λ.σA m s' = O.L.one Λ.σA := by
    show O.L.nsmul Λ.σA m (GoodReductionJacobian.schemeHomOverComp (actSpec τ) (actSpec_σA τ Λ.hσA) s) = _
    rw [← O.L.nsmul_natural Λ.σA Λ.σA (actSpec τ) (actSpec_σA τ Λ.hσA) m s, hs_tors, O.L.one_natural]

  have hred : GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s' =
      GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s := by
    apply Subtype.ext
    simp only [GoodReductionJacobian.schemeHomOverComp_coe]
    show resPt A ≫ actSpec τ ≫ s.1 = resPt A ≫ s.1
    rw [← Category.assoc, resPt_actSpec τ hτ]

  have heq : s' = s := by
    haveI : LocallyOfFiniteType O.g := O.locallyOfFiniteType
    apply eq_of_mul_inv_eq_one O.L
    refine GoodReductionJacobian.RelativeGroupLaw.eq_one_of_isTorsionPoint_of_comp_residue_eq O.L O.comm Λ.σA m
      (isUnit_natCast_of_coprime hA hmp) _ ?_ ?_
    · show O.L.nsmul Λ.σA m _ = O.L.one Λ.σA
      rw [nsmul_mul_of_comm O.L _ O.comm, nsmul_inv_of_comm O.L _ O.comm, hs_tors, hs'_tors, inv_one, O.L.one_mul]
    · rw [O.L.mul_natural, inv_natural, hred, O.L.mul_inv_cancel, O.L.one_natural]
  apply O.pts.injective
  apply Subtype.ext
  rw [hs', heq, hs]

theorem forall_smul_eq_self_of_mem_finPts (O : JHNeronObjectAtP p M H hpM A hA Λ) {m : ℕ} (hmp : m.Coprime p)
    (x : JH M H) (hx : x ∈ O.finPts m) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x := by
  intro σ hσ
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
      obtain ⟨hyt, s, hs⟩ := hy
      have hym : m • y = 0 := by
        have h2 := (Pic0.mem_torsion (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H)).mp hyt
        rwa [natCast_zsmul] at h2
      exact smul_eq_self_of_ext O hmp y hym s hs σ hσ
  | zero => exact smul_zero (A := JH M H) σ
  | add y z _ _ ihy ihz => rw [smul_add, ihy, ihz]
  | neg y _ ihy => rw [smul_neg, ihy]

end JH

end FINFIXEDH

end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open scoped MatrixGroups

open FINFIXEDH in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))
    (m : ℕ) (hm : 0 < m) (hmp : m.Coprime p)
    (x : JH M H) (hx : x ∈ O.finPts m) :
    ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x :=
  forall_smul_eq_self_of_mem_finPts O hmp x hx

#print axioms solution

end S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_finPts_of_coprime_of_representsRelSubPic
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_smul_eq_self_of_mem_inertiaSubgroupIn_of_mem_finPts_of_coprime_of_representsRelSubPic (solution)
