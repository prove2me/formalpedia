-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c623f85e-a427-50fa-8277-1e330984aa33

import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal IsLocalRing

open scoped Quaternion TensorProduct NumberField

universe u

namespace E162LVd1

theorem nsmulPt_eq_nsmul {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ)
    (P : SchemeHomOver t f) : nsmulPt L t n P = L.nsmul t n P := by
  induction n with
  | zero => rfl
  | succ n ih => rw [RelativeGroupLaw.nsmul_succ, ← ih]; rfl

theorem one_coe {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (L.one t).1 = t ≫ (L.one (𝟙 _)).1 := by
  have h := L.one_natural (𝟙 _) t t (Category.comp_id _)
  have h1 := congrArg Subtype.val h
  rw [schemeHomOverComp_coe] at h1
  exact h1.symm

theorem comp_schemeNsmul_eq_of_torsion {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f)
    (hP : L.nsmul t n P = L.one t) :
    P.1 ≫ L.schemeNsmul n = (P.1 ≫ f) ≫ (L.one (𝟙 _)).1 := by
  rw [← RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul, hP, one_coe, P.2]

theorem torsion_of_comp_schemeNsmul_eq {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (n : ℕ) (P : SchemeHomOver t f)
    (h : P.1 ≫ L.schemeNsmul n = (P.1 ≫ f) ≫ (L.one (𝟙 _)).1) :
    L.nsmul t n P = L.one t := by
  apply Subtype.ext
  rw [RelativeGroupLaw.coe_nsmul_eq_comp_schemeNsmul, h, P.2, ← one_coe]

theorem isClosedImmersion_oneSection {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) [IsSeparated f] :
    IsClosedImmersion (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
  have h1 : IsClosedImmersion ((L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f) := by
    rw [(L.one (𝟙 (Spec (CommRingCat.of R)))).2]; infer_instance
  exact IsClosedImmersion.of_comp (L.one (𝟙 (Spec (CommRingCat.of R)))).1 f

theorem kerFst_comp_f {R : Type u} [CommRing R] {A : Scheme.{u}}
    {f : A ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f) (n : ℕ) :
    pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f = L.schemeKerStr n := by
  calc pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫ f
      = pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
          (L.schemeNsmul n ≫ f) := by rw [RelativeGroupLaw.schemeNsmul_over]
    _ = (pullback.snd (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 ≫
          (L.one (𝟙 (Spec (CommRingCat.of R)))).1) ≫ f := by
        rw [← Category.assoc, pullback.condition]
    _ = L.schemeKerStr n := by
        rw [Category.assoc, (L.one (𝟙 (Spec (CommRingCat.of R)))).2, Category.comp_id]

end E162LVd1

open E162LVd1 in
theorem solution
    {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (n : ℕ) (Z : Set ↥A)
    (W : (L.schemeKer n).Opens)
    (hW : (W : Set ↥(L.schemeKer n))
      = (pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1).base ⁻¹' Z)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : SchemeHomOver t f) :
    FactorsThrough (W.ι ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1) P ↔
      nsmulPt L t n P = L.one t ∧ Set.range P.1.base ⊆ Z := by
  constructor
  · rintro ⟨P₀, hP₀⟩
    refine ⟨?_, ?_⟩
    · rw [nsmulPt_eq_nsmul]
      apply torsion_of_comp_schemeNsmul_eq
      rw [← hP₀]
      simp only [Category.assoc]
      rw [pullback.condition]
      have h := kerFst_comp_f L n
      dsimp only [RelativeGroupLaw.schemeKerStr] at h
      rw [← h]
      simp only [Category.assoc]
    · rintro _ ⟨x, rfl⟩
      have hx : W.ι.base (P₀.base x) ∈ Set.range W.ι.base := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι, hW] at hx
      rw [← hP₀]
      exact hx
  · rintro ⟨htor, hZ⟩
    have hcomm : P.1 ≫ L.schemeNsmul n = t ≫ (L.one (𝟙 (Spec (CommRingCat.of R)))).1 := by
      rw [comp_schemeNsmul_eq_of_torsion L t n P (by rw [← nsmulPt_eq_nsmul]; exact htor), P.2]
    have hκ : pullback.lift P.1 t hcomm ≫
        pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1 = P.1 :=
      pullback.lift_fst _ _ _
    have hrange : Set.range (pullback.lift P.1 t hcomm).base ⊆ Set.range W.ι.base := by
      rw [Scheme.Opens.range_ι, hW]
      rintro _ ⟨x, rfl⟩
      have hx : (pullback.lift P.1 t hcomm ≫
          pullback.fst (L.schemeNsmul n) (L.one (𝟙 (Spec (CommRingCat.of R)))).1).base x ∈ Z := by
        rw [hκ]; exact hZ ⟨x, rfl⟩
      exact hx
    refine ⟨IsOpenImmersion.lift W.ι (pullback.lift P.1 t hcomm) hrange, ?_⟩
    rw [← Category.assoc, IsOpenImmersion.lift_fac, hκ]

end S_GoodReductionJacobian_RelativeGroupLaw_factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_factorsThrough_opens_schemeKer_iff_nsmulPt_eq_one_and_range_subset (solution)
