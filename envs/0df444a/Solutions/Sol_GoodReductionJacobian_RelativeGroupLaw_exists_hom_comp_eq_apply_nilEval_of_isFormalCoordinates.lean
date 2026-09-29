-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/f8c2a3ca-7c7f-5e6b-a147-8647877f5103

import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_MvFormalGroup_PointsV2
import Theorems.Thm_MvFormalGroup_existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent
import Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem HTSu4_isNilpotent_of_mem {C : Type} [CommRing C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    {a : C} (ha : a ∈ J) : IsNilpotent a :=
  ⟨n + 1, by have h := Ideal.pow_mem_pow ha (n + 1); rwa [hJ, Ideal.mem_bot] at h⟩

theorem HTSu4_isNilpotent_ideal {C : Type} [CommRing C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) :
    IsNilpotent J := ⟨n + 1, by rw [hJ]; rfl⟩

theorem HTSu4_exists_pow_succ_eq_bot {C : Type} [CommRing C] (J : Ideal C) (hJ : IsNilpotent J) :
    ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨m, hm⟩ := hJ
  exact ⟨m, by rw [pow_succ, hm]; exact zero_mul _⟩

namespace HTSu4

variable {B : Type} [CommRing B] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)}

def push (h : A ⟶ A') (hh : h ≫ f' = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)}
    (P : SchemeHomOver t f) : SchemeHomOver t f' :=
  ⟨P.1 ≫ h, by rw [Category.assoc, hh, P.2]⟩

theorem push_coe (h : A ⟶ A') (hh : h ≫ f' = f) {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)}
    (P : SchemeHomOver t f) : (push h hh P).1 = P.1 ≫ h := rfl

theorem push_one (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') (h : A ⟶ A') (hh : h ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ h =
        (L'.mul t ⟨P.1 ≫ h, by rw [Category.assoc, hh, P.2]⟩ ⟨Q.1 ≫ h, by rw [Category.assoc, hh, Q.2]⟩).1)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) :
    push h hh (L.one t) = L'.one t := by
  set e : SchemeHomOver t f' := push h hh (L.one t) with he
  have hidem : L'.mul t e e = e := by
    apply Subtype.ext
    have := hhom t (L.one t) (L.one t)
    rw [L.one_mul] at this
    exact this.symm
  calc e = L'.mul t (L'.one t) e := (L'.one_mul t e).symm
    _ = L'.mul t (L'.mul t (L'.inv t e) e) e := by rw [L'.inv_mul_cancel]
    _ = L'.mul t (L'.inv t e) (L'.mul t e e) := L'.mul_assoc t _ _ _
    _ = L'.mul t (L'.inv t e) e := by rw [hidem]
    _ = L'.one t := L'.inv_mul_cancel t e

theorem exists_coords
    (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') {g g' : ℕ} (F : MvFormalGroup g B) (F' : MvFormalGroup g' B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (h : A ⟶ A') (hh : h ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ h =
        (L'.mul t ⟨P.1 ≫ h, by rw [Category.assoc, hh, P.2]⟩ ⟨Q.1 ≫ h, by rw [Category.assoc, hh, Q.2]⟩).1)
    (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (x : Fin g → C)
    (hJ : ∃ n : ℕ, J ^ (n + 1) = ⊥) (hx : ∀ j, x j ∈ J) :
    ∃ s : Fin g' → C, (∀ i, s i ∈ J) ∧ θ' C s = push h hh (θ C x) := by
  obtain ⟨n, hn⟩ := hJ
  refine (hθ'.2 C J n hn).2.2.1 (push h hh (θ C x)) ?_

  have hinf := (hθ.2 C J n hn).1 x hx
  unfold RelativeGroupLaw.IsInfinitesimal at hinf ⊢
  rw [← push_one L L' h hh hhom]
  apply Subtype.ext
  have e1 := congrArg Subtype.val hinf
  simp only [schemeHomOverComp_coe, push_coe] at e1 ⊢
  rw [← Category.assoc, e1]

end HTSu4

open HTSu4 in
theorem solution
    {B : Type} [CommRing B] {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} {f' : A' ⟶ Spec (CommRingCat.of B)}
    (L : RelativeGroupLaw B f) (L' : RelativeGroupLaw B f') {g g' : ℕ} (F : MvFormalGroup g B) (F' : MvFormalGroup g' B)
    (θ : RelativeGroupLaw.FormalCoordinates f g) (θ' : RelativeGroupLaw.FormalCoordinates f' g')
    (hθ : L.IsFormalCoordinates F θ) (hθ' : L'.IsFormalCoordinates F' θ')
    (h : A ⟶ A') (hh : h ≫ f' = f)
    (hhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (P Q : SchemeHomOver t f),
      (L.mul t P Q).1 ≫ h =
        (L'.mul t ⟨P.1 ≫ h, by rw [Category.assoc, hh, P.2]⟩ ⟨Q.1 ≫ h, by rw [Category.assoc, hh, Q.2]⟩).1) :
    ∃ σ : MvFormalGroup.Hom F F',
      (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
        ∀ s : Fin g → B'', (∀ i, s i ∈ J) →
          (θ B'' s).1 ≫ h = (θ' B'' (fun i => MvFormalGroup.nilEval n (σ.toPowerSeries i) s)).1) ∧
      ∀ σ₂ : MvFormalGroup.Hom F F',
        (∀ (B'' : Type) [CommRing B''] [Algebra B B''] (J : Ideal B'') (n : ℕ), J ^ (n + 1) = ⊥ →
          ∀ s : Fin g → B'', (∀ i, s i ∈ J) →
            (θ B'' s).1 ≫ h = (θ' B'' (fun i => MvFormalGroup.nilEval n (σ₂.toPowerSeries i) s)).1) → σ₂ = σ := by
  classical

  let t : ∀ (C : Type) [CommRing C] [Algebra B C], Ideal C → (Fin g → C) → (Fin g' → C) :=
    fun C _ _ J x => if hx : (∃ n : ℕ, J ^ (n + 1) = ⊥) ∧ (∀ j, x j ∈ J) then
      (exists_coords L L' F F' θ θ' hθ hθ' h hh hhom C J x hx.1 hx.2).choose else 0
  have ht : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ x : Fin g → C, (∀ j, x j ∈ J) → (∀ i, t C J x i ∈ J) ∧ θ' C (t C J x) = push h hh (θ C x) := by
    intro C _ _ J n hJ x hx
    have hx' : (∃ n : ℕ, J ^ (n + 1) = ⊥) ∧ (∀ j, x j ∈ J) := ⟨⟨n, hJ⟩, hx⟩
    show (∀ i, (if hx : (∃ n : ℕ, J ^ (n + 1) = ⊥) ∧ (∀ j, x j ∈ J) then
      (exists_coords L L' F F' θ θ' hθ hθ' h hh hhom C J x hx.1 hx.2).choose else 0) i ∈ J) ∧
      θ' C (if hx : (∃ n : ℕ, J ^ (n + 1) = ⊥) ∧ (∀ j, x j ∈ J) then
      (exists_coords L L' F F' θ θ' hθ hθ' h hh hhom C J x hx.1 hx.2).choose else 0) = push h hh (θ C x)
    rw [dif_pos hx']
    exact (exists_coords L L' F F' θ θ' hθ hθ' h hh hhom C J x hx'.1 hx'.2).choose_spec

  have huq : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ), J ^ (n + 1) = ⊥ →
      ∀ (x : Fin g → C) (s : Fin g' → C), (∀ j, x j ∈ J) → (∀ i, s i ∈ J) → θ' C s = push h hh (θ C x) → s = t C J x := by
    intro C _ _ J n hJ x s hx hs hsx
    obtain ⟨htm, hte⟩ := ht C J n hJ x hx
    exact (hθ'.2 C J n hJ).2.1 s (t C J x) hs htm (hsx.trans hte.symm)

  have hmem : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x : Fin g → C, (∀ j, x j ∈ J) → ∀ i, t C J x i ∈ J := by
    intro C _ _ J hJ x hx
    obtain ⟨n, hn⟩ := HTSu4_exists_pow_succ_eq_bot J hJ
    exact (ht C J n hn x hx).1
  have hnat : ∀ (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C']
      (J : Ideal C) (J' : Ideal C'), IsNilpotent J → IsNilpotent J' →
      ∀ φ : C →ₐ[B] C', (∀ s ∈ J, φ s ∈ J') →
        ∀ x : Fin g → C, (∀ j, x j ∈ J) → t C' J' (φ ∘ x) = φ ∘ t C J x := by
    intro C C' _ _ _ _ J J' hJ hJ' φ hφ x hx
    obtain ⟨n, hn⟩ := HTSu4_exists_pow_succ_eq_bot J hJ
    obtain ⟨n', hn'⟩ := HTSu4_exists_pow_succ_eq_bot J' hJ'
    obtain ⟨htm, hte⟩ := ht C J n hn x hx
    symm
    apply huq C' J' n' hn' (φ ∘ x) (φ ∘ t C J x) (fun j => hφ _ (hx j)) (fun i => hφ _ (htm i))
    rw [hθ'.1 C C' φ (t C J x) (fun i => HTSu4_isNilpotent_of_mem J n hn (htm i)), hte,
      hθ.1 C C' φ x (fun i => HTSu4_isNilpotent_of_mem J n hn (hx i))]
    apply Subtype.ext
    simp only [schemeHomOverComp_coe, push_coe, Category.assoc]
  have hadd : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C), IsNilpotent J →
      ∀ x y : Fin g → C, (∀ j, x j ∈ J) → (∀ j, y j ∈ J) →
        t C J (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) =
          fun i => MvFormalGroup.adicEval J (Sum.elim (t C J x) (t C J y)) (F'.toPowerSeries i) := by
    intro C _ _ J hJ x y hx hy
    obtain ⟨n, hn⟩ := HTSu4_exists_pow_succ_eq_bot J hJ
    obtain ⟨htxm, htxe⟩ := ht C J n hn x hx
    obtain ⟨htym, htye⟩ := ht C J n hn y hy
    have hxy : ∀ j, Sum.elim x y j ∈ J := by rintro (j | j); exacts [hx j, hy j]
    have htxy : ∀ j, Sum.elim (t C J x) (t C J y) j ∈ J := by rintro (j | j); exacts [htxm j, htym j]
    have e1 : (fun i => MvFormalGroup.adicEval J (Sum.elim x y) (F.toPowerSeries i)) = F.nilMul n x y := by
      funext i; exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hxy).symm
    have e2 : (fun i => MvFormalGroup.adicEval J (Sum.elim (t C J x) (t C J y)) (F'.toPowerSeries i)) =
        F'.nilMul n (t C J x) (t C J y) := by
      funext i; exact (MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ htxy).symm
    rw [e1, e2]
    have hm1 : ∀ i, F.nilMul n x y i ∈ J := fun i =>
      (MvFormalGroup.nilEval_subst_of_mem J n hn _ hxy F.toPowerSeries F.constantCoeff_eq_zero 0).1 i
    have hm2 : ∀ i, F'.nilMul n (t C J x) (t C J y) i ∈ J := fun i =>
      (MvFormalGroup.nilEval_subst_of_mem J n hn _ htxy F'.toPowerSeries F'.constantCoeff_eq_zero 0).1 i
    symm
    apply huq C J n hn _ _ hm1 hm2
    rw [(hθ'.2 C J n hn).2.2.2 _ _ htxm htym, htxe, htye, (hθ.2 C J n hn).2.2.2 _ _ hx hy]
    apply Subtype.ext
    rw [push_coe]
    exact (hhom _ (θ C x) (θ C y)).symm

  obtain ⟨φ, hφ, hφu⟩ := MvFormalGroup.existsUnique_hom_apply_eq_adicEval_of_natural_of_isNilpotent F F' t hmem hnat hadd
  have hφeval : ∀ (C : Type) [CommRing C] [Algebra B C] (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
      (x : Fin g → C), (∀ j, x j ∈ J) → (fun i => MvFormalGroup.nilEval n (φ.toPowerSeries i) x) = t C J x := by
    intro C _ _ J n hJ x hx
    funext i
    rw [MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hJ _ _ hx]
    exact (hφ C J (HTSu4_isNilpotent_ideal J n hJ) x hx i).symm
  refine ⟨φ, ?_, ?_⟩
  · intro C _ _ J n hJ s hs
    rw [hφeval C J n hJ s hs, (ht C J n hJ s hs).2, push_coe]
  · intro φ₂ hφ₂
    apply hφu
    intro C _ _ J hJ x hx i
    obtain ⟨n, hn⟩ := HTSu4_exists_pow_succ_eq_bot J hJ
    have hm : ∀ j, MvFormalGroup.nilEval n (φ₂.toPowerSeries j) x ∈ J := fun j =>
      (MvFormalGroup.nilEval_subst_of_mem J n hn x hx φ₂.toPowerSeries φ₂.constantCoeff_eq_zero 0).1 j
    have hP : θ' C (fun j => MvFormalGroup.nilEval n (φ₂.toPowerSeries j) x) = push h hh (θ C x) :=
      Subtype.ext (by rw [push_coe]; exact (hφ₂ C J n hn x hx).symm)
    have e := huq C J n hn x _ hx hm hP
    rw [← MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot J n hn _ _ hx]
    exact (congrFun e i).symm

end S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_hom_comp_eq_apply_nilEval_of_isFormalCoordinates (solution)
