-- Prove2me | solution 1 for GoodReductionJacobian.BareDeformation.exists_isFormalCoordinates_map_liftsCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/6119791f-4554-565c-9ddc-8682dcff8c82

import Mathlib
import Definitions.Def_GoodReductionJacobian_BareDeformation
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

noncomputable section

namespace E2Bridge

variable {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')

abbrev paBase (C : Type) [CommRing C] [Algebra R' C] : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom ((algebraMap R' C).comp φ))

theorem specOver_comp (C : Type) [CommRing C] [Algebra R' C] :
    Scheme.specOver (𝒪 := R') C ≫ Spec.map (CommRingCat.ofHom φ) = paBase φ C := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

section Congr

variable {S : Type} [CommRing S] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of S)} (L : RelativeGroupLaw S f)

theorem one_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t') :
    (L.one t).1 = (L.one t').1 := by
  subst h; rfl

theorem mul_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of S)} (h : t = t')
    (P Q : SchemeHomOver t f) (P' Q' : SchemeHomOver t' f) (hP : P.1 = P'.1) (hQ : Q.1 = Q'.1) :
    (L.mul t P Q).1 = (L.mul t' P' Q').1 := by
  subst h
  obtain rfl : P = P' := Subtype.ext hP
  obtain rfl : Q = Q' := Subtype.ext hQ
  rfl

theorem eq_one_of_mul_self {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of S)) (x : SchemeHomOver t f)
    (hx : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [hx]
    _ = L.one t := L.inv_mul_cancel t x

theorem isInfinitesimal_iff_val {C : Type} [CommRing C] [Algebra S C] (J : Ideal C)
    (P : SchemeHomOver (Scheme.specOver (𝒪 := S) C) f) :
    L.IsInfinitesimal J P ↔
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ P.1 =
        (L.one (Scheme.specOver (𝒪 := S) (C ⧸ J))).1 :=
  ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem specMap_mk_comp_specOver {C : Type} [CommRing C] [Algebra S C] (J : Ideal C) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ Scheme.specOver (𝒪 := S) C =
      Scheme.specOver (𝒪 := S) (C ⧸ J) :=
  Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ S J)

end Congr

section Nil

variable {C : Type} [CommRing C]

theorem exists_pow_succ_eq_bot {J : Ideal C} (hJ : IsNilpotent J) : ∃ n : ℕ, J ^ (n + 1) = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  exact ⟨n, by rw [pow_succ, hn, zero_mul]; rfl⟩

theorem isNilpotent_of_mem {J : Ideal C} (hJ : IsNilpotent J) {x : C} (hx : x ∈ J) : IsNilpotent x := by
  obtain ⟨n, hn⟩ := hJ
  refine ⟨n, ?_⟩
  have : x ^ n ∈ J ^ n := Ideal.pow_mem_pow hx n
  rw [hn] at this
  exact (Submodule.mem_bot C).1 this

theorem isNilpotent_span_range {n : ℕ} (s : Fin n → C) (hs : ∀ i, IsNilpotent (s i)) :
    IsNilpotent (Ideal.span (Set.range s)) := by
  classical
  have hle : Ideal.span (Set.range s) ≤ (⊥ : Ideal C).radical := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hs i
    exact ⟨k, by rw [hk]; exact Submodule.zero_mem _⟩
  obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hle
    (Submodule.fg_span (Set.finite_range s))
  exact ⟨k, le_bot_iff.1 hk⟩

theorem isAdicComplete_of_isNilpotent (J : Ideal C) (hJ : IsNilpotent J) : IsAdicComplete J C := by
  obtain ⟨n, hn⟩ := hJ
  haveI : IsHausdorff J C := ⟨fun x hx => by
    have := hx n
    rw [hn] at this
    simpa [SModEq.zero] using this⟩
  haveI : IsPrecomplete J C := ⟨fun {f} hf => ⟨f n, fun m => by
    by_cases hm : m ≤ n
    · exact hf hm
    · push Not at hm
      have h1 : f n ≡ f m [SMOD (J ^ n • ⊤ : Submodule C C)] := hf hm.le
      have h2 : (J ^ m • ⊤ : Submodule C C) = ⊥ := by
        rw [show m = n + (m - n) by omega, pow_add, hn, zero_mul]; simp
      have h3 : (J ^ n • ⊤ : Submodule C C) = ⊥ := by rw [hn]; simp
      rw [h2]; rw [h3] at h1
      exact h1.symm⟩⟩
  exact ⟨⟩

theorem aeval_mem_of_coeff_zero {S : Type} [CommRing S] [Algebra S C] {σ : Type} (J : Ideal C)
    (p : MvPolynomial σ S) (hp : p.coeff 0 = 0) (a : σ → C) (ha : ∀ i, a i ∈ J) : MvPolynomial.aeval a p ∈ J := by
  classical
  rw [p.as_sum, map_sum]
  refine Ideal.sum_mem _ fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]
  by_cases hd0 : d = 0
  · subst hd0
    rw [hp, map_zero, zero_mul]
    exact J.zero_mem
  · obtain ⟨s, hs⟩ : ∃ s, d s ≠ 0 := by
      by_contra h
      push Not at h
      exact hd0 (Finsupp.ext fun s => by simpa using h s)
    refine Ideal.mul_mem_left _ _ ?_
    rw [Finsupp.prod, ← Finset.mul_prod_erase _ _ (Finsupp.mem_support_iff.mpr hs)]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hk, pow_succ]
    exact Ideal.mul_mem_left _ _ (ha s)

theorem nilEval_mem {S : Type} [CommRing S] [Algebra S C] {σ : Type} [Fintype σ] [DecidableEq σ] (J : Ideal C)
    (n : ℕ) (φ : MvPowerSeries σ S) (hφ : MvPowerSeries.constantCoeff φ = 0) (a : σ → C) (ha : ∀ i, a i ∈ J) :
    MvFormalGroup.nilEval n φ a ∈ J := by
  unfold MvFormalGroup.nilEval
  refine aeval_mem_of_coeff_zero J _ ?_ a ha
  rw [MvPowerSeries.coeff_trunc', if_pos (Finsupp.le_def.2 fun _ => Nat.zero_le _),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hφ]

end Nil

section Transport

variable {A A' : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} {f' : A' ⟶ Spec (CommRingCat.of R')}
  (g : A' ⟶ A) (hg : IsPullback g f' f (Spec.map (CommRingCat.ofHom φ)))

include hg in
theorem ext_of_comp_eq {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of R')} (P Q : SchemeHomOver t f')
    (h : P.1 ≫ g = Q.1 ≫ g) : P = Q :=
  Subtype.ext (hg.hom_ext h (by rw [P.2, Q.2]))

def down {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (Scheme.specOver (𝒪 := R') C) f') :
    SchemeHomOver (paBase φ C) f :=
  ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2, specOver_comp]⟩

@[scoped simp] theorem down_val {C : Type} [CommRing C] [Algebra R' C]
    (P : SchemeHomOver (Scheme.specOver (𝒪 := R') C) f') : (down φ g hg P).1 = P.1 ≫ g := rfl

def up {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (paBase φ C) f) :
    SchemeHomOver (Scheme.specOver (𝒪 := R') C) f' :=
  ⟨hg.lift P.1 (Scheme.specOver (𝒪 := R') C) (by rw [P.2, specOver_comp]), hg.lift_snd _ _ _⟩

@[scoped simp] theorem up_val_comp {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (paBase φ C) f) :
    (up φ g hg P).1 ≫ g = P.1 :=
  hg.lift_fst _ _ _

theorem up_down {C : Type} [CommRing C] [Algebra R' C] (P : SchemeHomOver (Scheme.specOver (𝒪 := R') C) f') :
    up φ g hg (down φ g hg P) = P :=
  ext_of_comp_eq φ g hg _ _ (by rw [up_val_comp, down_val])

variable (L : RelativeGroupLaw R f) (L' : RelativeGroupLaw R' f')

def IsMulCompat : Prop :=
  ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) (P Q : SchemeHomOver t' f'),
    (L'.mul t' P Q).1 ≫ g =
      (L.mul (t' ≫ Spec.map (CommRingCat.ofHom φ))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

variable {L L'}

theorem one_val_comp (hmul : IsMulCompat φ g hg L L') {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (L'.one t').1 ≫ g = (L.one (t' ≫ Spec.map (CommRingCat.ofHom φ))).1 := by
  have h := hmul t' (L'.one t') (L'.one t')
  rw [L'.mul_one] at h
  have hx := eq_one_of_mul_self L _
    (⟨(L'.one t').1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, (L'.one t').2]⟩ :
      SchemeHomOver (t' ≫ Spec.map (CommRingCat.ofHom φ)) f)
    (Subtype.ext h.symm)
  exact congrArg Subtype.val hx

theorem quotBase_eq (C : Type) [CommRing C] [Algebra R' C] (J : Ideal C) :
    Spec.map (CommRingCat.ofHom ((Ideal.Quotient.mk J).comp ((algebraMap R' C).comp φ))) =
      Scheme.specOver (𝒪 := R') (C ⧸ J) ≫ Spec.map (CommRingCat.ofHom φ) := by
  rw [specOver_comp]

end Transport

end E2Bridge
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates.E2Bridge"

theorem E2Aux_nilEval_map {σ : Type} [Fintype σ] [DecidableEq σ] {B B₁ C : Type} [CommRing B] [CommRing B₁] [CommRing C]
    [Algebra B B₁] [Algebra B₁ C] [Algebra B C] [IsScalarTower B B₁ C] (n : ℕ) (φ : MvPowerSeries σ B) (s : σ → C) :
    MvFormalGroup.nilEval n (MvPowerSeries.map (algebraMap B B₁) φ) s = MvFormalGroup.nilEval n φ s := by
  unfold MvFormalGroup.nilEval
  rw [MvPowerSeries.trunc'_map, MvPolynomial.aeval_map_algebraMap]

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates.E2Bridge"

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

theorem solution
    (B B₁ : Type) [CommRing B] [CommRing B₁] [Algebra B B₁]
    {A₁ : Scheme.{0}} {f₁ : A₁ ⟶ Spec (CommRingCat.of B₁)} {L₁ : RelativeGroupLaw B₁ f₁}
    (D : BareDeformation f₁ L₁ B) {g : ℕ} (F : MvFormalGroup g B)
    (θ : RelativeGroupLaw.FormalCoordinates D.f g) (hθ : D.L.IsFormalCoordinates F θ) :
    ∃ θ₁ : RelativeGroupLaw.FormalCoordinates f₁ g,
      L₁.IsFormalCoordinates (F.map (algebraMap B B₁)) θ₁ ∧ D.LiftsCoordinates θ₁ θ := by
  classical

  let θ₁ : RelativeGroupLaw.FormalCoordinates f₁ g := fun C _ _ s =>
    letI : Algebra B C := ((algebraMap B₁ C).comp (algebraMap B B₁)).toAlgebra
    E2Bridge.up (algebraMap B B₁ : B →+* B₁) D.g D.cart (θ C s)
  have hθ₁g : ∀ (C : Type) [CommRing C] [Algebra B₁ C] (s : Fin g → C),
      (θ₁ C s).1 ≫ D.g = (@θ C _ ((algebraMap B₁ C).comp (algebraMap B B₁)).toAlgebra s).1 := by
    intro C _ _ s
    exact E2Bridge.up_val_comp (algebraMap B B₁ : B →+* B₁) D.g D.cart _
  have hmul : E2Bridge.IsMulCompat (algebraMap B B₁ : B →+* B₁) D.g D.cart D.L L₁ := fun t' P Q => D.hom t' P Q
  refine ⟨θ₁, ⟨?_, ?_⟩, ?_⟩
  ·
    intro C _ _ C' _ _ ψ s hs
    letI iC : Algebra B C := ((algebraMap B₁ C).comp (algebraMap B B₁)).toAlgebra
    letI iC' : Algebra B C' := ((algebraMap B₁ C').comp (algebraMap B B₁)).toAlgebra
    haveI : IsScalarTower B B₁ C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : IsScalarTower B B₁ C' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    apply E2Bridge.ext_of_comp_eq (algebraMap B B₁ : B →+* B₁) D.g D.cart
    rw [hθ₁g, schemeHomOverComp_coe, Category.assoc, hθ₁g]
    have h := hθ.1 C C' (ψ.restrictScalars B) s hs
    exact congrArg Subtype.val h
  · intro C _ _ J n hJ
    letI iC : Algebra B C := ((algebraMap B₁ C).comp (algebraMap B B₁)).toAlgebra
    haveI : IsScalarTower B B₁ C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    obtain ⟨hinto, hinj, honto, hhom⟩ := hθ.2 C J n hJ
    have hbase : Scheme.specOver (𝒪 := B₁) C ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁ : B →+* B₁)) =
        Scheme.specOver (𝒪 := B) C := E2Bridge.specOver_comp (algebraMap B B₁ : B →+* B₁) C
    have hbaseq : Scheme.specOver (𝒪 := B₁) (C ⧸ J) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₁ : B →+* B₁)) =
        Scheme.specOver (𝒪 := B) (C ⧸ J) := E2Bridge.specOver_comp (algebraMap B B₁ : B →+* B₁) (C ⧸ J)
    refine ⟨?_, ?_, ?_, ?_⟩
    ·
      intro s hs
      have h := (E2Bridge.isInfinitesimal_iff_val D.L J (θ C s)).1 (hinto s hs)
      rw [E2Bridge.isInfinitesimal_iff_val]
      apply D.cart.hom_ext
      · rw [Category.assoc, hθ₁g, h, E2Bridge.one_val_comp (algebraMap B B₁ : B →+* B₁) D.g D.cart hmul]
        exact E2Bridge.one_val_congr D.L hbaseq.symm
      · rw [Category.assoc, (θ₁ C s).2, (L₁.one (Scheme.specOver (𝒪 := B₁) (C ⧸ J))).2,
          E2Bridge.specMap_mk_comp_specOver]
    ·
      intro s t hs ht hst
      apply hinj s t hs ht
      apply Subtype.ext
      rw [← hθ₁g, ← hθ₁g, hst]
    ·
      intro P hP
      have hPval := (E2Bridge.isInfinitesimal_iff_val L₁ J P).1 hP
      have hd : D.L.IsInfinitesimal J (E2Bridge.down (algebraMap B B₁ : B →+* B₁) D.g D.cart P) := by
        rw [E2Bridge.isInfinitesimal_iff_val]
        rw [E2Bridge.down_val, ← Category.assoc, hPval, E2Bridge.one_val_comp (algebraMap B B₁ : B →+* B₁) D.g D.cart hmul]
        exact E2Bridge.one_val_congr D.L hbaseq
      obtain ⟨s, hs, hθs⟩ := honto _ hd
      refine ⟨s, hs, ?_⟩
      apply E2Bridge.ext_of_comp_eq (algebraMap B B₁ : B →+* B₁) D.g D.cart
      rw [hθ₁g, hθs, E2Bridge.down_val]
    ·
      intro s t hs ht
      apply E2Bridge.ext_of_comp_eq (algebraMap B B₁ : B →+* B₁) D.g D.cart
      have hnm : (F.map (algebraMap B B₁)).nilMul n s t = F.nilMul n s t := by
        funext i
        exact E2Aux_nilEval_map n (F.toPowerSeries i) (Sum.elim s t)
      rw [hnm, hθ₁g, hhom s t hs ht, hmul]
      apply E2Bridge.mul_val_congr
      · exact hbase.symm
      · exact (hθ₁g C s).symm
      · exact (hθ₁g C t).symm
  ·
    intro C _ instB instB₁ instST s hs
    have e : instB = ((algebraMap B₁ C).comp (algebraMap B B₁)).toAlgebra :=
      Algebra.algebra_ext _ _ (fun r => IsScalarTower.algebraMap_apply B B₁ C r)
    subst e
    exact hθ₁g C s

end S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates
end P2MW
export P2MW.S_GoodReductionJacobian_BareDeformation_exists_isFormalCoordinates_map_liftsCoordinates (solution)
