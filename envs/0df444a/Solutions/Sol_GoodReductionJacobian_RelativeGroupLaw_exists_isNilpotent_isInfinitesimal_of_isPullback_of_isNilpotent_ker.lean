-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/46665d5d-5580-5201-8022-41163cad1110

import Mathlib
import Definitions.Def_CerednikDrinfeld_QMFormalModuleOf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian QuaternionAlgebra CerednikDrinfeld CerednikDrinfeld.QM CerednikDrinfeld.SpecialFormal

open scoped Quaternion TensorProduct NumberField

noncomputable section

namespace InfTransferAux

section Generic

variable {R : Type} [CommRing R] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)}

theorem nsmulPt_zero (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) : nsmulPt L t 0 x = L.one t := rfl

theorem nsmulPt_succ (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (n : ℕ) (x : SchemeHomOver t f) : nsmulPt L t (n + 1) x = L.mul t (nsmulPt L t n x) x := rfl

theorem nsmulPt_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) (n : ℕ) :
    schemeHomOverComp ψ hψ (nsmulPt L t n x) = nsmulPt L t' n (schemeHomOverComp ψ hψ x) := by
  induction n with
  | zero => exact L.one_natural t t' ψ hψ
  | succ n ih => rw [nsmulPt_succ, nsmulPt_succ, L.mul_natural, ih]

theorem eq_one_of_mul_self (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver t f) (h : L.mul t x x = x) : x = L.one t := by
  calc x = L.mul t (L.one t) x := (L.one_mul t x).symm
    _ = L.mul t (L.mul t (L.inv t x) x) x := by rw [L.inv_mul_cancel]
    _ = L.mul t (L.inv t x) (L.mul t x x) := by rw [L.mul_assoc]
    _ = L.mul t (L.inv t x) x := by rw [h]
    _ = L.one t := L.inv_mul_cancel t x

theorem one_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of R)} (h : t = t') :
    (L.one t).1 = (L.one t').1 := by
  subst h; rfl

end Generic

theorem cancel_specMap_ringEquiv {X : Scheme.{0}} {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S)
    {a b : Spec (CommRingCat.of R) ⟶ X}
    (h : Spec.map (CommRingCat.ofHom e.toRingHom) ≫ a = Spec.map (CommRingCat.ofHom e.toRingHom) ≫ b) : a = b := by
  have key : Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom e.toRingHom) = 𝟙 _ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingEquiv.symm_toRingHom_comp_toRingHom, CommRingCat.ofHom_id,
      Spec.map_id]
  have h2 := congrArg (fun k => Spec.map (CommRingCat.ofHom e.symm.toRingHom) ≫ k) h
  simpa only [← Category.assoc, key, Category.id_comp] using h2

theorem specOver_tower (B B₀ C₀ : Type) [CommRing B] [CommRing B₀] [CommRing C₀] [Algebra B B₀] [Algebra B₀ C₀]
    [Algebra B C₀] [IsScalarTower B B₀ C₀] :
    Scheme.specOver (𝒪 := B₀) C₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) = Scheme.specOver (𝒪 := B) C₀ := by
  rw [Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

section Transport

variable {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
  {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)
  {A₀ : Scheme.{0}} {f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)} (L₀ : RelativeGroupLaw B₀ f₀)
  (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))

def gPt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B₀)} (p : SchemeHomOver t f₀) :
    SchemeHomOver (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) f :=
  ⟨p.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, p.2]⟩

@[scoped simp] theorem gPt_val {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B₀)} (p : SchemeHomOver t f₀) :
    (gPt g hg p).1 = p.1 ≫ g := rfl

include hg in
theorem gPt_injective {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B₀)} (p p' : SchemeHomOver t f₀)
    (h : gPt g hg p = gPt g hg p') : p = p' :=
  Subtype.ext (hg.hom_ext (congrArg Subtype.val h) (by rw [p.2, p'.2]))

def IsMulCompat : Prop :=
  ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
    (L₀.mul t P Q).1 ≫ g =
      (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
        ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
        ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1

variable {L L₀}

theorem gPt_mul (hmul : IsMulCompat L L₀ g hg) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀))
    (P Q : SchemeHomOver t f₀) :
    gPt g hg (L₀.mul t P Q) = L.mul _ (gPt g hg P) (gPt g hg Q) :=
  Subtype.ext (hmul t P Q)

theorem gPt_one (hmul : IsMulCompat L L₀ g hg) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) :
    gPt g hg (L₀.one t) = L.one (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) := by
  apply eq_one_of_mul_self
  rw [← gPt_mul g hg hmul, L₀.one_mul]

theorem gPt_nsmul (hmul : IsMulCompat L L₀ g hg) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀))
    (p : SchemeHomOver t f₀) (n : ℕ) :
    gPt g hg (nsmulPt L₀ t n p) = nsmulPt L (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) n (gPt g hg p) := by
  induction n with
  | zero => exact gPt_one g hg hmul t
  | succ n ih => rw [nsmulPt_succ, nsmulPt_succ, gPt_mul g hg hmul, ih]

end Transport

end InfTransferAux
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker.InfTransferAux"

open InfTransferAux

theorem solution
    (q : ℕ) (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) (hker : IsNilpotent (RingHom.ker (algebraMap B B₀)))
    {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of B)) (L : RelativeGroupLaw B f)
    {A₀ : Scheme.{0}} (f₀ : A₀ ⟶ Spec (CommRingCat.of B₀)) (L₀ : RelativeGroupLaw B₀ f₀)
    (g : A₀ ⟶ A) (hg : IsPullback g f₀ f (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (hgmul : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B₀)) (P Q : SchemeHomOver t f₀),
      (L₀.mul t P Q).1 ≫ g =
        (L.mul (t ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))
          ⟨P.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, P.2]⟩
          ⟨Q.1 ≫ g, by rw [Category.assoc, hg.w, ← Category.assoc, Q.2]⟩).1)
    (hinf₀ : ∀ (C : Type) [CommRing C] [Algebra B₀ C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B₀) C) f₀),
      nsmulPt L₀ (Scheme.specOver (𝒪 := B₀) C) (q ^ m) P = L₀.one (Scheme.specOver (𝒪 := B₀) C) →
        ∃ J : Ideal C, IsNilpotent J ∧ L₀.IsInfinitesimal J P)
    (C : Type) [CommRing C] [Algebra B C] (m : ℕ) (P : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f)
    (hP : nsmulPt L (Scheme.specOver (𝒪 := B) C) (q ^ m) P = L.one (Scheme.specOver (𝒪 := B) C)) :
    ∃ J : Ideal C, IsNilpotent J ∧ L.IsInfinitesimal J P := by
  classical
  have hmul : IsMulCompat L L₀ g hg := hgmul

  obtain ⟨kI, hkI⟩ := hker
  set IC : Ideal C := (RingHom.ker (algebraMap B B₀)).map (algebraMap B C) with hICdef
  have hICnil : ∃ b : ℕ, IC ^ b = ⊥ :=
    ⟨kI, by rw [hICdef, ← Ideal.map_pow, hkI, Ideal.zero_eq_bot, Ideal.map_bot]⟩

  have hkerle : RingHom.ker (algebraMap B B₀) ≤ RingHom.ker ((Ideal.Quotient.mk IC).comp (algebraMap B C)) := by
    intro x hx
    rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hICdef]
    exact Ideal.mem_map_of_mem _ hx
  let φ₀ : B₀ →+* C ⧸ IC :=
    (algebraMap B B₀).liftOfSurjective hπ ⟨(Ideal.Quotient.mk IC).comp (algebraMap B C), hkerle⟩
  have hφ₀ : ∀ x : B, φ₀ (algebraMap B B₀ x) = Ideal.Quotient.mk IC (algebraMap B C x) :=
    fun x => (algebraMap B B₀).liftOfSurjective_comp_apply hπ ⟨_, hkerle⟩ x
  letI instB₀C₀ : Algebra B₀ (C ⧸ IC) := φ₀.toAlgebra
  haveI : IsScalarTower B B₀ (C ⧸ IC) := IsScalarTower.of_algebraMap_eq (fun x => (hφ₀ x).symm)

  set ψ : Spec (CommRingCat.of (C ⧸ IC)) ⟶ Spec (CommRingCat.of C) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B IC).toRingHom) with hψdef
  have hψ : ψ ≫ Scheme.specOver (𝒪 := B) C = (Scheme.specOver (𝒪 := B₀) (C ⧸ IC)) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) := by
    rw [hψdef, Scheme.specMap_algHom_comp_specOver, specOver_tower]

  set Pbar : SchemeHomOver ((Scheme.specOver (𝒪 := B₀) (C ⧸ IC)) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) f := schemeHomOverComp ψ hψ P
    with hPbar
  have hPbar_tors : nsmulPt L _ (q ^ m) Pbar = L.one _ := by
    rw [hPbar, ← nsmulPt_natural, hP, L.one_natural]
  let p₀ : SchemeHomOver (Scheme.specOver (𝒪 := B₀) (C ⧸ IC)) f₀ := ⟨hg.lift Pbar.1 (Scheme.specOver (𝒪 := B₀) (C ⧸ IC)) Pbar.2, hg.lift_snd _ _ _⟩
  have hp₀ : gPt g hg p₀ = Pbar := Subtype.ext (hg.lift_fst _ _ _)
  have hp₀_tors : nsmulPt L₀ (Scheme.specOver (𝒪 := B₀) (C ⧸ IC)) (q ^ m) p₀ = L₀.one (Scheme.specOver (𝒪 := B₀) (C ⧸ IC)) := by
    apply gPt_injective g hg
    rw [gPt_nsmul g hg hmul, gPt_one g hg hmul, hp₀, hPbar_tors]

  obtain ⟨J₀, ⟨a, ha⟩, hJ₀⟩ := hinf₀ (C ⧸ IC) m p₀ hp₀_tors

  set χ : C →+* (C ⧸ IC) ⧸ J₀ := (Ideal.Quotient.mk J₀).comp (Ideal.Quotient.mk IC) with hχdef
  have hχ : Function.Surjective χ := Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hJ : RingHom.ker χ = J₀.comap (Ideal.Quotient.mk IC) := by
    rw [hχdef, ← RingHom.comap_ker, Ideal.mk_ker]
  obtain ⟨b, hb⟩ := hICnil
  refine ⟨RingHom.ker χ, ⟨a * b, ?_⟩, ?_⟩
  ·
    rw [Ideal.zero_eq_bot, ← le_bot_iff, pow_mul, hJ]
    have hle : J₀.comap (Ideal.Quotient.mk IC) ^ a ≤ IC := by
      refine (Ideal.le_comap_pow _ a).trans ?_
      rw [ha, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact (Ideal.pow_right_mono hle b).trans hb.le
  ·
    set e : C ⧸ RingHom.ker χ ≃+* (C ⧸ IC) ⧸ J₀ := χ.quotientKerEquivOfSurjective hχ with hedef
    unfold GoodReductionJacobian.RelativeGroupLaw.IsInfinitesimal
    apply Subtype.ext
    apply cancel_specMap_ringEquiv e

    have hSpecχ : Spec.map (CommRingCat.ofHom e.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B (RingHom.ker χ)).toRingHom) =
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B₀ J₀).toRingHom) ≫ ψ := by
      rw [hψdef, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
    have hJ₀val : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B₀ J₀).toRingHom) ≫ p₀.1 =
        (L₀.one (Scheme.specOver (𝒪 := B₀) ((C ⧸ IC) ⧸ J₀))).1 := by
      have := congrArg Subtype.val hJ₀
      rwa [schemeHomOverComp_coe] at this
    have hone : (L₀.one (Scheme.specOver (𝒪 := B₀) ((C ⧸ IC) ⧸ J₀))).1 ≫ g =
        (L.one (Scheme.specOver (𝒪 := B₀) ((C ⧸ IC) ⧸ J₀) ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))).1 :=
      congrArg Subtype.val (gPt_one g hg hmul _)
    have hlift : ψ ≫ P.1 = p₀.1 ≫ g := (hg.lift_fst _ _ _).symm
    rw [schemeHomOverComp_coe, ← Category.assoc, hSpecχ, Category.assoc, hlift, ← Category.assoc, hJ₀val, hone]

    rw [show Spec.map (CommRingCat.ofHom e.toRingHom) ≫ (L.one (Scheme.specOver (𝒪 := B) (C ⧸ RingHom.ker χ))).1 =
        (L.one (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ Scheme.specOver (𝒪 := B) (C ⧸ RingHom.ker χ))).1 from
      congrArg Subtype.val (L.one_natural _ _ (Spec.map (CommRingCat.ofHom e.toRingHom)) rfl)]
    apply one_val_congr
    rw [specOver_tower, Scheme.specOver, Scheme.specOver, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2

end
p2m_reactivate "P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker.InfTransferAux"

end S_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isNilpotent_isInfinitesimal_of_isPullback_of_isNilpotent_ker (solution)
