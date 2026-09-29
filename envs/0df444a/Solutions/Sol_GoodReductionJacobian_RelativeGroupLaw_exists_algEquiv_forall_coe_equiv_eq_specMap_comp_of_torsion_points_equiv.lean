-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_algEquiv_forall_coe_equiv_eq_specMap_comp_of_torsion_points_equiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/03018c26-11b2-5baf-b013-875a23bd8887

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_CerednikDrinfeld_SchemeNilpPoints
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_algEquiv_forall_coe_equiv_eq_specMap_comp_of_torsion_points_equiv

set_option autoImplicit false

namespace R2HAux
open CategoryTheory AlgebraicGeometry

theorem specMap_ofHom_preimage {R S : Type} [CommRing R] [CommRing S]
    (w : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (Spec.preimage w).hom) = w := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem ringHom_eq_of_specMap_eq {R S : Type} [CommRing R] [CommRing S] (φ ψ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ := by
  have h2 := Spec.map_inj.mp h
  have h3 := congrArg CommRingCat.Hom.hom h2
  simpa only [CommRingCat.hom_ofHom] using h3

theorem fold {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : S →+* T) (b : R →+* S) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = Spec.map (CommRingCat.ofHom (a.comp b)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end R2HAux

namespace R2HAux
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
section GroupLaw
variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)

theorem nsmul_val {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (n : ℕ) (P : SchemeHomOver t f) :
    (L.nsmul t n P).1 = P.1 ≫ L.schemeNsmul n := by
  have h := L.nsmul_natural f t P.1 P.2 n RelativeGroupLaw.idPoint
  have hP : schemeHomOverComp P.1 P.2 (RelativeGroupLaw.idPoint (f := f)) = P := by
    apply Subtype.ext
    rw [schemeHomOverComp_coe]
    exact Category.comp_id _
  rw [hP] at h
  rw [← h, schemeHomOverComp_coe]
  rfl

theorem one_val {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) :
    (L.one t).1 = t ≫ (L.one (𝟙 (Spec (CommRingCat.of B)))).1 := by
  have h := L.one_natural (𝟙 (Spec (CommRingCat.of B))) t t (Category.comp_id t)
  rw [← h, schemeHomOverComp_coe]
end GroupLaw

section Torsion

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f) (n : ℕ)
  (R : Type) [CommRing R] [Algebra B R] (e : Spec (CommRingCat.of R) ≅ L.schemeKer n)
  (he : e.hom ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap B R)))

theorem fst_comp_f : pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f = L.schemeKerStr n := by
  have h1 : pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ f =
      pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1 ≫ (L.schemeNsmul n ≫ f) := by rw [L.schemeNsmul_over]
  rw [h1, ← Category.assoc, pullback.condition, Category.assoc, (L.one (𝟙 _)).2]
  exact Category.comp_id _

include he in

theorem univ_over : (e.hom ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1) ≫ f =
    Spec.map (CommRingCat.ofHom (algebraMap B R)) := by
  rw [Category.assoc, fst_comp_f, he]

noncomputable def univPt (he : e.hom ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap B R))) :
    SchemeHomOver (Scheme.specOver (𝒪 := B) R) f :=
  ⟨e.hom ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1, univ_over L n R e he⟩

theorem univPt_torsion : L.nsmul (Scheme.specOver (𝒪 := B) R) n (univPt L n R e he) =
    L.one (Scheme.specOver (𝒪 := B) R) := by
  apply Subtype.ext
  rw [nsmul_val, one_val]
  show (e.hom ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1) ≫ L.schemeNsmul n =
    Spec.map (CommRingCat.ofHom (algebraMap B R)) ≫ (L.one (𝟙 _)).1
  rw [Category.assoc, pullback.condition, ← Category.assoc, ← he]

theorem exists_classify (C : Type) [CommRing C] [Algebra B C] (Q : SchemeHomOver (Scheme.specOver (𝒪 := B) C) f)
    (hQ : L.nsmul (Scheme.specOver (𝒪 := B) C) n Q = L.one (Scheme.specOver (𝒪 := B) C)) :
    ∃ χ : R →ₐ[B] C, Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ (univPt L n R e he).1 = Q.1 := by
  have w : Q.1 ≫ L.schemeNsmul n = Scheme.specOver (𝒪 := B) C ≫ (L.one (𝟙 _)).1 := by
    rw [← nsmul_val, hQ, one_val]
  let l : Spec (CommRingCat.of C) ⟶ L.schemeKer n := pullback.lift Q.1 (Scheme.specOver (𝒪 := B) C) w
  obtain ⟨χ, hχ⟩ : ∃ χ : R →+* C, Spec.map (CommRingCat.ofHom χ) = l ≫ e.inv := ⟨_, specMap_ofHom_preimage _⟩
  have hcomm : χ.comp (algebraMap B R) = algebraMap B C := by
    apply ringHom_eq_of_specMap_eq
    rw [CommRingCat.ofHom_comp, Spec.map_comp, hχ, ← he, Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
  refine ⟨{ toRingHom := χ, commutes' := fun b => DFunLike.congr_fun hcomm b }, ?_⟩
  show Spec.map (CommRingCat.ofHom χ) ≫ e.hom ≫ pullback.fst _ _ = Q.1
  rw [hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]

include he in

theorem classify_unique (C : Type) [CommRing C] [Algebra B C] (χ₁ χ₂ : R →ₐ[B] C)
    (h : Spec.map (CommRingCat.ofHom χ₁.toRingHom) ≫ (univPt L n R e he).1 =
      Spec.map (CommRingCat.ofHom χ₂.toRingHom) ≫ (univPt L n R e he).1) : χ₁ = χ₂ := by
  have hb : ∀ χ : R →ₐ[B] C, Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap B R)) =
      Spec.map (CommRingCat.ofHom (algebraMap B C)) := fun χ => by
    rw [fold, χ.toRingHom_eq_coe, χ.comp_algebraMap]
  have h' : Spec.map (CommRingCat.ofHom χ₁.toRingHom) ≫ e.hom = Spec.map (CommRingCat.ofHom χ₂.toRingHom) ≫ e.hom := by
    apply pullback.hom_ext
    · simp only [Category.assoc] at h ⊢
      exact h
    · change (_ ≫ e.hom) ≫ L.schemeKerStr n = (_ ≫ e.hom) ≫ L.schemeKerStr n
      rw [Category.assoc, Category.assoc, he, hb, hb]
  rw [cancel_mono] at h'
  apply AlgHom.ext
  intro r
  have := ringHom_eq_of_specMap_eq _ _ h'
  exact DFunLike.congr_fun this r

end Torsion
end R2HAux

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian R2HAux in
theorem solution
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (H : Type) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_nat : ∀ (T T' : Type) [CommRing T] [Algebra K T] [CommRing T'] [Algebra K T']
        (g' : T →ₐ[K] T') (φ : WithConv (H →ₐ[K] T)),
      ((e T' (.toConv (g'.comp φ.ofConv))).val : SchemeHomOver _ f).1 =
        Spec.map (CommRingCat.ofHom g'.toRingHom) ≫ (e T φ).val.1)
    (R : Type) [CommRing R] [Algebra K R] (eR : Spec (CommRingCat.of R) ≅ L.schemeKer n)
    (heR : eR.hom ≫ L.schemeKerStr n = Spec.map (CommRingCat.ofHom (algebraMap K R))) :
    ∃ ι : H ≃ₐ[K] R,
      ∀ (T : Type) [CommRing T] [Algebra K T] (q : H →ₐ[K] T),
        ((e T (.toConv q)).val : SchemeHomOver _ f).1 =
          Spec.map (CommRingCat.ofHom (q.comp (ι.symm : R →ₐ[K] H)).toRingHom) ≫
            (eR.hom ≫ pullback.fst (L.schemeNsmul n) (L.one (𝟙 _)).1) := by
  classical

  let uR : SchemeHomOver (Scheme.specOver (𝒪 := K) R) f := univPt L n R eR heR
  have huR : L.nsmul (Scheme.specOver (𝒪 := K) R) n uR = L.one _ := univPt_torsion L n R eR heR
  let uH := e H (.toConv (AlgHom.id K H))

  let q₁ : WithConv (H →ₐ[K] R) := (e R).symm ⟨uR, huR⟩
  have hq₁ : (e R q₁).val = uR := by simp only [q₁, Equiv.apply_symm_apply]
  let ψ : H →ₐ[K] R := q₁.ofConv

  obtain ⟨χ, hχ⟩ := exists_classify L n R eR heR H uH.val uH.2

  have hnatH : ∀ (T : Type) [CommRing T] [Algebra K T] (q : H →ₐ[K] T),
      ((e T (.toConv q)).val : SchemeHomOver _ f).1 = Spec.map (CommRingCat.ofHom q.toRingHom) ≫ uH.val.1 := by
    intro T _ _ q
    have h := he_nat H T q (.toConv (AlgHom.id K H))
    rw [show WithConv.toConv (q.comp (WithConv.toConv (AlgHom.id K H)).ofConv) = WithConv.toConv q from by
      rw [WithConv.ofConv_toConv, AlgHom.comp_id]] at h
    exact h

  have hA : χ.comp ψ = AlgHom.id K H := by
    have h1 := he_nat R H χ q₁

    have h2 : ((e H (.toConv (χ.comp ψ))).val : SchemeHomOver _ f).1 = uH.val.1 := by
      rw [h1, congrArg Subtype.val hq₁]
      exact hχ
    have h3 : e H (.toConv (χ.comp ψ)) = uH := Subtype.ext (Subtype.ext h2)
    have h4 := (e H).injective h3
    exact congrArg WithConv.ofConv h4

  have hB : ψ.comp χ = AlgHom.id K R := by
    apply classify_unique L n R eR heR R
    rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom, ← fold, Category.assoc]
    change Spec.map (CommRingCat.ofHom (ψ : H →+* R)) ≫ Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ uR.1 = _
    rw [hχ, ← AlgHom.toRingHom_eq_coe, ← hnatH R ψ]
    change (e R (.toConv q₁.ofConv)).val.1 = _
    rw [WithConv.toConv_ofConv, congrArg Subtype.val hq₁]
    have hid : Spec.map (CommRingCat.ofHom (AlgHom.id K R).toRingHom) = 𝟙 _ := by
      change Spec.map (CommRingCat.ofHom (RingHom.id R)) = 𝟙 _
      rw [CommRingCat.ofHom_id]; exact Spec.map_id _
    rw [hid, Category.id_comp]
  let ι : H ≃ₐ[K] R := AlgEquiv.ofAlgHom ψ χ hB hA
  refine ⟨ι, ?_⟩
  intro T _ _ q
  rw [hnatH T q, ← hχ, ← Category.assoc, fold]
  rfl

end S_GoodReductionJacobian_RelativeGroupLaw_exists_algEquiv_forall_coe_equiv_eq_specMap_comp_of_torsion_points_equiv
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_algEquiv_forall_coe_equiv_eq_specMap_comp_of_torsion_points_equiv (solution)
