-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4e8cc289-4ccb-53ea-aa7e-fb5e9a78d107

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one

set_option autoImplicit false
set_option maxHeartbeats 800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one.GoodReductionJacobian"

universe u

namespace GoodReductionJacobian
p2m_export "GoodReductionJacobian" "schemeHomOverComp RelativeGroupLaw"
namespace RelativeGroupLaw
p2m_export "GoodReductionJacobian.RelativeGroupLaw" "nsmul nsmul_zero nsmul_succ nsmul_natural idPoint schemeNsmul schemeNsmul_over pointGroup mul_inv_cancel one mul"
p2m_open "GoodReductionJacobian.RelativeGroupLaw GoodReductionJacobian"

theorem nsmul_coe_eq_comp_schemeNsmul'' {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} (n : ℕ) (x : SchemeHomOver t f) :
    (G.nsmul t n x).1 = x.1 ≫ G.schemeNsmul n := by
  have hid : schemeHomOverComp x.1 x.2 (idPoint (f := f)) = x := Subtype.ext (Category.comp_id x.1)
  have h : schemeHomOverComp x.1 x.2 (G.nsmul f n idPoint) = G.nsmul t n (schemeHomOverComp x.1 x.2 idPoint) :=
    G.nsmul_natural f t x.1 x.2 n idPoint
  rw [hid] at h
  exact (congrArg Subtype.val h).symm

theorem locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ)
    (hinj : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k K))) f),
      G.nsmul _ n x = G.one _ → x = G.one _) :
    LocallyQuasiFinite (G.schemeNsmul n) := by

  haveI : LocallyOfFiniteType (G.schemeNsmul n) := by
    have : LocallyOfFiniteType (G.schemeNsmul n ≫ f) := by rw [G.schemeNsmul_over]; infer_instance
    exact locallyOfFiniteType_of_comp _ f

  suffices h : UniversallyInjective (G.schemeNsmul n) by infer_instance
  rw [UniversallyInjective.iff_diagonal]
  refine ⟨fun z => ?_⟩

  let P := pullback (G.schemeNsmul n) (G.schemeNsmul n)
  let w : Spec (P.residueField z) ⟶ P := P.fromSpecResidueField z
  let x₁ : Spec (P.residueField z) ⟶ A := w ≫ pullback.fst _ _
  let x₂ : Spec (P.residueField z) ⟶ A := w ≫ pullback.snd _ _
  have h12 : x₁ ≫ G.schemeNsmul n = x₂ ≫ G.schemeNsmul n := by
    simp only [x₁, x₂, Category.assoc, pullback.condition]
  let t : Spec (P.residueField z) ⟶ Spec (CommRingCat.of k) := x₁ ≫ f
  have ht₂ : x₂ ≫ f = t := by
    show x₂ ≫ f = x₁ ≫ f
    rw [← G.schemeNsmul_over n, ← Category.assoc, ← h12, Category.assoc]
  let X₁ : SchemeHomOver t f := ⟨x₁, rfl⟩
  let X₂ : SchemeHomOver t f := ⟨x₂, ht₂⟩
  have hN : G.nsmul t n X₁ = G.nsmul t n X₂ :=
    Subtype.ext (by rw [nsmul_coe_eq_comp_schemeNsmul'', nsmul_coe_eq_comp_schemeNsmul'']; exact h12)

  let K : Type u := AlgebraicClosure (P.residueField z)
  let j : Spec (CommRingCat.of K) ⟶ Spec (P.residueField z) :=
    Spec.map (CommRingCat.ofHom (algebraMap (P.residueField z) K))
  haveI : Surjective j := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  haveI : Epi j := Flat.epi_of_flat_of_surjective j
  let Y₁ : SchemeHomOver (j ≫ t) f := GoodReductionJacobian.schemeHomOverComp j rfl X₁
  let Y₂ : SchemeHomOver (j ≫ t) f := GoodReductionJacobian.schemeHomOverComp j rfl X₂
  have hY : G.nsmul (j ≫ t) n Y₁ = G.nsmul (j ≫ t) n Y₂ := by
    rw [← G.nsmul_natural t (j ≫ t) j rfl n X₁, ← G.nsmul_natural t (j ≫ t) j rfl n X₂, hN]

  obtain ⟨φ, hφ⟩ : ∃ φ : CommRingCat.of k ⟶ CommRingCat.of K, Spec.map φ = j ≫ t :=
    ⟨Spec.preimage (j ≫ t), Spec.map_preimage _⟩
  letI : Algebra k K := φ.hom.toAlgebra
  have hφ' : Spec.map (CommRingCat.ofHom (algebraMap k K)) = j ≫ t := by rw [← hφ]; rfl
  have hinj' : ∀ x : SchemeHomOver (j ≫ t) f, G.nsmul _ n x = G.one _ → x = G.one _ := by
    have h := hinj K
    rw [hφ'] at h
    exact h

  have hYeq : Y₁ = Y₂ := by
    letI : CommGroup (SchemeHomOver (j ≫ t) f) := { G.pointGroup (j ≫ t) with mul_comm := hcomm (j ≫ t) }
    have hpow : ∀ (m : ℕ) (x : SchemeHomOver (j ≫ t) f), G.nsmul (j ≫ t) m x = x ^ m := by
      intro m x
      induction m with
      | zero => rw [nsmul_zero, pow_zero]; rfl
      | succ m ih => rw [nsmul_succ, pow_succ, ih]; rfl
    have h1 : G.nsmul (j ≫ t) n (Y₁ * Y₂⁻¹) = G.one (j ≫ t) := by
      rw [hpow, mul_pow, inv_pow, ← hpow, ← hpow, hY]
      exact _root_.mul_inv_cancel _
    have h2 := hinj' (Y₁ * Y₂⁻¹) h1
    exact mul_inv_eq_one.mp h2

  have hx : x₁ = x₂ := by
    have h := congrArg Subtype.val hYeq
    exact (cancel_epi j).1 h

  refine ⟨x₁ (default : ↥(Spec (P.residueField z))), ?_⟩
  have hw : x₁ ≫ pullback.diagonal (G.schemeNsmul n) = w := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hx]
  have hz : (x₁ ≫ pullback.diagonal (G.schemeNsmul n)) (default : ↥(Spec (P.residueField z))) = z := by
    rw [hw]
    exact Scheme.fromSpecResidueField_apply z _
  simpa using hz

end GoodReductionJacobian.RelativeGroupLaw

theorem solution
    {k : Type u} [Field k] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of k)} [LocallyOfFiniteType f]
    (G : RelativeGroupLaw k f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of k)) (x y : SchemeHomOver t f),
      G.mul t x y = G.mul t y x)
    (n : ℕ)
    (hinj : ∀ (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K]
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap k K))) f),
      G.nsmul _ n x = G.one _ → x = G.one _) :
    LocallyQuasiFinite (G.schemeNsmul n) :=
  GoodReductionJacobian.RelativeGroupLaw.locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one G hcomm n hinj

end S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_locallyQuasiFinite_schemeNsmul_of_forall_nsmul_eq_one_imp_eq_one (solution)
