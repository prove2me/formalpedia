-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.apply_apply_mk_eq_apply_mk_subst_of_forall_apply_eq_nilEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/a6427e1b-0341-5c59-8a71-b10c6f9a4062

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_apply_apply_mk_eq_apply_mk_subst_of_forall_apply_eq_nilEval

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct

namespace R2Kit

open MvPowerSeries

section NilEval
variable {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {C : Type} [CommRing C] [Algebra B C]

noncomputable abbrev bnd (σ : Type) [Fintype σ] [DecidableEq σ] (n : ℕ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => n

theorem le_bnd_iff (n : ℕ) (m : σ →₀ ℕ) : m ≤ bnd σ n ↔ ∀ i, m i ≤ n := by
  simp [bnd, Finsupp.le_def]

theorem prod_pow_eq_zero (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (m : σ →₀ ℕ) (hm : ¬ m ≤ bnd σ n) : (m.prod fun i k => a i ^ k) = 0 := by
  rw [le_bnd_iff] at hm
  push Not at hm
  obtain ⟨i, hi⟩ := hm
  rw [Finsupp.prod]
  have hi' : i ∈ m.support := by
    rw [Finsupp.mem_support_iff]; omega
  apply Finset.prod_eq_zero hi'
  have : a i ^ (n + 1) = 0 := by
    have := Ideal.pow_mem_pow (ha i) (n + 1)
    rwa [hJ, Ideal.mem_bot] at this
  rw [show m i = (n + 1) + (m i - (n + 1)) by omega, pow_add, this, zero_mul]

theorem aeval_eq_zero_of_coeff (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (P : MvPolynomial σ B) (hP : ∀ m, m ≤ bnd σ n → P.coeff m = 0) : MvPolynomial.aeval a P = 0 := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  apply Finset.sum_eq_zero
  intro m _
  by_cases hm : m ≤ bnd σ n
  · rw [hP m hm, map_zero, zero_mul]
  · rw [← Finsupp.prod, prod_pow_eq_zero J n hJ a ha m hm, mul_zero]

theorem nilEval_def (n : ℕ) (φ : MvPowerSeries σ B) (a : σ → C) :
    MvFormalGroup.nilEval n φ a = MvPolynomial.aeval a (trunc' B (bnd σ n) φ) := rfl

theorem nilEval_mono (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (φ : MvPowerSeries σ B) (n' : ℕ) (hn : n ≤ n') :
    MvFormalGroup.nilEval n' φ a = MvFormalGroup.nilEval n φ a := by
  rw [nilEval_def, nilEval_def, ← sub_eq_zero, ← map_sub]
  apply aeval_eq_zero_of_coeff J n hJ a ha
  intro m hm
  have hm' : m ≤ bnd σ n' := by
    rw [le_bnd_iff] at hm ⊢; exact fun i => (hm i).trans hn
  rw [MvPolynomial.coeff_sub, coeff_trunc', coeff_trunc', if_pos hm', if_pos hm, sub_self]

theorem nilEval_level (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (J' : Ideal C) (n' : ℕ) (hJ' : J' ^ (n' + 1) = ⊥)
    (a : σ → C) (ha : ∀ i, a i ∈ J) (ha' : ∀ i, a i ∈ J') (φ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n φ a = MvFormalGroup.nilEval n' φ a := by
  rw [← nilEval_mono J n hJ a ha φ (max n n') (le_max_left _ _),
    nilEval_mono J' n' hJ' a ha' φ (max n n') (le_max_right _ _)]

theorem nilEval_add (n : ℕ) (a : σ → C) (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ + ψ) a = MvFormalGroup.nilEval n φ a + MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_add]
  congr 1
  ext m
  simp only [coeff_trunc', MvPolynomial.coeff_add, map_add]

theorem nilEval_sub (n : ℕ) (a : σ → C) (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ - ψ) a = MvFormalGroup.nilEval n φ a - MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_sub]
  congr 1
  ext m
  simp only [coeff_trunc', MvPolynomial.coeff_sub, map_sub]

theorem sup_pow_eq_bot (J₁ J₂ : Ideal C) (n₁ n₂ : ℕ) (h₁ : J₁ ^ (n₁ + 1) = ⊥) (h₂ : J₂ ^ (n₂ + 1) = ⊥) :
    (J₁ ⊔ J₂) ^ ((n₁ + n₂ + 1) + 1) = ⊥ := by
  have h := Ideal.sup_pow_add_le_pow_sup_pow (I := J₁) (J := J₂) (m := n₂ + 1) (n := n₁ + 1)
  rw [h₁, h₂, bot_sup_eq, le_bot_iff] at h
  rw [show n₁ + n₂ + 1 + 1 = (n₁ + 1) + (n₂ + 1) by omega]
  exact h

end NilEval

end R2Kit

theorem solution
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (F : MvFormalGroup 2 K) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (φ : Fin 2 → MvPowerSeries (Fin 2) K)
    (H : Type) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)

    (ν : ℕ) (Φ : (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range φ)) ≃ₐ[K] H)
    (hpin : ∀ (T : Type) [CommRing T] [Algebra K T] (χ : H →ₐ[K] T),
      (∃ J : Ideal T, J ^ (ν + 1) = ⊥ ∧
        ∀ i, χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ J) ∧
      (∀ G : MvPowerSeries (Fin 2) K,
        χ (Φ (Ideal.Quotient.mk _ G)) =
          MvFormalGroup.nilEval ν G (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))) ∧
      ((e T (.toConv χ)).val : SchemeHomOver _ f) =
        θ T (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))))

    (act : A ⟶ A)
    (S : Fin 2 → MvPowerSeries (Fin 2) K) (hS0 : ∀ i, MvPowerSeries.constantCoeff (S i) = 0)
    (hS : ∀ (T : Type) [CommRing T] [Algebra K T] (J : Ideal T) (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → T, (∀ i, s i ∈ J) →
        (θ T (fun i => MvFormalGroup.nilEval m (S i) s)).1 = (θ T s).1 ≫ act)
    (φH : H →ₐ[K] H)
    (hφH : ∀ (T : Type) [CommRing T] [Algebra K T] (χ : WithConv (H →ₐ[K] T)),
      ((e T (.toConv (χ.ofConv.comp φH))).val : SchemeHomOver _ f).1 = (e T χ).val.1 ≫ act)
    (G : MvPowerSeries (Fin 2) K) :
    φH (Φ (Ideal.Quotient.mk _ G)) = Φ (Ideal.Quotient.mk _ (MvPowerSeries.subst S G)) := by
  classical

  suffices key : ∀ (T : Type) [CommRing T] [Algebra K T] (χ : H →ₐ[K] T),
      χ (φH (Φ (Ideal.Quotient.mk _ G))) = χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.subst S G))) by
    simpa using key H (AlgHom.id K H)
  intro T _ _ χ
  obtain ⟨⟨J₁, hJ₁, hc₁⟩, hev₁, he₁⟩ := hpin T χ
  obtain ⟨⟨J₂, hJ₂, hc₂⟩, hev₂, he₂⟩ := hpin T (χ.comp φH)

  set c₁ : Fin 2 → T := fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) with hc₁def
  set c₂ : Fin 2 → T := fun i => (χ.comp φH) (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) with hc₂def

  have hJ := R2Kit.sup_pow_eq_bot J₁ J₂ ν ν hJ₁ hJ₂
  set M : ℕ := ν + ν + 1 with hM
  have hc₁' : ∀ i, c₁ i ∈ J₁ ⊔ J₂ := fun i => Ideal.mem_sup_left (hc₁ i)
  have hc₂' : ∀ i, c₂ i ∈ J₁ ⊔ J₂ := fun i => Ideal.mem_sup_right (hc₂ i)

  obtain ⟨hSmem, hsubst⟩ :=
    MvFormalGroup.nilEval_subst_of_mem (J₁ ⊔ J₂) M hJ c₁ hc₁' S hS0 G

  have hθ₂ : θ T c₂ = θ T (fun i => MvFormalGroup.nilEval M (S i) c₁) := by
    apply Subtype.ext
    rw [hS T (J₁ ⊔ J₂) M hJ c₁ hc₁']
    have h1 : ((e T (.toConv χ)).val : SchemeHomOver _ f) = θ T c₁ := he₁
    have h2 : ((e T (.toConv (χ.comp φH))).val : SchemeHomOver _ f) = θ T c₂ := he₂
    have h3 := hφH T (.toConv χ)
    rw [WithConv.ofConv_toConv] at h3
    rw [← h2, h3, h1]
  have hc₂eq : c₂ = fun i => MvFormalGroup.nilEval M (S i) c₁ :=
    (hθ.2 T (J₁ ⊔ J₂) M hJ).2.1 c₂ _ hc₂' hSmem hθ₂

  calc χ (φH (Φ (Ideal.Quotient.mk _ G)))
      = (χ.comp φH) (Φ (Ideal.Quotient.mk _ G)) := rfl
    _ = MvFormalGroup.nilEval ν G c₂ := hev₂ G
    _ = MvFormalGroup.nilEval M G c₂ :=
        R2Kit.nilEval_level J₂ ν hJ₂ (J₁ ⊔ J₂) M hJ c₂ hc₂ hc₂' G
    _ = MvFormalGroup.nilEval M G (fun i => MvFormalGroup.nilEval M (S i) c₁) := by rw [hc₂eq]
    _ = MvFormalGroup.nilEval M (MvPowerSeries.subst S G) c₁ := hsubst.symm
    _ = MvFormalGroup.nilEval ν (MvPowerSeries.subst S G) c₁ :=
        (R2Kit.nilEval_level J₁ ν hJ₁ (J₁ ⊔ J₂) M hJ c₁ hc₁ hc₁' _).symm
    _ = χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.subst S G))) := (hev₁ _).symm

end S_GoodReductionJacobian_RelativeGroupLaw_apply_apply_mk_eq_apply_mk_subst_of_forall_apply_eq_nilEval
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_apply_apply_mk_eq_apply_mk_subst_of_forall_apply_eq_nilEval (solution)
