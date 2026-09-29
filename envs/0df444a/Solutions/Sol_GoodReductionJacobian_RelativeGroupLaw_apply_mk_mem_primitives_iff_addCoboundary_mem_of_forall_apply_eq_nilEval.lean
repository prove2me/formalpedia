-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.apply_mk_mem_primitives_iff_addCoboundary_mem_of_forall_apply_eq_nilEval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4f520172-d355-5562-b340-cfaf680fbff9

import Mathlib
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_MvFormalGroup_TwoCocycle
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection
import Theorems.Thm_MvFormalGroup_nilEval_subst_of_mem
import Theorems.Thm_MvFormalGroup_nilEval_X_of_mem
import Theorems.Thm_MvFormalGroup_mem_span_of_forall_nilEval_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_apply_mk_mem_primitives_iff_addCoboundary_mem_of_forall_apply_eq_nilEval

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

namespace R2Kit
open MvPowerSeries
section NilEval2
variable {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
variable {C : Type} [CommRing C] [Algebra B C]

theorem nilEval_mul (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J)
    (φ ψ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval n (φ * ψ) a = MvFormalGroup.nilEval n φ a * MvFormalGroup.nilEval n ψ a := by
  rw [nilEval_def, nilEval_def, nilEval_def, ← map_mul, ← sub_eq_zero, ← map_sub]
  apply aeval_eq_zero_of_coeff J n hJ a ha
  intro m hm
  rw [MvPolynomial.coeff_sub, coeff_trunc', if_pos hm, MvPolynomial.coeff_mul, coeff_mul, sub_eq_zero]
  apply Finset.sum_congr rfl
  intro x hx
  have hx1 : x.1 ≤ bnd σ n := by
    have := (Finset.HasAntidiagonal.mem_antidiagonal.mp hx); rw [← this] at hm
    exact le_trans (le_self_add) hm
  have hx2 : x.2 ≤ bnd σ n := by
    have := (Finset.HasAntidiagonal.mem_antidiagonal.mp hx); rw [← this] at hm
    exact le_trans (le_add_self) hm
  rw [coeff_trunc', coeff_trunc', if_pos hx1, if_pos hx2]

theorem nilEval_C (n : ℕ) (a : σ → C) (b : B) :
    MvFormalGroup.nilEval n (MvPowerSeries.C b) a = algebraMap B C b := by
  rw [nilEval_def]
  have : trunc' B (bnd σ n) (MvPowerSeries.C b) = MvPolynomial.C b := by
    ext m
    rw [coeff_trunc', MvPowerSeries.coeff_C, MvPolynomial.coeff_C]
    by_cases h0 : m = 0
    · subst h0; simp
    · rw [if_neg h0, if_neg (show ¬ (0 = m) from fun h => h0 h.symm)]
      all_goals (split_ifs <;> rfl)
  rw [this, MvPolynomial.aeval_C]

noncomputable def nilEvalRingHom (J : Ideal C) (n : ℕ) (hJ : J ^ (n + 1) = ⊥) (a : σ → C) (ha : ∀ i, a i ∈ J) :
    MvPowerSeries σ B →+* C where
  toFun φ := MvFormalGroup.nilEval n φ a
  map_one' := by rw [show (1 : MvPowerSeries σ B) = MvPowerSeries.C 1 from (map_one _).symm, nilEval_C, map_one]
  map_mul' φ ψ := nilEval_mul J n hJ a ha φ ψ
  map_zero' := by rw [show (0 : MvPowerSeries σ B) = MvPowerSeries.C 0 from (map_zero _).symm, nilEval_C, map_zero]
  map_add' φ ψ := nilEval_add n a φ ψ

theorem constantCoeff_trunc' (n : σ →₀ ℕ) (φ : MvPowerSeries σ B) :
    MvPolynomial.constantCoeff (MvPowerSeries.trunc' B n φ) = MvPowerSeries.constantCoeff φ := by
  show MvPolynomial.coeff 0 (MvPowerSeries.trunc' B n φ) = MvPowerSeries.coeff 0 φ
  rw [MvPowerSeries.coeff_trunc']
  simp

theorem nilEval_zero' {B' : Type} [CommRing B'] [Algebra B B'] (k : ℕ) (φ : MvPowerSeries σ B) :
    MvFormalGroup.nilEval k φ (0 : σ → B') = algebraMap B B' (MvPowerSeries.constantCoeff φ) := by
  unfold MvFormalGroup.nilEval
  rw [MvPolynomial.aeval_zero, constantCoeff_trunc']

theorem nilEval_mem (J : Ideal C) (n : ℕ) (a : σ → C) (ha : ∀ i, a i ∈ J) (φ : MvPowerSeries σ B)
    (hφ : MvPowerSeries.constantCoeff φ = 0) : MvFormalGroup.nilEval n φ a ∈ J := by
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  unfold MvFormalGroup.nilEval
  have hz : (fun j => (Ideal.Quotient.mk J) (a j)) = 0 :=
    funext fun j => Ideal.Quotient.eq_zero_iff_mem.mpr (ha j)
  have h := congrArg (fun ψ => ψ (MvPowerSeries.trunc' B (Finsupp.equivFunOnFinite.symm fun _ => n) φ))
    (MvPolynomial.comp_aeval a (Ideal.Quotient.mkₐ B J))
  simp only [AlgHom.comp_apply] at h
  rw [Ideal.Quotient.mkₐ_eq_mk] at h
  rw [h, hz, MvPolynomial.aeval_zero, constantCoeff_trunc', hφ, map_zero]

end NilEval2

theorem nilMul_mem {B : Type} [CommRing B] {g : ℕ} (F : MvFormalGroup g B)
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (k : ℕ) (s t : Fin g → B')
    (hs : ∀ i, s i ∈ J) (ht : ∀ i, t i ∈ J) : ∀ i, F.nilMul k s t i ∈ J := by
  intro i
  show MvFormalGroup.nilEval k (F.toPowerSeries i) (Sum.elim s t) ∈ J
  refine nilEval_mem J k _ ?_ _ (F.constantCoeff_eq_zero i)
  rintro (j | j)
  · exact hs j
  · exact ht j

end R2Kit

theorem solution
    (K : Type) [Field K] {A : Scheme.{0}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (n : ℕ)
    (F : MvFormalGroup 2 K) (θ : RelativeGroupLaw.FormalCoordinates f 2) (hθ : L.IsFormalCoordinates F θ)
    (φ : Fin 2 → MvPowerSeries (Fin 2) K)
    (H : Type) [CommRing H] [HopfAlgebra K H]
    (e : ∀ (T : Type) [CommRing T] [Algebra K T],
      WithConv (H →ₐ[K] T) ≃ L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K T))) n)
    (he_mul : ∀ (T : Type) [CommRing T] [Algebra K T] (φ ψ : WithConv (H →ₐ[K] T)),
      ((e T (φ * ψ)).val : SchemeHomOver _ f) = L.mul _ (e T φ).val (e T ψ).val)

    (ν : ℕ) (Φ : (MvPowerSeries (Fin 2) K ⧸ Ideal.span (Set.range φ)) ≃ₐ[K] H)
    (hpin : ∀ (T : Type) [CommRing T] [Algebra K T] (χ : H →ₐ[K] T),
      (∃ J : Ideal T, J ^ (ν + 1) = ⊥ ∧
        ∀ i, χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ J) ∧
      (∀ G : MvPowerSeries (Fin 2) K,
        χ (Φ (Ideal.Quotient.mk _ G)) =
          MvFormalGroup.nilEval ν G (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))) ∧
      ((e T (.toConv χ)).val : SchemeHomOver _ f) =
        θ T (fun i => χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))))
    (hsurj : ∀ (T : Type) [CommRing T] [Algebra K T] (J : Ideal T) (m : ℕ), J ^ (m + 1) = ⊥ →
      ∀ s : Fin 2 → T, (∀ i, s i ∈ J) → (∀ i, MvFormalGroup.nilEval m (φ i) s = 0) →
        ∃ χ : H →ₐ[K] T, ∀ i, χ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) = s i)
    (G : MvPowerSeries (Fin 2) K) :
    Φ (Ideal.Quotient.mk _ G) ∈ primitives K H ↔
      (MvPowerSeries.constantCoeff G = 0 ∧
        F.addCoboundary G ∈ Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l))))) := by
  classical

  have prim_to_conv : ∀ x : H, x ∈ primitives K H →
      ∀ (T : Type) [CommRing T] [Algebra K T] (χ₁ χ₂ : H →ₐ[K] T),
        (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv x = χ₁ x + χ₂ x := by
    intro x hx T _ _ χ₁ χ₂
    have hx' : Coalgebra.comul (R := K) x = x ⊗ₜ[K] 1 + 1 ⊗ₜ[K] x := by
      have h0 := hx
      simp only [primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.flip_apply,
        TensorProduct.mk_apply] at h0
      rw [sub_sub, sub_eq_zero] at h0
      exact h0
    rw [AlgHom.convMul_apply]
    change (Algebra.TensorProduct.lift χ₁ χ₂ _) (Coalgebra.comul (R := K) x) = _
    rw [hx', map_add, Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.lift_tmul, map_one, map_one,
      mul_one, one_mul]
  have conv_to_prim : ∀ x : H,
      (∀ (T : Type) [CommRing T] [Algebra K T] (χ₁ χ₂ : H →ₐ[K] T),
        (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv x = χ₁ x + χ₂ x) → x ∈ primitives K H := by
    intro x h
    have h1 := h (H ⊗[K] H) (Algebra.TensorProduct.includeLeft : H →ₐ[K] H ⊗[K] H)
      (Algebra.TensorProduct.includeRight : H →ₐ[K] H ⊗[K] H)
    rw [AlgHom.convMul_apply] at h1
    change (Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft : H →ₐ[K] H ⊗[K] H)
      (Algebra.TensorProduct.includeRight : H →ₐ[K] H ⊗[K] H) _) (Coalgebra.comul (R := K) x) = _ at h1
    have hlift : ∀ z : H ⊗[K] H, (Algebra.TensorProduct.lift
        (Algebra.TensorProduct.includeLeft : H →ₐ[K] H ⊗[K] H)
        (Algebra.TensorProduct.includeRight : H →ₐ[K] H ⊗[K] H)
        (fun _ _ => Commute.all _ _)) z = z := by
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul a b =>
          rw [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.includeLeft_apply,
            Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      | add z w hz hw => rw [map_add, hz, hw]
    rw [hlift, Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply] at h1
    simp only [primitives, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.flip_apply, TensorProduct.mk_apply]
    rw [sub_sub, sub_eq_zero]
    exact h1

  have key : ∀ (T : Type) [CommRing T] [Algebra K T] (χ₁ χ₂ : H →ₐ[K] T) (Jc : Ideal T) (M : ℕ),
      Jc ^ (M + 1) = ⊥ →
      (∀ i, χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ Jc) →
      (∀ i, χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ Jc) →
      (∀ i, (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ Jc) →
      ((WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv (Φ (Ideal.Quotient.mk _ G))
          - χ₁ (Φ (Ideal.Quotient.mk _ G)) - χ₂ (Φ (Ideal.Quotient.mk _ G)) =
        MvFormalGroup.nilEval M (F.addCoboundary G)
          (Sum.elim (fun i => χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))
            (fun i => χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))))) ∧
      (∀ ψ ∈ Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l))),
        MvFormalGroup.nilEval M ψ
          (Sum.elim (fun i => χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))
            (fun i => χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))) = 0) := by
    intro T _ _ χ₁ χ₂ Jc M hJc hc₁ hc₂ hc₃
    set χ₃ : H →ₐ[K] T := (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv with hχ₃
    set c₁ : Fin 2 → T := fun i => χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) with hc₁def
    set c₂ : Fin 2 → T := fun i => χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) with hc₂def
    set c₃ : Fin 2 → T := fun i => χ₃ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) with hc₃def
    obtain ⟨⟨J₁, hJ₁, hm₁⟩, hev₁, he₁⟩ := hpin T χ₁
    obtain ⟨⟨J₂, hJ₂, hm₂⟩, hev₂, he₂⟩ := hpin T χ₂
    obtain ⟨⟨J₃, hJ₃, hm₃⟩, hev₃, he₃⟩ := hpin T χ₃
    have hc₃' : ∀ i, c₃ i ∈ Jc := hc₃

    have hcc : ∀ i, Sum.elim c₁ c₂ i ∈ Jc := by
      rintro (i | i)
      · exact hc₁ i
      · exact hc₂ i

    have hhom := (hθ.2 T Jc M hJc).2.2.2 c₁ c₂ hc₁ hc₂
    have hθ₃ : θ T c₃ = θ T (F.nilMul M c₁ c₂) := by
      rw [hhom]
      have h3 : ((e T (.toConv χ₃)).val : SchemeHomOver _ f) = θ T c₃ := he₃
      rw [← h3, hχ₃, WithConv.toConv_ofConv, he_mul]
      have h1 : ((e T (.toConv χ₁)).val : SchemeHomOver _ f) = θ T c₁ := he₁
      have h2 : ((e T (.toConv χ₂)).val : SchemeHomOver _ f) = θ T c₂ := he₂
      rw [h1, h2]
    have hc₃eq : c₃ = F.nilMul M c₁ c₂ :=
      (hθ.2 T Jc M hJc).2.1 c₃ _ hc₃' (R2Kit.nilMul_mem F Jc M c₁ c₂ hc₁ hc₂) hθ₃

    have hXl : ∀ t : Fin 2, MvPowerSeries.constantCoeff
        ((MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) = 0 :=
      fun t => MvPowerSeries.constantCoeff_X _
    have hXr : ∀ t : Fin 2, MvPowerSeries.constantCoeff
        ((MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) = 0 :=
      fun t => MvPowerSeries.constantCoeff_X _
    have hsubF := fun (G' : MvPowerSeries (Fin 2) K) =>
      (MvFormalGroup.nilEval_subst_of_mem Jc M hJc (Sum.elim c₁ c₂) hcc F.toPowerSeries F.constantCoeff_eq_zero G').2
    have hsubL := fun (G' : MvPowerSeries (Fin 2) K) =>
      (MvFormalGroup.nilEval_subst_of_mem Jc M hJc (Sum.elim c₁ c₂) hcc
        (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) hXl G').2
    have hsubR := fun (G' : MvPowerSeries (Fin 2) K) =>
      (MvFormalGroup.nilEval_subst_of_mem Jc M hJc (Sum.elim c₁ c₂) hcc
        (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) hXr G').2
    have hXl' : (fun t : Fin 2 => MvFormalGroup.nilEval M
        ((MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (Sum.elim c₁ c₂)) = c₁ := by
      funext t; rw [MvFormalGroup.nilEval_X_of_mem Jc M hJc _ hcc]; rfl
    have hXr' : (fun t : Fin 2 => MvFormalGroup.nilEval M
        ((MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (Sum.elim c₁ c₂)) = c₂ := by
      funext t; rw [MvFormalGroup.nilEval_X_of_mem Jc M hJc _ hcc]; rfl
    have hF' : (fun i : Fin 2 => MvFormalGroup.nilEval M (F.toPowerSeries i) (Sum.elim c₁ c₂)) = F.nilMul M c₁ c₂ := rfl
    refine ⟨?_, ?_⟩
    ·
      have e3 : χ₃ (Φ (Ideal.Quotient.mk _ G)) =
          MvFormalGroup.nilEval M (MvPowerSeries.subst F.toPowerSeries G) (Sum.elim c₁ c₂) := by
        rw [hev₃, R2Kit.nilEval_level J₃ ν hJ₃ Jc M hJc c₃ hm₃ hc₃' G]
        change MvFormalGroup.nilEval M G c₃ = _
        rw [hc₃eq, ← hF', hsubF]
      have e1 : χ₁ (Φ (Ideal.Quotient.mk _ G)) =
          MvFormalGroup.nilEval M (MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) G) (Sum.elim c₁ c₂) := by
        rw [hev₁, R2Kit.nilEval_level J₁ ν hJ₁ Jc M hJc c₁ hm₁ hc₁ G]
        change MvFormalGroup.nilEval M G c₁ = _
        rw [hsubL, hXl']
      have e2 : χ₂ (Φ (Ideal.Quotient.mk _ G)) =
          MvFormalGroup.nilEval M (MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) G) (Sum.elim c₁ c₂) := by
        rw [hev₂, R2Kit.nilEval_level J₂ ν hJ₂ Jc M hJc c₂ hm₂ hc₂ G]
        change MvFormalGroup.nilEval M G c₂ = _
        rw [hsubR, hXr']
      change χ₃ (Φ (Ideal.Quotient.mk _ G)) - χ₁ (Φ (Ideal.Quotient.mk _ G)) - χ₂ (Φ (Ideal.Quotient.mk _ G)) = _
      rw [e1, e2, e3]
      unfold MvFormalGroup.addCoboundary
      rw [R2Kit.nilEval_sub, R2Kit.nilEval_sub]
    ·
      rintro ψ ⟨(l | l), rfl⟩
      · change MvFormalGroup.nilEval M (MvPowerSeries.subst _ (φ l)) _ = 0
        have hφl : (Ideal.Quotient.mk (Ideal.span (Set.range φ)) (φ l)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self l))
        rw [hsubL, hXl', ← R2Kit.nilEval_level J₁ ν hJ₁ Jc M hJc c₁ hm₁ hc₁ (φ l), ← hev₁, hφl, map_zero, map_zero]
      · change MvFormalGroup.nilEval M (MvPowerSeries.subst _ (φ l)) _ = 0
        have hφl : (Ideal.Quotient.mk (Ideal.span (Set.range φ)) (φ l)) = 0 :=
          Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self l))
        rw [hsubR, hXr', ← R2Kit.nilEval_level J₂ ν hJ₂ Jc M hJc c₂ hm₂ hc₂ (φ l), ← hev₂, hφl, map_zero, map_zero]
  constructor
  ·
    intro hx
    refine ⟨?_, ?_⟩
    ·
      let χ₀ : H →ₐ[K] K := Bialgebra.counitAlgHom K H
      have h3 : χ₀ (Φ (Ideal.Quotient.mk _ G)) = 0 := by

        have hnt : Nontrivial H := ⟨⟨0, 1, fun h01 => by
          have h' := congrArg (Bialgebra.counitAlgHom K H) h01
          rw [map_zero, map_one] at h'
          exact zero_ne_one h'⟩⟩
        have h1 : WithConv.toConv ((Algebra.ofId K H).comp (Bialgebra.counitAlgHom K H)) = 1 :=
          (AlgHom.convOne_def).symm
        have h2 := prim_to_conv _ hx H ((Algebra.ofId K H).comp (Bialgebra.counitAlgHom K H)) (AlgHom.id K H)
        rw [h1, one_mul, WithConv.ofConv_toConv, AlgHom.id_apply, AlgHom.comp_apply, Algebra.ofId_apply] at h2
        have h4 : algebraMap K H (χ₀ (Φ (Ideal.Quotient.mk _ G))) = 0 := by linear_combination -h2
        exact (map_eq_zero_iff _ (algebraMap K H).injective).mp h4
      obtain ⟨⟨J₀, hJ₀, hm₀⟩, hev₀, -⟩ := hpin K χ₀
      have hc0 : (fun i => χ₀ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))) = (0 : Fin 2 → K) := by
        funext i
        have hn : IsNilpotent (χ₀ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))) :=
          ⟨ν + 1, by have := Ideal.pow_mem_pow (hm₀ i) (ν + 1); rwa [hJ₀, Ideal.mem_bot] at this⟩
        exact hn.eq_zero
      rw [hev₀, hc0, R2Kit.nilEval_zero'] at h3
      simpa using h3
    ·
      apply MvFormalGroup.mem_span_of_forall_nilEval_eq_zero
      intro C _ _ J m hJ s hs hS

      have hs₁ : ∀ t, s (Sum.inl t) ∈ J := fun t => hs _
      have hs₂ : ∀ t, s (Sum.inr t) ∈ J := fun t => hs _
      have hXl : ∀ t : Fin 2, MvPowerSeries.constantCoeff
          ((MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) = 0 :=
        fun t => MvPowerSeries.constantCoeff_X _
      have hXr : ∀ t : Fin 2, MvPowerSeries.constantCoeff
          ((MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) = 0 :=
        fun t => MvPowerSeries.constantCoeff_X _
      have hz₁ : ∀ l, MvFormalGroup.nilEval m (φ l) (fun t => s (Sum.inl t)) = 0 := by
        intro l
        have h := hS _ ⟨Sum.inl l, rfl⟩
        change MvFormalGroup.nilEval m (MvPowerSeries.subst _ (φ l)) s = 0 at h
        rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXl (φ l)).2] at h
        have : (fun t : Fin 2 => MvFormalGroup.nilEval m
            ((MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) s) = fun t => s (Sum.inl t) := by
          funext t; rw [MvFormalGroup.nilEval_X_of_mem J m hJ s hs]
        rwa [this] at h
      have hz₂ : ∀ l, MvFormalGroup.nilEval m (φ l) (fun t => s (Sum.inr t)) = 0 := by
        intro l
        have h := hS _ ⟨Sum.inr l, rfl⟩
        change MvFormalGroup.nilEval m (MvPowerSeries.subst _ (φ l)) s = 0 at h
        rw [(MvFormalGroup.nilEval_subst_of_mem J m hJ s hs _ hXr (φ l)).2] at h
        have : (fun t : Fin 2 => MvFormalGroup.nilEval m
            ((MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) s) = fun t => s (Sum.inr t) := by
          funext t; rw [MvFormalGroup.nilEval_X_of_mem J m hJ s hs]
        rwa [this] at h
      obtain ⟨χ₁, hχ₁⟩ := hsurj C J m hJ _ hs₁ hz₁
      obtain ⟨χ₂, hχ₂⟩ := hsurj C J m hJ _ hs₂ hz₂
      obtain ⟨⟨J₃, hJ₃, hm₃⟩, -, -⟩ := hpin C (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv
      have hJc := R2Kit.sup_pow_eq_bot J J₃ m ν hJ hJ₃
      have hc₁ : ∀ i, χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ J ⊔ J₃ :=
        fun i => by rw [hχ₁]; exact Ideal.mem_sup_left (hs₁ i)
      have hc₂ : ∀ i, χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))) ∈ J ⊔ J₃ :=
        fun i => by rw [hχ₂]; exact Ideal.mem_sup_left (hs₂ i)
      obtain ⟨hk, -⟩ := key C χ₁ χ₂ (J ⊔ J₃) _ hJc hc₁ hc₂ (fun i => Ideal.mem_sup_right (hm₃ i))
      have hsum : (Sum.elim (fun i => χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))
          (fun i => χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))) = s := by
        funext i; rcases i with i | i
        · exact hχ₁ i
        · exact hχ₂ i
      rw [prim_to_conv _ hx, hsum] at hk
      rw [R2Kit.nilEval_level J m hJ (J ⊔ J₃) _ hJc s hs (fun i => Ideal.mem_sup_left (hs i)), ← hk]
      ring
  ·
    rintro ⟨-, hmem⟩
    apply conv_to_prim
    intro T _ _ χ₁ χ₂
    obtain ⟨⟨J₁, hJ₁, hm₁⟩, -, -⟩ := hpin T χ₁
    obtain ⟨⟨J₂, hJ₂, hm₂⟩, -, -⟩ := hpin T χ₂
    obtain ⟨⟨J₃, hJ₃, hm₃⟩, -, -⟩ := hpin T (WithConv.toConv χ₁ * WithConv.toConv χ₂).ofConv
    have h12 := R2Kit.sup_pow_eq_bot J₁ J₂ ν ν hJ₁ hJ₂
    have h123 := R2Kit.sup_pow_eq_bot (J₁ ⊔ J₂) J₃ _ ν h12 hJ₃
    obtain ⟨hk, hgen⟩ := key T χ₁ χ₂ ((J₁ ⊔ J₂) ⊔ J₃) _ h123
      (fun i => Ideal.mem_sup_left (Ideal.mem_sup_left (hm₁ i)))
      (fun i => Ideal.mem_sup_left (Ideal.mem_sup_right (hm₂ i)))
      (fun i => Ideal.mem_sup_right (hm₃ i))
    have hcc : ∀ i, Sum.elim (fun i => χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))
        (fun i => χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i)))) i ∈ (J₁ ⊔ J₂) ⊔ J₃ := by
      rintro (i | i)
      · exact Ideal.mem_sup_left (Ideal.mem_sup_left (hm₁ i))
      · exact Ideal.mem_sup_left (Ideal.mem_sup_right (hm₂ i))
    have hzero : MvFormalGroup.nilEval ((ν + ν + 1) + ν + 1) (F.addCoboundary G)
        (Sum.elim (fun i => χ₁ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))
          (fun i => χ₂ (Φ (Ideal.Quotient.mk _ (MvPowerSeries.X i))))) = 0 := by
      have hle : Ideal.span (Set.range (Sum.elim
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inl t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l))
          (fun l => MvPowerSeries.subst
            (fun t => (MvPowerSeries.X (Sum.inr t) : MvPowerSeries (Fin 2 ⊕ Fin 2) K)) (φ l)))) ≤
          RingHom.ker (R2Kit.nilEvalRingHom (B := K) ((J₁ ⊔ J₂) ⊔ J₃) ((ν + ν + 1) + ν + 1) h123 _ hcc) :=
        Ideal.span_le.mpr fun ψ hψ => (RingHom.mem_ker).mpr (hgen ψ hψ)
      exact (RingHom.mem_ker).mp (hle hmem)
    rw [hzero] at hk
    rw [sub_sub, sub_eq_zero] at hk
    exact hk

end S_GoodReductionJacobian_RelativeGroupLaw_apply_mk_mem_primitives_iff_addCoboundary_mem_of_forall_apply_eq_nilEval
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_apply_mk_mem_primitives_iff_addCoboundary_mem_of_forall_apply_eq_nilEval (solution)
