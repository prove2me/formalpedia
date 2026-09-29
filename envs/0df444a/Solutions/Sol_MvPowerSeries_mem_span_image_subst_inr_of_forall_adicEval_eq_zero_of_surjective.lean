-- Prove2me | solution 1 for MvPowerSeries.mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/164a6f35-61e1-5f68-a62d-a993fa0e2005

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Theorems.Thm_MvFormalGroup_algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal
open scoped TensorProduct

namespace GenTensorTruncSol

section Trunc

variable {σ : Type} [DecidableEq σ] {R : Type} [CommRing R]

theorem mem_span_X_pow_of_coeff_eq_zero (N : ℕ) (s : Finset σ) :
    ∀ G : MvPowerSeries σ R, (∀ d : σ →₀ ℕ, (∀ j ∈ s, d j < N) → MvPowerSeries.coeff d G = 0) →
      G ∈ Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ R) ^ N) := by
  induction s using Finset.induction_on with
  | empty =>
    intro G hG
    have : G = 0 := MvPowerSeries.ext fun d => by
      rw [hG d (fun j hj => absurd hj (Finset.notMem_empty j)), map_zero]
    rw [this]; exact Ideal.zero_mem _
  | insert j s hjs ih =>
    intro G hG

    let G₁ : MvPowerSeries σ R := fun d => if d j < N then MvPowerSeries.coeff d G else 0
    have hG₁ : ∀ d, MvPowerSeries.coeff d G₁ = if d j < N then MvPowerSeries.coeff d G else 0 := fun d => rfl
    have h1 : G₁ ∈ Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ R) ^ N) := by
      apply ih
      intro d hd
      rw [hG₁]
      split_ifs with hdj
      · exact hG d (fun j' hj' => by
          rcases Finset.mem_insert.mp hj' with rfl | hj'
          · exact hdj
          · exact hd j' hj')
      · rfl
    have h2 : G - G₁ ∈ Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ R) ^ N) := by
      have hdvd : (MvPowerSeries.X j : MvPowerSeries σ R) ^ N ∣ G - G₁ := by
        rw [MvPowerSeries.X_pow_dvd_iff]
        intro m hm
        rw [map_sub, hG₁, if_pos hm, sub_self]
      obtain ⟨q, hq⟩ := hdvd
      rw [hq]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨j, rfl⟩)
    have : G = G₁ + (G - G₁) := by abel
    rw [this]
    exact Ideal.add_mem _ h1 h2

theorem exists_sub_coe_mem_span_X_pow [Fintype σ] (N : ℕ) (hN : 0 < N) (G : MvPowerSeries σ R) :
    ∃ P : MvPolynomial σ R,
      G - ↑P ∈ Ideal.span (Set.range fun j : σ => (MvPowerSeries.X j : MvPowerSeries σ R) ^ N) := by
  let n : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun _ => N - 1)
  have hn : ∀ j, n j = N - 1 := fun j => by simp [n]
  refine ⟨MvPowerSeries.trunc' R n G, mem_span_X_pow_of_coeff_eq_zero N Finset.univ _ fun d hd => ?_⟩
  have hle : d ≤ n := fun j => by rw [hn]; have := hd j (Finset.mem_univ j); omega
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos hle, sub_self]

end Trunc

section ProductMap

variable {S : Type} [CommRing S] {τ : Type}

theorem coe_mem_range_productMap {σ₁ σ₂ : Type} (sL : MvPowerSeries σ₁ S →ₐ[S] MvPowerSeries τ S)
    (sR : MvPowerSeries σ₂ S →ₐ[S] MvPowerSeries τ S)
    (hX : ∀ j : τ, (∃ i, sL (MvPowerSeries.X i) = MvPowerSeries.X j) ∨ (∃ i, sR (MvPowerSeries.X i) = MvPowerSeries.X j))
    (P : MvPolynomial τ S) :
    ∃ p : MvPowerSeries σ₁ S ⊗[S] MvPowerSeries σ₂ S,
      Algebra.TensorProduct.productMap sL sR p = (↑P : MvPowerSeries τ S) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    refine ⟨algebraMap S _ a, ?_⟩
    rw [AlgHom.commutes, MvPolynomial.coe_C]
    rfl
  | add p q hp hq =>
    obtain ⟨p', hp'⟩ := hp
    obtain ⟨q', hq'⟩ := hq
    exact ⟨p' + q', by rw [map_add, hp', hq', MvPolynomial.coe_add]⟩
  | mul_X p j hp =>
    obtain ⟨p', hp'⟩ := hp
    rcases hX j with ⟨i, hi⟩ | ⟨i, hi⟩
    · refine ⟨p' * (MvPowerSeries.X i ⊗ₜ[S] 1), ?_⟩
      rw [map_mul, hp', Algebra.TensorProduct.productMap_apply_tmul, hi, map_one, mul_one, MvPolynomial.coe_mul,
        MvPolynomial.coe_X]
    · refine ⟨p' * (1 ⊗ₜ[S] MvPowerSeries.X i), ?_⟩
      rw [map_mul, hp', Algebra.TensorProduct.productMap_apply_tmul, hi, map_one, one_mul, MvPolynomial.coe_mul,
        MvPolynomial.coe_X]

end ProductMap

end GenTensorTruncSol

open GenTensorTruncSol in

theorem genTensorTrunc
    {S : Type} [CommRing S] {C₁ : Type} [CommRing C₁] [Algebra S C₁] {C₂ : Type} [CommRing C₂] [Algebra S C₂]
    (θ₁ : MvPowerSeries (Fin 2) S →ₐ[S] C₁) (θ₂ : MvPowerSeries (Fin 2) S →ₐ[S] C₂)
    (hθ₁ : Function.Surjective θ₁) (hθ₂ : Function.Surjective θ₂)
    (hX₁ : ∀ i, IsNilpotent (θ₁ (MvPowerSeries.X i))) (hX₂ : ∀ i, IsNilpotent (θ₂ (MvPowerSeries.X i)))
    (hev₁ : ∀ G, θ₁ G = MvFormalGroup.adicEval (⊥ : Ideal C₁) (fun i => θ₁ (MvPowerSeries.X i)) G)
    (hev₂ : ∀ G, θ₂ G = MvFormalGroup.adicEval (⊥ : Ideal C₂) (fun i => θ₂ (MvPowerSeries.X i)) G)
    (G : MvPowerSeries (Fin 2 ⊕ Fin 2) S) :
    MvFormalGroup.adicEval (⊥ : Ideal (C₁ ⊗[S] C₂))
        (Sum.elim (fun j => θ₁ (MvPowerSeries.X j) ⊗ₜ[S] (1 : C₂)) (fun j => (1 : C₁) ⊗ₜ[S] θ₂ (MvPowerSeries.X j))) G = 0 ↔
      G ∈ Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
            (RingHom.ker θ₁ : Set (MvPowerSeries (Fin 2) S)) ∪
         (MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) S))) ''
            (RingHom.ker θ₂ : Set (MvPowerSeries (Fin 2) S))) := by
  classical
  set c₁ : Fin 2 → C₁ := fun i => θ₁ (MvPowerSeries.X i) with hc₁_def
  set c₂ : Fin 2 → C₂ := fun i => θ₂ (MvPowerSeries.X i) with hc₂_def
  set c₄ : Fin 2 ⊕ Fin 2 → C₁ ⊗[S] C₂ :=
    Sum.elim (fun j => θ₁ (MvPowerSeries.X j) ⊗ₜ[S] (1 : C₂)) (fun j => (1 : C₁) ⊗ₜ[S] θ₂ (MvPowerSeries.X j))
    with hc₄_def
  let aL : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) S := fun l => MvPowerSeries.X (Sum.inl l)
  let aR : Fin 2 → MvPowerSeries (Fin 2 ⊕ Fin 2) S := fun l => MvPowerSeries.X (Sum.inr l)
  set J : Ideal (MvPowerSeries (Fin 2 ⊕ Fin 2) S) :=
    Ideal.span (MvPowerSeries.subst aL '' (RingHom.ker θ₁ : Set (MvPowerSeries (Fin 2) S)) ∪
      MvPowerSeries.subst aR '' (RingHom.ker θ₂ : Set (MvPowerSeries (Fin 2) S))) with hJ_def
  have hL : MvPowerSeries.HasSubst aL :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  have hR : MvPowerSeries.HasSubst aR :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _
  let sL : MvPowerSeries (Fin 2) S →ₐ[S] MvPowerSeries (Fin 2 ⊕ Fin 2) S := MvPowerSeries.substAlgHom hL
  let sR : MvPowerSeries (Fin 2) S →ₐ[S] MvPowerSeries (Fin 2 ⊕ Fin 2) S := MvPowerSeries.substAlgHom hR
  have hsL : ∀ f, sL f = MvPowerSeries.subst aL f := fun f => congrFun (MvPowerSeries.coe_substAlgHom hL) f
  have hsR : ∀ f, sR f = MvPowerSeries.subst aR f := fun f => congrFun (MvPowerSeries.coe_substAlgHom hR) f

  obtain ⟨n₀, hn₀⟩ := hX₁ 0
  obtain ⟨n₁, hn₁⟩ := hX₁ 1
  obtain ⟨m₀, hm₀⟩ := hX₂ 0
  obtain ⟨m₁, hm₁⟩ := hX₂ 1
  set N : ℕ := n₀ + n₁ + m₀ + m₁ + 1 with hN_def
  have hNpos : 0 < N := by omega
  have hc₁N : ∀ i, c₁ i ^ N = 0 := by
    intro i
    fin_cases i
    · exact pow_eq_zero_of_le (by omega) hn₀
    · exact pow_eq_zero_of_le (by omega) hn₁
  have hc₂N : ∀ i, c₂ i ^ N = 0 := by
    intro i
    fin_cases i
    · exact pow_eq_zero_of_le (by omega) hm₀
    · exact pow_eq_zero_of_le (by omega) hm₁
  have hc₁ : ∀ i, c₁ i ∈ (⊥ : Ideal C₁).radical := fun i => ⟨N, by rw [hc₁N i]; exact Ideal.zero_mem _⟩
  have hc₂ : ∀ i, c₂ i ∈ (⊥ : Ideal C₂).radical := fun i => ⟨N, by rw [hc₂N i]; exact Ideal.zero_mem _⟩
  have hc₄N : ∀ j, c₄ j ^ N = 0 := by
    rintro (j | j)
    · show (θ₁ (MvPowerSeries.X j) ⊗ₜ[S] (1 : C₂)) ^ N = 0
      rw [Algebra.TensorProduct.tmul_pow, one_pow, show θ₁ (MvPowerSeries.X j) ^ N = 0 from hc₁N j,
        TensorProduct.zero_tmul]
    · show ((1 : C₁) ⊗ₜ[S] θ₂ (MvPowerSeries.X j)) ^ N = 0
      rw [Algebra.TensorProduct.tmul_pow, one_pow, show θ₂ (MvPowerSeries.X j) ^ N = 0 from hc₂N j,
        TensorProduct.tmul_zero]
  have hc₄ : ∀ j, c₄ j ∈ (⊥ : Ideal (C₁ ⊗[S] C₂)).radical := fun j => ⟨N, by rw [hc₄N j]; exact Ideal.zero_mem _⟩

  let Ψ : MvPowerSeries (Fin 2 ⊕ Fin 2) S →ₐ[S] C₁ ⊗[S] C₂ := MvFormalGroup.adicEvalAlgHom (R := S) ⊥ hc₄
  have hΨ : ∀ G, Ψ G = MvFormalGroup.adicEval (⊥ : Ideal (C₁ ⊗[S] C₂)) c₄ G :=
    fun G => congrFun (MvFormalGroup.coe_adicEvalAlgHom (R := S) ⊥ hc₄) G
  have hΨX : ∀ j, Ψ (MvPowerSeries.X j) = c₄ j := fun j => by rw [hΨ, MvFormalGroup.adicEval_X]
  have hbotC : ∀ s ∈ (⊥ : Ideal C₁), (Algebra.TensorProduct.includeLeft : C₁ →ₐ[S] C₁ ⊗[S] C₂) s ∈
      (⊥ : Ideal (C₁ ⊗[S] C₂)).radical := by
    intro s hs
    rw [(Submodule.mem_bot S).mp hs, map_zero]
    exact Ideal.zero_mem _
  have hbotC' : ∀ s ∈ (⊥ : Ideal C₂), (Algebra.TensorProduct.includeRight : C₂ →ₐ[S] C₁ ⊗[S] C₂) s ∈
      (⊥ : Ideal (C₁ ⊗[S] C₂)).radical := by
    intro s hs
    rw [(Submodule.mem_bot S).mp hs, map_zero]
    exact Ideal.zero_mem _
  have hΨL : ∀ f, Ψ (sL f) = θ₁ f ⊗ₜ[S] (1 : C₂) := by
    intro f
    rw [hsL, hΨ, MvFormalGroup.adicEval_subst ⊥ hc₄ hL f]
    have h1 : (fun t => MvFormalGroup.adicEval (⊥ : Ideal (C₁ ⊗[S] C₂)) c₄ (aL t)) = fun t => c₁ t ⊗ₜ[S] (1 : C₂) := by
      funext t
      exact MvFormalGroup.adicEval_X _ _ _
    rw [h1]
    have h2 : θ₁ f ⊗ₜ[S] (1 : C₂) = (Algebra.TensorProduct.includeLeft : C₁ →ₐ[S] C₁ ⊗[S] C₂) (θ₁ f) := rfl
    rw [h2, hev₁ f, MvFormalGroup.map_adicEval ⊥ ⊥ _ (Submodule.fg_bot) hbotC hc₁ f]
    rfl
  have hΨR : ∀ f, Ψ (sR f) = (1 : C₁) ⊗ₜ[S] θ₂ f := by
    intro f
    rw [hsR, hΨ, MvFormalGroup.adicEval_subst ⊥ hc₄ hR f]
    have h1 : (fun t => MvFormalGroup.adicEval (⊥ : Ideal (C₁ ⊗[S] C₂)) c₄ (aR t)) = fun t => (1 : C₁) ⊗ₜ[S] c₂ t := by
      funext t
      exact MvFormalGroup.adicEval_X _ _ _
    rw [h1]
    have h2 : (1 : C₁) ⊗ₜ[S] θ₂ f = (Algebra.TensorProduct.includeRight : C₂ →ₐ[S] C₁ ⊗[S] C₂) (θ₂ f) := rfl
    rw [h2, hev₂ f, MvFormalGroup.map_adicEval ⊥ ⊥ _ (Submodule.fg_bot) hbotC' hc₂ f]
    rfl

  have h0 : MvFormalGroup.adicEval (⊥ : Ideal (C₁ ⊗[S] C₂)) c₄ G = 0 ↔ Ψ G = 0 := by rw [hΨ]
  rw [h0]

  have hJΨ : ∀ g ∈ J, Ψ g = 0 := by
    have : J ≤ RingHom.ker Ψ := by
      rw [hJ_def, Ideal.span_le]
      rintro g (⟨f, hf, rfl⟩ | ⟨f, hf, rfl⟩)
      · show Ψ (MvPowerSeries.subst aL f) = 0
        rw [← hsL, hΨL, show θ₁ f = 0 from (RingHom.mem_ker).mp hf, TensorProduct.zero_tmul]
      · show Ψ (MvPowerSeries.subst aR f) = 0
        rw [← hsR, hΨR, show θ₂ f = 0 from (RingHom.mem_ker).mp hf, TensorProduct.tmul_zero]
    intro g hg
    exact (RingHom.mem_ker).mp (this hg)

  set 𝔫 : Ideal (MvPowerSeries (Fin 2 ⊕ Fin 2) S) :=
    Ideal.span (Set.range fun j : Fin 2 ⊕ Fin 2 => (MvPowerSeries.X j : MvPowerSeries (Fin 2 ⊕ Fin 2) S) ^ N)
    with h𝔫_def
  have hXker₁ : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ N ∈ RingHom.ker θ₁ := by
    intro i
    rw [RingHom.mem_ker]
    show θ₁ (MvPowerSeries.X i ^ N) = 0
    rw [map_pow]; exact hc₁N i
  have hXker₂ : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ N ∈ RingHom.ker θ₂ := by
    intro i
    rw [RingHom.mem_ker]
    show θ₂ (MvPowerSeries.X i ^ N) = 0
    rw [map_pow]; exact hc₂N i
  have h𝔫J : 𝔫 ≤ J := by
    rw [h𝔫_def, Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with i | i
    · have : (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (Fin 2 ⊕ Fin 2) S) ^ N =
          MvPowerSeries.subst aL ((MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ N) := by
        rw [← hsL, map_pow, hsL, MvPowerSeries.subst_X hL]
      show (MvPowerSeries.X (Sum.inl i) : MvPowerSeries (Fin 2 ⊕ Fin 2) S) ^ N ∈ J
      rw [this]
      exact Ideal.subset_span (Or.inl ⟨_, hXker₁ i, rfl⟩)
    · have : (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin 2 ⊕ Fin 2) S) ^ N =
          MvPowerSeries.subst aR ((MvPowerSeries.X i : MvPowerSeries (Fin 2) S) ^ N) := by
        rw [← hsR, map_pow, hsR, MvPowerSeries.subst_X hR]
      show (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin 2 ⊕ Fin 2) S) ^ N ∈ J
      rw [this]
      exact Ideal.subset_span (Or.inr ⟨_, hXker₂ i, rfl⟩)
  have h𝔫Ψ : ∀ g ∈ 𝔫, Ψ g = 0 := by
    have : 𝔫 ≤ RingHom.ker Ψ := by
      rw [h𝔫_def, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      show Ψ (MvPowerSeries.X j ^ N) = 0
      rw [map_pow, hΨX, hc₄N]
    intro g hg
    exact (RingHom.mem_ker).mp (this hg)

  obtain ⟨P, hP⟩ := exists_sub_coe_mem_span_X_pow N hNpos G
  have hGP : G = (↑P : MvPowerSeries (Fin 2 ⊕ Fin 2) S) + (G - ↑P) := by abel
  constructor
  swap
  · exact hJΨ G
  intro hΨG
  rw [hGP]
  refine Ideal.add_mem _ ?_ (h𝔫J hP)
  have hΨP : Ψ ↑P = 0 := by
    have : Ψ ↑P = Ψ G - Ψ (G - ↑P) := by rw [map_sub, sub_sub_cancel]
    rw [this, hΨG, h𝔫Ψ _ hP, sub_zero]

  let ι : MvPowerSeries (Fin 2) S ⊗[S] MvPowerSeries (Fin 2) S →ₐ[S] MvPowerSeries (Fin 2 ⊕ Fin 2) S :=
    Algebra.TensorProduct.productMap sL sR
  obtain ⟨q, hq⟩ := coe_mem_range_productMap sL sR (fun j => by
      rcases j with i | i
      · exact Or.inl ⟨i, by rw [hsL, MvPowerSeries.subst_X hL]⟩
      · exact Or.inr ⟨i, by rw [hsR, MvPowerSeries.subst_X hR]⟩) P
  rw [← hq]
  have hcomp : Ψ.comp ι = Algebra.TensorProduct.map θ₁ θ₂ := by
    apply Algebra.TensorProduct.ext
    · ext a
      show Ψ (ι (a ⊗ₜ[S] 1)) = Algebra.TensorProduct.map θ₁ θ₂ (a ⊗ₜ[S] 1)
      rw [Algebra.TensorProduct.map_tmul, show ι (a ⊗ₜ[S] 1) = sL a * sR 1 from
        Algebra.TensorProduct.productMap_apply_tmul sL sR a 1, map_one, mul_one, hΨL, map_one]
    · ext b
      show Ψ (ι (1 ⊗ₜ[S] b)) = Algebra.TensorProduct.map θ₁ θ₂ (1 ⊗ₜ[S] b)
      rw [Algebra.TensorProduct.map_tmul, show ι (1 ⊗ₜ[S] b) = sL 1 * sR b from
        Algebra.TensorProduct.productMap_apply_tmul sL sR 1 b, map_one, one_mul, hΨR, map_one]
  have hqker : q ∈ RingHom.ker (Algebra.TensorProduct.map θ₁ θ₂) := by
    rw [RingHom.mem_ker, ← hcomp]
    show Ψ (ι q) = 0
    rw [hq]; exact hΨP
  rw [Algebra.TensorProduct.map_ker _ _ hθ₁ hθ₂] at hqker
  have hιJ : Ideal.map (Algebra.TensorProduct.includeLeft :
        MvPowerSeries (Fin 2) S →ₐ[S] MvPowerSeries (Fin 2) S ⊗[S] MvPowerSeries (Fin 2) S) (RingHom.ker θ₁) ⊔
      Ideal.map (Algebra.TensorProduct.includeRight :
        MvPowerSeries (Fin 2) S →ₐ[S] MvPowerSeries (Fin 2) S ⊗[S] MvPowerSeries (Fin 2) S) (RingHom.ker θ₂) ≤
      J.comap ι := by
    apply sup_le
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      show ι (f ⊗ₜ[S] 1) ∈ J
      rw [show ι (f ⊗ₜ[S] 1) = sL f * sR 1 from Algebra.TensorProduct.productMap_apply_tmul sL sR f 1, map_one,
        mul_one, hsL]
      exact Ideal.subset_span (Or.inl ⟨f, hf, rfl⟩)
    · rw [Ideal.map_le_iff_le_comap]
      intro f hf
      show ι (1 ⊗ₜ[S] f) ∈ J
      rw [show ι (1 ⊗ₜ[S] f) = sL 1 * sR f from Algebra.TensorProduct.productMap_apply_tmul sL sR 1 f, map_one,
        one_mul, hsR]
      exact Ideal.subset_span (Or.inr ⟨f, hf, rfl⟩)
  exact hιJ hqker

namespace XAdicClosed

noncomputable section

open MvPowerSeries (coeff)

variable {σ τ : Type} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ] {B : Type} [CommRing B]

abbrev E : (σ ⊕ τ →₀ ℕ) ≃+ (σ →₀ ℕ) × (τ →₀ ℕ) := Finsupp.sumFinsuppAddEquivProdFinsupp

abbrev eL : σ ↪ σ ⊕ τ := Function.Embedding.inl
abbrev eR : τ ↪ σ ⊕ τ := Function.Embedding.inr

theorem E_symm_fst (a : σ →₀ ℕ) (b : τ →₀ ℕ) (i : σ) : ((E (σ := σ) (τ := τ)).symm (a, b)) (Sum.inl i) = a i :=
  Finsupp.sumElim_inl _ _ _

theorem E_symm_snd (a : σ →₀ ℕ) (b : τ →₀ ℕ) (j : τ) : ((E (σ := σ) (τ := τ)).symm (a, b)) (Sum.inr j) = b j :=
  Finsupp.sumElim_inr _ _ _

theorem E_symm_zero_left (b : τ →₀ ℕ) :
    (E (σ := σ) (τ := τ)).symm (0, b) = Finsupp.embDomain (eR (σ := σ) (τ := τ)) b := by
  ext s
  rcases s with i | j
  · rw [E_symm_fst, Finsupp.zero_apply, Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩; exact Sum.inr_ne_inl hj
  · rw [E_symm_snd]
    exact (Finsupp.embDomain_apply_self (eR (σ := σ) (τ := τ)) b j).symm

theorem E_symm_zero_right (a : σ →₀ ℕ) :
    (E (σ := σ) (τ := τ)).symm (a, 0) = Finsupp.embDomain (eL (σ := σ) (τ := τ)) a := by
  ext s
  rcases s with i | j
  · rw [E_symm_fst]
    exact (Finsupp.embDomain_apply_self (eL (σ := σ) (τ := τ)) a i).symm
  · rw [E_symm_snd, Finsupp.zero_apply, Finsupp.embDomain_notin_range]
    rintro ⟨i, hi⟩; exact Sum.inl_ne_inr hi

def xcoeff (a : σ →₀ ℕ) (G : MvPowerSeries (σ ⊕ τ) B) : MvPowerSeries τ B :=
  fun b => coeff ((E (σ := σ) (τ := τ)).symm (a, b)) G

theorem coeff_xcoeff (a : σ →₀ ℕ) (b : τ →₀ ℕ) (G : MvPowerSeries (σ ⊕ τ) B) :
    coeff b (xcoeff a G) = coeff ((E (σ := σ) (τ := τ)).symm (a, b)) G := rfl

theorem xcoeff_add (a : σ →₀ ℕ) (G H : MvPowerSeries (σ ⊕ τ) B) :
    xcoeff a (G + H) = xcoeff a G + xcoeff a H := by
  ext b; simp only [coeff_xcoeff, map_add]

theorem xcoeff_zero (a : σ →₀ ℕ) : xcoeff a (0 : MvPowerSeries (σ ⊕ τ) B) = 0 := by
  ext b; simp only [coeff_xcoeff, map_zero]

theorem xcoeff_sum (a : σ →₀ ℕ) {ι : Type} (s : Finset ι) (G : ι → MvPowerSeries (σ ⊕ τ) B) :
    xcoeff a (∑ i ∈ s, G i) = ∑ i ∈ s, xcoeff a (G i) := by
  ext b; simp only [coeff_xcoeff, map_sum]

theorem eq_of_xcoeff_eq (G H : MvPowerSeries (σ ⊕ τ) B) (h : ∀ a, xcoeff a G = xcoeff a H) : G = H := by
  ext e
  have := congrArg (coeff ((E (σ := σ) (τ := τ)) e).2) (h ((E (σ := σ) (τ := τ)) e).1)
  rw [coeff_xcoeff, coeff_xcoeff, Prod.mk.eta, AddEquiv.symm_apply_apply] at this
  exact this

theorem coeff_E_symm_mul (a : σ →₀ ℕ) (b : τ →₀ ℕ) (c G : MvPowerSeries (σ ⊕ τ) B) :
    coeff ((E (σ := σ) (τ := τ)).symm (a, b)) (c * G) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, ∑ q ∈ Finset.HasAntidiagonal.antidiagonal b,
        coeff ((E (σ := σ) (τ := τ)).symm (p.1, q.1)) c * coeff ((E (σ := σ) (τ := τ)).symm (p.2, q.2)) G := by
  classical
  rw [MvPowerSeries.coeff_mul, ← Finset.sum_product']
  symm
  apply Finset.sum_nbij'
    (fun pq => ((E (σ := σ) (τ := τ)).symm (pq.1.1, pq.2.1), (E (σ := σ) (τ := τ)).symm (pq.1.2, pq.2.2)))
    (fun r => ((((E (σ := σ) (τ := τ)) r.1).1, ((E (σ := σ) (τ := τ)) r.2).1),
      (((E (σ := σ) (τ := τ)) r.1).2, ((E (σ := σ) (τ := τ)) r.2).2)))
  · intro pq hpq
    rw [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.HasAntidiagonal.mem_antidiagonal] at hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal, ← map_add, Prod.mk_add_mk, hpq.1, hpq.2]
  · intro r hr
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hr
    have h := congrArg (E (σ := σ) (τ := τ)) hr
    rw [map_add, AddEquiv.apply_symm_apply, Prod.ext_iff, Prod.fst_add, Prod.snd_add] at h
    rw [Finset.mem_product, Finset.HasAntidiagonal.mem_antidiagonal, Finset.HasAntidiagonal.mem_antidiagonal]
    exact ⟨h.1, h.2⟩
  · intro pq _
    simp only [AddEquiv.apply_symm_apply, Prod.mk.eta]
  · intro r _
    simp only [Prod.mk.eta, AddEquiv.symm_apply_apply]
  · intro pq _
    rfl

theorem xcoeff_mul (a : σ →₀ ℕ) (c G : MvPowerSeries (σ ⊕ τ) B) :
    xcoeff a (c * G) = ∑ p ∈ Finset.HasAntidiagonal.antidiagonal a, xcoeff p.1 c * xcoeff p.2 G := by
  ext b
  rw [coeff_xcoeff, coeff_E_symm_mul, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [MvPowerSeries.coeff_mul]
  exact Finset.sum_congr rfl fun q _ => rfl

theorem xcoeff_rename_inr (a : σ →₀ ℕ) (f : MvPowerSeries τ B) :
    xcoeff a (MvPowerSeries.rename (eR (σ := σ) (τ := τ)) f) = if a = 0 then f else 0 := by
  classical
  ext b
  rw [coeff_xcoeff]
  split_ifs with ha
  · rw [ha, E_symm_zero_left, MvPowerSeries.coeff_embDomain_rename]
  · rw [map_zero]
    apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply ha
    ext i
    have := congrArg (fun e : σ ⊕ τ →₀ ℕ => e (Sum.inl i)) hy
    simp only [E_symm_fst] at this
    rw [← this, Finsupp.zero_apply, ← Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_notin_range]
    rintro ⟨j, hj⟩; exact Sum.inr_ne_inl hj

theorem xcoeff_rename_inl (a : σ →₀ ℕ) (m : MvPowerSeries σ B) :
    xcoeff a (MvPowerSeries.rename (eL (σ := σ) (τ := τ)) m) = MvPowerSeries.C (coeff a m) := by
  classical
  ext b
  rw [coeff_xcoeff, MvPowerSeries.coeff_C]
  split_ifs with hb
  · rw [hb, E_symm_zero_right, MvPowerSeries.coeff_embDomain_rename]
  · apply MvPowerSeries.coeff_rename_eq_zero
    rintro ⟨y, hy⟩
    apply hb
    ext j
    have := congrArg (fun e : σ ⊕ τ →₀ ℕ => e (Sum.inr j)) hy
    simp only [E_symm_snd] at this
    rw [← this, Finsupp.zero_apply, ← Finsupp.embDomain_eq_mapDomain, Finsupp.embDomain_notin_range]
    rintro ⟨i, hi⟩; exact Sum.inl_ne_inr hi

theorem coeff_eq_zero_of_mem_pow (k : ℕ) :
    ∀ m ∈ (Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ B))) ^ k,
      ∀ d : σ →₀ ℕ, Finsupp.degree d < k → coeff d m = 0 := by
  classical
  induction k with
  | zero => intro m _ d hd; exact absurd hd (Nat.not_lt_zero _)
  | succ k ih =>
    intro m hm
    rw [pow_succ] at hm
    refine Submodule.mul_induction_on hm ?_ ?_
    · intro x hx y hy d hd
      rw [MvPowerSeries.coeff_mul]
      refine Finset.sum_eq_zero fun r hr => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hr
      by_cases h1 : Finsupp.degree r.1 < k
      · rw [ih x hx r.1 h1, zero_mul]
      · have hdeg : Finsupp.degree r.1 + Finsupp.degree r.2 = Finsupp.degree d := by rw [← map_add, hr]
        have h2 : Finsupp.degree r.2 = 0 := by omega
        rw [Finsupp.degree_eq_zero_iff] at h2
        rw [h2]
        have hy0 : coeff (0 : σ →₀ ℕ) y = 0 := by
          have hle : Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ B)) ≤
              RingHom.ker (MvPowerSeries.constantCoeff : MvPowerSeries σ B →+* B) := by
            rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact MvPowerSeries.constantCoeff_X i
          have := hle hy
          rw [RingHom.mem_ker] at this
          rw [MvPowerSeries.coeff_zero_eq_constantCoeff]; exact this
        rw [hy0, mul_zero]
    · intro x y hx hy d hd
      rw [map_add, hx d hd, hy d hd, add_zero]

theorem xcoeff_mem_of_mem_span_inr (I : Ideal (MvPowerSeries τ B)) :
    ∀ G ∈ Ideal.span ((MvPowerSeries.rename (eR (σ := σ) (τ := τ))) '' (I : Set (MvPowerSeries τ B))),
      ∀ a : σ →₀ ℕ, xcoeff a G ∈ I := by
  intro G hG
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hG
  · rintro _ ⟨f, hf, rfl⟩ a
    rw [xcoeff_rename_inr]
    split_ifs
    · exact hf
    · exact I.zero_mem
  · intro a; rw [xcoeff_zero]; exact I.zero_mem
  · intro x y _ _ hx hy a
    rw [xcoeff_add]; exact I.add_mem (hx a) (hy a)
  · intro c x _ hx a
    rw [smul_eq_mul, xcoeff_mul]
    exact I.sum_mem fun p _ => I.mul_mem_left _ (hx p.2)

theorem xcoeff_eq_zero_of_mem_span_inl (n : ℕ) :
    ∀ G ∈ Ideal.span ((MvPowerSeries.rename (eL (σ := σ) (τ := τ))) ''
        (((Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ B))) ^ (n + 1) :
          Ideal (MvPowerSeries σ B)) : Set (MvPowerSeries σ B))),
      ∀ a : σ →₀ ℕ, Finsupp.degree a ≤ n → xcoeff a G = 0 := by
  intro G hG
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hG
  · rintro _ ⟨m, hm, rfl⟩ a ha
    rw [xcoeff_rename_inl, coeff_eq_zero_of_mem_pow (n + 1) m hm a (by omega), map_zero]
  · intro a _; exact xcoeff_zero a
  · intro x y _ _ hx hy a ha
    rw [xcoeff_add, hx a ha, hy a ha, add_zero]
  · intro c x _ hx a ha
    rw [smul_eq_mul, xcoeff_mul]
    refine Finset.sum_eq_zero fun p hp => ?_
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have : Finsupp.degree p.2 ≤ n := by
      have := congrArg Finsupp.degree hp
      rw [map_add] at this; omega
    rw [hx p.2 this, mul_zero]

theorem mem_span_inr_of_forall (I : Ideal (MvPowerSeries τ B)) (hI : I.FG) (G : MvPowerSeries (σ ⊕ τ) B)
    (h : ∀ n : ℕ, G ∈ Ideal.span
      ((MvPowerSeries.rename (eL (σ := σ) (τ := τ))) ''
          (((Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ B))) ^ (n + 1) :
            Ideal (MvPowerSeries σ B)) : Set (MvPowerSeries σ B)) ∪
        (MvPowerSeries.rename (eR (σ := σ) (τ := τ))) '' (I : Set (MvPowerSeries τ B)))) :
    G ∈ Ideal.span ((MvPowerSeries.rename (eR (σ := σ) (τ := τ))) '' (I : Set (MvPowerSeries τ B))) := by
  classical

  have hcoef : ∀ a : σ →₀ ℕ, xcoeff a G ∈ I := by
    intro a
    have hn := h (Finsupp.degree a)
    rw [Ideal.span_union] at hn
    obtain ⟨k, hk, j, hj, rfl⟩ := Submodule.mem_sup.mp hn
    rw [xcoeff_add, xcoeff_eq_zero_of_mem_span_inl _ k hk a le_rfl, zero_add]
    exact xcoeff_mem_of_mem_span_inr I j hj a

  obtain ⟨m, f, hf⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hI
  have hcf : ∀ a : σ →₀ ℕ, ∃ c : Fin m → MvPowerSeries τ B, ∑ i, c i • f i = xcoeff a G := fun a =>
    (Submodule.mem_span_range_iff_exists_fun _).mp (by rw [hf]; exact hcoef a)
  choose cf hcf using hcf
  let H : Fin m → MvPowerSeries (σ ⊕ τ) B := fun i e =>
    coeff ((E (σ := σ) (τ := τ)) e).2 (cf ((E (σ := σ) (τ := τ)) e).1 i)
  have hH : ∀ a i, xcoeff a (H i) = cf a i := by
    intro a i
    ext b
    rw [coeff_xcoeff]
    show coeff ((E (σ := σ) (τ := τ)) ((E (σ := σ) (τ := τ)).symm (a, b))).2
      (cf ((E (σ := σ) (τ := τ)) ((E (σ := σ) (τ := τ)).symm (a, b))).1 i) = coeff b (cf a i)
    rw [AddEquiv.apply_symm_apply]
  let G' : MvPowerSeries (σ ⊕ τ) B := ∑ i, MvPowerSeries.rename (eR (σ := σ) (τ := τ)) (f i) * H i
  have hG' : G = G' := by
    apply eq_of_xcoeff_eq
    intro a
    rw [xcoeff_sum]
    rw [← hcf a]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [xcoeff_mul, Finset.sum_eq_single (0, a)]
    · rw [xcoeff_rename_inr, if_pos rfl, hH, smul_eq_mul, mul_comm]
    · intro p hp hne
      rw [xcoeff_rename_inr]
      split_ifs with h0
      · exfalso
        apply hne
        rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
        ext <;> simp [h0, ← hp]
      · rw [zero_mul]
    · intro hna
      exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (zero_add a)) hna
  rw [hG']
  refine Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨f i, ?_, rfl⟩)
  have : f i ∈ Submodule.span (MvPowerSeries τ B) (Set.range f) := Submodule.subset_span ⟨i, rfl⟩
  rw [hf] at this
  exact this

end

end XAdicClosed

theorem solution
    {B : Type} [CommRing B]
    (I : Ideal (MvPowerSeries (Fin 2) B)) (hI : I.FG)
    {L : Type} [CommRing L] [Algebra B L]
    (π : MvPowerSeries (Fin 2) B →ₐ[B] L) (hπ : Function.Surjective π) (hker : RingHom.ker π = I)
    (hπnil : ∀ i, IsNilpotent (π (MvPowerSeries.X i)))
    (hev : ∀ G, π G = MvFormalGroup.adicEval (⊥ : Ideal L) (fun i => π (MvPowerSeries.X i)) G)
    (G : MvPowerSeries (Fin 2 ⊕ Fin 2) B)
    (hG : ∀ n : ℕ,
      MvFormalGroup.adicEval
        (⊥ : Ideal ((MvPowerSeries (Fin 2) B ⧸
          (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))) ^ (n + 1)) ⊗[B] L))
        (Sum.elim
          (fun j => Ideal.Quotient.mk
            ((Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))) ^ (n + 1))
              (MvPowerSeries.X j) ⊗ₜ[B] (1 : L))
          (fun j => (1 : MvPowerSeries (Fin 2) B ⧸
            (Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B))) ^ (n + 1)) ⊗ₜ[B]
              π (MvPowerSeries.X j))) G = 0) :
    G ∈ Ideal.span
        ((MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B))) ''
            (I : Set (MvPowerSeries (Fin 2) B))) := by
  classical
  set 𝔪 : Ideal (MvPowerSeries (Fin 2) B) :=
    Ideal.span (Set.range (MvPowerSeries.X : Fin 2 → MvPowerSeries (Fin 2) B)) with h𝔪_def

  have hRfun : (⇑(MvPowerSeries.rename (⇑(XAdicClosed.eR (σ := Fin 2) (τ := Fin 2))) :
        MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
        MvPowerSeries (Fin 2) B → MvPowerSeries (Fin 2 ⊕ Fin 2) B) =
      MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inr l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) := by
    funext f
    rw [MvPowerSeries.rename_eq_subst]
    rfl
  have hLfun : (⇑(MvPowerSeries.rename (⇑(XAdicClosed.eL (σ := Fin 2) (τ := Fin 2))) :
        MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2 ⊕ Fin 2) B) :
        MvPowerSeries (Fin 2) B → MvPowerSeries (Fin 2 ⊕ Fin 2) B) =
      MvPowerSeries.subst (fun l => (MvPowerSeries.X (Sum.inl l) : MvPowerSeries (Fin 2 ⊕ Fin 2) B)) := by
    funext f
    rw [MvPowerSeries.rename_eq_subst]
    rfl
  rw [← hRfun]
  apply XAdicClosed.mem_span_inr_of_forall I hI G
  intro n
  rw [hRfun, hLfun]

  let θ₁ : MvPowerSeries (Fin 2) B →ₐ[B] MvPowerSeries (Fin 2) B ⧸ 𝔪 ^ (n + 1) := Ideal.Quotient.mkₐ B (𝔪 ^ (n + 1))
  have hθ₁ : Function.Surjective θ₁ := Ideal.Quotient.mkₐ_surjective B _
  have hXmem : ∀ i, (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (n + 1) ∈ 𝔪 ^ (n + 1) := fun i =>
    Ideal.pow_mem_pow (show (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ∈ 𝔪 from
      Ideal.subset_span (Set.mem_range_self i)) (n + 1)
  have hX₁ : ∀ i, IsNilpotent (θ₁ (MvPowerSeries.X i)) := fun i =>
    ⟨n + 1, by rw [← map_pow]; exact Ideal.Quotient.eq_zero_iff_mem.mpr (hXmem i)⟩
  have hrad₁ : ∀ i, θ₁ (MvPowerSeries.X i) ∈ (⊥ : Ideal (MvPowerSeries (Fin 2) B ⧸ 𝔪 ^ (n + 1))).radical := fun i =>
    ⟨n + 1, by rw [← map_pow]; exact (Submodule.mem_bot _).mpr (Ideal.Quotient.eq_zero_iff_mem.mpr (hXmem i))⟩
  have hev₁ : ∀ G, θ₁ G = MvFormalGroup.adicEval (⊥ : Ideal (MvPowerSeries (Fin 2) B ⧸ 𝔪 ^ (n + 1)))
      (fun i => θ₁ (MvPowerSeries.X i)) G := fun G =>
    MvFormalGroup.algHom_apply_eq_adicEval_of_forall_apply_X_mem_radical ⊥ θ₁ hrad₁ G
  have key := (genTensorTrunc θ₁ π hθ₁ hπ hX₁ hπnil hev₁ hev G).mp (hG n)
  have hkerθ : RingHom.ker θ₁ = 𝔪 ^ (n + 1) :=
    Ideal.ext fun x => by rw [RingHom.mem_ker]; exact Ideal.Quotient.eq_zero_iff_mem
  rw [hkerθ, hker] at key
  exact key

end S_MvPowerSeries_mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective
end P2MW
export P2MW.S_MvPowerSeries_mem_span_image_subst_inr_of_forall_adicEval_eq_zero_of_surjective (solution)
