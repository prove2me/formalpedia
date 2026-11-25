-- Prove2me | solution 1 for GlobalTheory.SW.finite_cls_and_stab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:38:19.008302+00:00
-- url     : https://prove2.me/submissions/6bfaa97d-929d-41a5-83a1-929c4dc6d9ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClassesSelfDualOfSelfDual
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FiniteClsAndStab
import Theorems.Thm_GlobalTheory_SW_Base_ccT_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_cls_eq_iff
import Theorems.Thm_GlobalTheory_SW_Base_herm_one
import Theorems.Thm_GlobalTheory_SW_Base_map_cc
import Theorems.Thm_GlobalTheory_SW_Base_mem_stdL
import Theorems.Thm_GlobalTheory_SW_Base_moves_one
import Theorems.Thm_GlobalTheory_SW_Base_mul_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_nat_smul_mem
import Theorems.Thm_GlobalTheory_SW_Base_one_mem_DH
import Theorems.Thm_GlobalTheory_SW_Base_stdL_mem_Vset
import Theorems.Thm_GlobalTheory_finite_classes_selfDual_level

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW.ClassFin
open GlobalTheory.SW.Base
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
end GlobalTheory.SW.ClassFin
namespace GlobalTheory.SW
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma exists_scale_one_mod_M_of_mem_Vset (M : ℕ) (hM : 0 < M) {Λ : _root_.GlobalTheory.SW.Lt E n}
    (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) :
    ∃ s t : ℕ, s = 1 + M * t ∧ (∀ v ∈ Λ, (s : E) • v ∈ _root_.GlobalTheory.SW.stdL E n) ∧
      ∀ v ∈ _root_.GlobalTheory.SW.stdL E n, (s : E) • v ∈ Λ := by
  obtain ⟨-, -, s₀, hs₀, hc, hstd, hΛs⟩ := hΛ
  have hφ : 0 < M.totient := Nat.totient_pos.2 hM
  have hmod : s₀ ^ M.totient ≡ 1 [MOD M] := Nat.ModEq.pow_totient hc
  have h1 : 1 ≤ s₀ ^ M.totient := Nat.one_le_pow _ _ hs₀
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' h1).1 hmod.symm
  have hpow : ((s₀ ^ (M.totient - 1) : ℕ) : E) * s₀ = ((s₀ ^ M.totient : ℕ) : E) := by
    rw [← Nat.cast_mul, ← pow_succ, Nat.sub_add_cancel hφ]
  refine ⟨s₀ ^ M.totient, t, by rw [← ht, Nat.add_sub_cancel' h1], fun v hv => ?_, fun v hv => ?_⟩
  · have := _root_.GlobalTheory.SW.Base.nat_smul_mem _ (s₀ ^ (M.totient - 1)) (hstd v hv)
    rwa [smul_smul, hpow] at this
  · have := _root_.GlobalTheory.SW.Base.nat_smul_mem _ (s₀ ^ (M.totient - 1)) (hΛs v hv)
    rwa [smul_smul, hpow] at this
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma ccT_apply (A : Matrix (Fin n) (Fin n) E) (i j : Fin n) :
    _root_.GlobalTheory.SW.ccT A i j = _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (A j i) := by
  simp [_root_.GlobalTheory.SW.ccT]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma unitary_of_hermitian_mulVec {h : Matrix (Fin n) (Fin n) E}
    (H : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (h *ᵥ x) (h *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y) :
    _root_.GlobalTheory.SW.ccT h * h = 1 := by
  ext j i
  have := H (Pi.single i 1) (Pi.single j 1)
  rw [_root_.GlobalTheory.SW.Base.herm_one, _root_.GlobalTheory.SW.Base.herm_one, Matrix.mulVec_single_one,
    Matrix.mulVec_single_one] at this
  rw [Matrix.mul_apply]
  simp only [ccT_apply, Matrix.transpose_apply, Matrix.col_apply] at this ⊢
  rw [Finset.sum_congr rfl (fun a _ => mul_comm _ _), this]
  simp [Pi.single_apply, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, Matrix.one_apply, eq_comm]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma single_mem_stdL' (a : Fin n) :
    (Pi.single a 1 : Fin n → E) ∈ _root_.GlobalTheory.SW.stdL E n := by
  rw [_root_.GlobalTheory.SW.Base.mem_stdL]
  intro b
  rw [Pi.single_apply]
  split_ifs <;> simp [isIntegral_one, isIntegral_zero]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma related_of_same_reduction_lemma_5 (M : ℕ) {Λ₁ Λ₂ : _root_.GlobalTheory.SW.Lt E n}
    (Q : Submodule (𝓞 E) (Fin n → E)) (q : Q →ₗ[𝓞 E] (Fin n → 𝓞 E ⧸ Ideal.span {(M : 𝓞 E)}))
    (s₁ t₁ s₂ t₂ : ℕ) (hst₁ : s₁ = 1 + M * t₁) (hst₂ : s₂ = 1 + M * t₂)
    (hstd₁ : ∀ v ∈ Λ₁, (s₁ : E) • v ∈ _root_.GlobalTheory.SW.stdL E n)
    (hΛs₁ : ∀ v ∈ _root_.GlobalTheory.SW.stdL E n, (s₁ : E) • v ∈ Λ₁)
    (hstd₂ : ∀ v ∈ Λ₂, (s₂ : E) • v ∈ _root_.GlobalTheory.SW.stdL E n)
    (γ₁ γ₂ : (Fin n → E) ≃ₗ[E] (Fin n → E))
    (hγ₁ : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (γ₁ x) (γ₁ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)
    (hγ₂ : ∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (γ₂ x) (γ₂ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y)
    (hmem₁ : ∀ x, x ∈ Q ↔ γ₁ x ∈ Λ₁) (hmem₂ : ∀ x, x ∈ Q ↔ γ₂ x ∈ Λ₂)
    (hf₁ : ∀ x (hx : x ∈ Q) (a : Fin n) (hint : IsIntegral ℤ ((s₁ : E) * γ₁ x a)),
      q ⟨x, hx⟩ a = Ideal.Quotient.mk _ ⟨(s₁ : E) * γ₁ x a, hint⟩)
    (hf₂ : ∀ x (hx : x ∈ Q) (a : Fin n) (hint : IsIntegral ℤ ((s₂ : E) * γ₂ x a)),
      q ⟨x, hx⟩ a = Ideal.Quotient.mk _ ⟨(s₂ : E) * γ₂ x a, hint⟩) :
    ∃ h ∈ _root_.GlobalTheory.SW.DH E n M, _root_.GlobalTheory.SW.Moves h Λ₁ Λ₂ := by
  set h := LinearMap.toMatrix' ((γ₂ : (Fin n → E) →ₗ[E] (Fin n → E)) ∘ₗ
    (γ₁.symm : (Fin n → E) →ₗ[E] (Fin n → E))) with hdef
  have hmv : ∀ v, h *ᵥ v = γ₂ (γ₁.symm v) := fun v => by
    rw [hdef, LinearMap.toMatrix'_mulVec]
    rfl
  have hu : _root_.GlobalTheory.SW.ccT h * h = 1 := unitary_of_hermitian_mulVec fun x y => by
    rw [hmv, hmv, hγ₂, ← hγ₁, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  refine ⟨h, ⟨hu, s₁ * s₂, ?_, ?_, ?_⟩, fun v => by
    rw [hmv, ← hmem₂, hmem₁, LinearEquiv.apply_symm_apply]⟩
  · rw [hst₁, hst₂]
    positivity
  · rw [hst₁, hst₂]
    exact Nat.Coprime.mul (by simp) (by simp)
  · have hcong : ∀ a i, ∃ c : E, IsIntegral ℤ c ∧
        (s₁ : E) * ((s₁ : E) * (Pi.single i (1 : E) : Fin n → E) a) - s₂ * (s₁ * h a i) = c * M := by
      intro a i
      have hv : (s₁ : E) • (Pi.single i 1 : Fin n → E) ∈ Λ₁ := hΛs₁ _ (single_mem_stdL' i)
      set x := γ₁.symm ((s₁ : E) • (Pi.single i 1 : Fin n → E)) with hx
      have hγx : γ₁ x = (s₁ : E) • Pi.single i 1 := γ₁.apply_symm_apply _
      have hxQ : x ∈ Q := (hmem₁ x).2 (hγx ▸ hv)
      have hγ₂x : γ₂ x = h *ᵥ ((s₁ : E) • Pi.single i 1) := (hmv _).symm
      have hint₁ : IsIntegral ℤ ((s₁ : E) * γ₁ x a) := by
        have := (_root_.GlobalTheory.SW.Base.mem_stdL _).1 (hstd₁ _ ((hmem₁ x).1 hxQ)) a
        rwa [Pi.smul_apply, smul_eq_mul] at this
      have hint₂ : IsIntegral ℤ ((s₂ : E) * γ₂ x a) := by
        have := (_root_.GlobalTheory.SW.Base.mem_stdL _).1 (hstd₂ _ ((hmem₂ x).1 hxQ)) a
        rwa [Pi.smul_apply, smul_eq_mul] at this
      have heq := (hf₁ x hxQ a hint₁).symm.trans (hf₂ x hxQ a hint₂)
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 heq)
      refine ⟨c, c.isIntegral_coe, ?_⟩
      have hce : (c : E) * M = (s₁ : E) * γ₁ x a - s₂ * γ₂ x a := by
        have := congrArg (algebraMap (𝓞 E) E) hc
        rw [map_mul, map_natCast] at this
        exact this
      rw [hce, hγx, hγ₂x, Matrix.mulVec_smul, Matrix.mulVec_single_one]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.col_apply]
    choose c hc hce using hcong
    refine ⟨fun a i => -c a i + s₁ * ((t₁ : E) - t₂) * (Pi.single i (1 : E) : Fin n → E) a, ?_, ?_⟩
    · intro a i
      refine (hc a i).neg.add (((isIntegral_natCast s₁).mul
        ((isIntegral_natCast t₁).sub (isIntegral_natCast t₂))).mul ?_)
      rw [Pi.single_apply]
      split_ifs <;> simp [isIntegral_one, isIntegral_zero]
    · ext a i
      have e₁ : (s₁ : E) = 1 + M * t₁ := by rw [hst₁]; push_cast; ring
      have e₂ : (s₂ : E) = 1 + M * t₂ := by rw [hst₂]; push_cast; ring
      have hδ : (1 : Matrix (Fin n) (Fin n) E) a i = (Pi.single i (1 : E) : Fin n → E) a := by
        rw [Matrix.one_apply, Pi.single_apply]
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, hδ, Pi.smul_apply]
      change _ = (M : E) * (-c a i + (s₁ : E) * ((t₁ : E) - t₂) * (Pi.single i (1 : E) : Fin n → E) a)
      push_cast
      linear_combination (-1 : E) * hce a i + (s₁ : E) * (Pi.single i (1 : E) : Fin n → E) a * (e₁ - e₂)
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma finite_cls' (M : ℕ) (hM : 0 < M) : Finite (_root_.GlobalTheory.SW.Cls E n M) := by
  obtain ⟨S, -, hS2⟩ := _root_.GlobalTheory.finite_classes_selfDual_level (E := E) n M hM.ne'
  have key : ∀ Λ : _root_.GlobalTheory.SW.Vset E n M, ∃ P ∈ S, ∃ s t : ℕ, s = 1 + M * t ∧
      (∀ v ∈ (Λ : _root_.GlobalTheory.SW.Lt E n), (s : E) • v ∈ _root_.GlobalTheory.SW.stdL E n) ∧
      (∀ v ∈ _root_.GlobalTheory.SW.stdL E n, (s : E) • v ∈ (Λ : _root_.GlobalTheory.SW.Lt E n)) ∧
      ∃ γ : (Fin n → E) ≃ₗ[E] (Fin n → E), (∀ x y, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (γ x) (γ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y) ∧
        (∀ x, x ∈ P.1 ↔ γ x ∈ (Λ : _root_.GlobalTheory.SW.Lt E n)) ∧
        ∀ x (hx : x ∈ P.1) (a : Fin n) (hint : IsIntegral ℤ ((s : E) * γ x a)),
          P.2 ⟨x, hx⟩ a = Ideal.Quotient.mk _ ⟨(s : E) * γ x a, hint⟩ := by
    rintro ⟨Λ, hΛ⟩
    obtain ⟨s, t, hst, hstd, hΛs⟩ := exists_scale_one_mod_M_of_mem_Vset M hM hΛ
    obtain ⟨hfg, hsd, -⟩ := hΛ
    obtain ⟨P, hP, γ, hγ, hmem, hf⟩ := hS2 Λ hfg (fun x hx y hy => (hsd x).1 hx y hy)
      (fun x hx => (hsd x).2 hx) (_root_.GlobalTheory.SW.ClassFin.red M Λ s hstd)
    exact ⟨P, hP, s, t, hst, hstd, hΛs, γ, hγ, hmem, fun x hx a hint => by rw [hf ⟨x, hx⟩]; rfl⟩
  choose P hPS s t hst hstd hΛs γ hγ hmem hf using key
  let F : _root_.GlobalTheory.SW.Cls E n M → S := fun c => ⟨P (Quot.out c), hPS _⟩
  refine Finite.of_injective F fun c₁ c₂ hc => ?_
  have hP : P (Quot.out c₁) = P (Quot.out c₂) := congrArg Subtype.val hc
  rw [← Quot.out_eq c₁, ← Quot.out_eq c₂]
  apply (_root_.GlobalTheory.SW.Base.cls_eq_iff _ _).2
  have hmem₁ := hmem (Quot.out c₁)
  have hf₁ := hf (Quot.out c₁)
  rw [hP] at hmem₁ hf₁
  exact related_of_same_reduction_lemma_5 M (P (Quot.out c₂)).1 (P (Quot.out c₂)).2 _ _ _ _
    (hst _) (hst _) (hstd _) (hΛs _) (hstd _) (γ _) (γ _) (hγ _) (hγ _) hmem₁ (hmem _) hf₁ (hf _)
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma finite_integral_multiple_embeddings_bounded (s : ℕ) (hs : 0 < s) :
    {x : E | IsIntegral ℤ ((s : E) * x) ∧ ∀ τ : E →+* ℂ, ‖τ x‖ ≤ 1}.Finite := by
  refine ((NumberField.Embeddings.finite_of_norm_le E ℂ (s : ℝ)).image fun y : E => y / s).subset ?_
  rintro x ⟨hx, hb⟩
  have hs' : (s : E) ≠ 0 := by exact_mod_cast hs.ne'
  refine ⟨(s : E) * x, ⟨hx, fun τ => ?_⟩, by field_simp⟩
  rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
  simpa using mul_le_mul_of_nonneg_left (hb τ) (Nat.cast_nonneg (α := ℝ) s)
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma sum_conj_mul_eq_of_unitary {h : Matrix (Fin n) (Fin n) E}
    (hh : _root_.GlobalTheory.SW.ccT h * h = 1) (i j : Fin n) :
    ∑ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (h a j) * h a i = (1 : Matrix (Fin n) (Fin n) E) j i := by
  rw [← hh, Matrix.mul_apply]
  simp [ccT_apply]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma norm_embedding_entry_le_one_of_unitary {h : Matrix (Fin n) (Fin n) E}
    (hh : _root_.GlobalTheory.SW.ccT h * h = 1) (τ : E →+* ℂ) (k a : Fin n) : ‖τ (h k a)‖ ≤ 1 := by
  have key := congrArg τ (sum_conj_mul_eq_of_unitary hh a a)
  simp only [map_sum, map_mul, _root_.GlobalTheory.SW.Base.map_cc, Matrix.one_apply_eq, map_one] at key
  have hsum : ∑ b, ‖τ (h b a)‖ ^ 2 = 1 := by
    have : ((∑ b, ‖τ (h b a)‖ ^ 2 : ℝ) : ℂ) = 1 := by
      push_cast
      rw [← key]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Complex.conj_mul']
    exact_mod_cast this
  have hle : ‖τ (h k a)‖ ^ 2 ≤ 1 := hsum ▸ Finset.single_le_sum
    (f := fun b => ‖τ (h b a)‖ ^ 2) (fun b _ => by positivity) (Finset.mem_univ k)
  exact (sq_le_one_iff₀ (norm_nonneg _)).1 hle
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma finite_stabiliser_DH (M : ℕ) {Λ : _root_.GlobalTheory.SW.Lt E n}
    (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) :
    {h ∈ _root_.GlobalTheory.SW.DH E n M | _root_.GlobalTheory.SW.Moves h Λ Λ}.Finite := by
  obtain ⟨-, -, s, hs, -, hstd, hΛs⟩ := hΛ
  have hT := finite_integral_multiple_embeddings_bounded (E := E) (s * s) (Nat.mul_pos hs hs)
  refine (Set.Finite.pi (t := fun _ : Fin n => Set.pi Set.univ fun _ : Fin n => _)
    fun _ => Set.Finite.pi fun _ => hT).subset ?_
  rintro (h : Matrix (Fin n) (Fin n) E) ⟨⟨hu, -⟩, hmov⟩
  intro k _ a _
  refine ⟨?_, fun τ => norm_embedding_entry_le_one_of_unitary hu τ k a⟩
  have h1 := hstd _ ((hmov _).1 (hΛs _ (single_mem_stdL' a)))
  rw [_root_.GlobalTheory.SW.Base.mem_stdL] at h1
  have h2 := h1 k
  rw [Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, Matrix.mulVec_single_one, smul_eq_mul,
    smul_eq_mul] at h2
  have e : ((s * s : ℕ) : E) * h k a = (s : E) * ((s : E) * h.col a k) := by
    push_cast
    rw [mul_assoc]
    rfl
  rw [e]
  exact h2
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma herm_one_mulVec_of_unitary {h : Matrix (Fin n) (Fin n) E}
    (hh : _root_.GlobalTheory.SW.ccT h * h = 1) (x y : Fin n → E) :
    _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 (h *ᵥ x) (h *ᵥ y) = _root_.ReciprocityTheory.ChartRestriction.G.FD.herm 1 x y := by
  have key := sum_conj_mul_eq_of_unitary hh
  rw [_root_.GlobalTheory.SW.Base.herm_one, _root_.GlobalTheory.SW.Base.herm_one]
  calc ∑ a, (h *ᵥ x) a * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc ((h *ᵥ y) a)
      = ∑ i, ∑ j, x i * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y j) * ∑ a, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (h a j) * h a i := by
        simp only [Matrix.mulVec, dotProduct, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc, map_sum, map_mul, Finset.sum_mul,
          Finset.mul_sum]
        have e : ∀ f : Fin n → Fin n → Fin n → E,
            ∑ a, ∑ i, ∑ j, f a i j = ∑ j, ∑ i, ∑ a, f a i j := fun f => by
          calc _ = ∑ a, ∑ j, ∑ i, f a i j := Finset.sum_congr rfl fun a _ => Finset.sum_comm
            _ = ∑ j, ∑ a, ∑ i, f a i j := Finset.sum_comm
            _ = _ := Finset.sum_congr rfl fun j _ => Finset.sum_comm
        refine (e _).trans ?_
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun a _ => ?_
        ring
    _ = ∑ i, x i * _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (y i) := by
        simp only [key, Matrix.one_apply]
        simp
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma exists_coprime_scale_integral_entries_of_mem_DH {M : ℕ} {h : Matrix (Fin n) (Fin n) E}
    (hh : h ∈ _root_.GlobalTheory.SW.DH E n M) :
    ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧ ∀ k i, IsIntegral ℤ ((s : E) * h k i) := by
  obtain ⟨-, s, hs, hc, y, hy, he⟩ := hh
  refine ⟨s, hs, hc, fun k i => ?_⟩
  have e := congrFun (congrFun he k) i
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul] at e
  have : (s : E) * h k i = M * y k i + s * (1 : Matrix (Fin n) (Fin n) E) k i := by
    linear_combination e
  rw [this]
  refine ((isIntegral_natCast M).mul (hy k i)).add ((isIntegral_natCast s).mul ?_)
  rw [Matrix.one_apply]
  split_ifs <;> simp [isIntegral_one, isIntegral_zero]
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma smul_mulVec_mem_stdL_of_integral_scaled {g : Matrix (Fin n) (Fin n) E} {s : ℕ}
    (hg : ∀ k i, IsIntegral ℤ ((s : E) * g k i)) {v : Fin n → E}
    (hv : v ∈ _root_.GlobalTheory.SW.stdL E n) :
    (s : E) • (g *ᵥ v) ∈ _root_.GlobalTheory.SW.stdL E n := by
  rw [_root_.GlobalTheory.SW.Base.mem_stdL] at hv ⊢
  intro k
  have : ((s : E) • (g *ᵥ v)) k = ∑ i, (s : E) * g k i * v i := by
    simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  rw [this]
  exact IsIntegral.sum _ fun i _ => (hg k i).mul (hv i)
open Matrix Complex NumberField Filter Topology in
open scoped ComplexConjugate ComplexOrder Real in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} in
private lemma exists_moves_mem_Vset_of_mem_DH {M : ℕ} {h : Matrix (Fin n) (Fin n) E}
    (hh : h ∈ _root_.GlobalTheory.SW.DH E n M) {Λ : _root_.GlobalTheory.SW.Lt E n}
    (hΛ : Λ ∈ _root_.GlobalTheory.SW.Vset E n M) :
    ∃ Λ' ∈ _root_.GlobalTheory.SW.Vset E n M, _root_.GlobalTheory.SW.Moves h Λ Λ' := by
  have hu : _root_.GlobalTheory.SW.ccT h * h = 1 := hh.1
  have hu' := mul_eq_one_comm.1 hu
  have hinv : ∀ v, h *ᵥ (_root_.GlobalTheory.SW.ccT h *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hu', Matrix.one_mulVec]
  have hinv' : ∀ v, _root_.GlobalTheory.SW.ccT h *ᵥ (h *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  obtain ⟨hfg, hsd, s₁, hs₁, hc₁, hstd₁, hΛs₁⟩ := hΛ
  let Λ' : _root_.GlobalTheory.SW.Lt E n := Λ.map ((Matrix.mulVecLin h).restrictScalars (𝓞 E))
  have hmem : ∀ x, x ∈ Λ' ↔ _root_.GlobalTheory.SW.ccT h *ᵥ x ∈ Λ := fun x => by
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [hinv'] using hw
    · intro hx
      exact ⟨_, hx, hinv x⟩
  have hmov : _root_.GlobalTheory.SW.Moves h Λ Λ' := fun v => by rw [hmem, hinv']
  refine ⟨Λ', ⟨hfg.map _, fun x => ?_, ?_⟩, hmov⟩
  · rw [hmem x, hsd]
    constructor
    · intro H y hy
      have := H _ ((hmem y).1 hy)
      rwa [← herm_one_mulVec_of_unitary hu, hinv, hinv] at this
    · intro H y hy
      have := H _ ((hmov y).1 hy)
      rwa [← hinv x, herm_one_mulVec_of_unitary hu] at this
  · obtain ⟨s₂, hs₂, hc₂, hg₂⟩ := exists_coprime_scale_integral_entries_of_mem_DH hh
    obtain ⟨s₃, hs₃, hc₃, hg₃⟩ :=
      exists_coprime_scale_integral_entries_of_mem_DH (_root_.GlobalTheory.SW.Base.ccT_mem_DH hh)
    refine ⟨s₁ * s₂ * s₃, by positivity, (hc₁.mul hc₂).mul hc₃, fun v hv => ?_, fun v hv => ?_⟩
    · have h1 := smul_mulVec_mem_stdL_of_integral_scaled hg₂ (hstd₁ _ ((hmem v).1 hv))
      have h2 := _root_.GlobalTheory.SW.Base.nat_smul_mem _ s₃ h1
      rw [Matrix.mulVec_smul, hinv, smul_smul, smul_smul] at h2
      convert h2 using 2
      push_cast
      ring
    · have h1 := hΛs₁ _ (smul_mulVec_mem_stdL_of_integral_scaled hg₃ hv)
      have h2 := (hmov _).1 h1
      rw [Matrix.mulVec_smul, Matrix.mulVec_smul, hinv, smul_smul] at h2
      have h3 := _root_.GlobalTheory.SW.Base.nat_smul_mem _ s₂ h2
      rw [smul_smul] at h3
      convert h3 using 2
      push_cast
      ring
end GlobalTheory.SW
end

set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW
open Matrix Complex NumberField Filter Topology
open scoped ComplexConjugate ComplexOrder Real
namespace GlobalTheory.SW
namespace _root_.GlobalTheory.SW
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (n M : ℕ), 0 < M → Finite (_root_.GlobalTheory.SW.Cls E n M) ∧
    _root_.GlobalTheory.SW.stdL E n ∈ _root_.GlobalTheory.SW.Vset E n M ∧
    (∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      {h ∈ _root_.GlobalTheory.SW.DH E n M | _root_.GlobalTheory.SW.Moves h Λ Λ}.Finite ∧
        0 < _root_.GlobalTheory.SW.wt M Λ) ∧
    (1 ∈ _root_.GlobalTheory.SW.DH E n M ∧
      ∀ h ∈ _root_.GlobalTheory.SW.DH E n M,
        _root_.GlobalTheory.SW.ccT h ∈ _root_.GlobalTheory.SW.DH E n M ∧
          ∀ h' ∈ _root_.GlobalTheory.SW.DH E n M,
            h * h' ∈ _root_.GlobalTheory.SW.DH E n M) ∧
    ∀ h ∈ _root_.GlobalTheory.SW.DH E n M, ∀ Λ ∈ _root_.GlobalTheory.SW.Vset E n M,
      ∃ Λ' ∈ _root_.GlobalTheory.SW.Vset E n M, _root_.GlobalTheory.SW.Moves h Λ Λ' := by
  intro E _ _ _ n M hM
  refine ⟨finite_cls' M hM, _root_.GlobalTheory.SW.Base.stdL_mem_Vset n M,
    fun Λ hΛ => ⟨finite_stabiliser_DH M hΛ, ?_⟩,
    ⟨_root_.GlobalTheory.SW.Base.one_mem_DH M, fun h hh =>
      ⟨_root_.GlobalTheory.SW.Base.ccT_mem_DH hh,
        fun h' hh' => _root_.GlobalTheory.SW.Base.mul_mem_DH hh hh'⟩⟩,
    fun h hh Λ hΛ => exists_moves_mem_Vset_of_mem_DH hh hΛ⟩
  have hne : {h | h ∈ _root_.GlobalTheory.SW.DH E n M ∧
      _root_.GlobalTheory.SW.Moves h Λ Λ}.Nonempty :=
    ⟨1, _root_.GlobalTheory.SW.Base.one_mem_DH M, _root_.GlobalTheory.SW.Base.moves_one Λ⟩
  unfold _root_.GlobalTheory.SW.wt
  exact inv_pos.2 (Nat.cast_pos.2 ((Set.ncard_pos (finite_stabiliser_DH M hΛ)).2 hne))
end _root_.GlobalTheory.SW
end GlobalTheory.SW
