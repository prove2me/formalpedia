-- Prove2me | solution 1 for GlobalTheory.FitSquare.fitting_exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:07:59.622799+00:00
-- url     : https://prove2.me/submissions/ba2ecf86-8966-4d70-b75f-90a0c69ea2df

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DetMemSpanAdjugate
import Theorems.Thm_GlobalTheory_FitSquare_relations_mem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Matrix
namespace GlobalTheory.FitSquare
variable {R : Type} [CommRing R]
section blocks
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_updateRow_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α]
    (Φ : Matrix α α R) (k : α) (w : α → R) :
    (Φ.updateRow k w).det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  rw [← det_transpose, ← updateCol_transpose, ← cramer_apply, cramer_eq_adjugate_mulVec,
    ← adjugate_transpose]
  simp only [mulVec, dotProduct, transpose_apply]
  exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(l, k), rfl⟩)
open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_mem_span_adjugate_entries {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (Φ : Matrix α α R) :
    Φ.det ∈ Ideal.span (Set.range fun p : α × α => Φ.adjugate p.1 p.2) := by
  obtain ⟨i⟩ := ‹Nonempty α›
  have h := det_updateRow_mem_span_adjugate_entries Φ i (Φ i)
  rwa [updateRow_eq_self] at h
open Matrix in
variable {R : Type} [CommRing R] in
variable {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] in
private theorem det_eq_mul_of_toBlocks₂₁_eq_zero {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (M : Matrix (α ⊕ β) (α ⊕ β) R) (h : M.toBlocks₂₁ = 0) :
    M.det = M.toBlocks₁₁.det * M.toBlocks₂₂.det := by
  conv_lhs => rw [← fromBlocks_toBlocks M, h]
  exact det_fromBlocks_zero₂₁ _ _ _
end blocks
end GlobalTheory.FitSquare
end

set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.FitSquare
variable {R : Type} [CommRing R]
open Matrix
variable {R : Type} [CommRing R]
namespace GlobalTheory.FitSquare
namespace _root_.GlobalTheory.FitSquare
theorem _root_.solution : ∀ (R : Type) [CommRing R] (M₁ M₂ M₃ : Type) [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃] (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃), Function.Exact f g → Function.Surjective g → ∀ (k : ℕ) (x : R) (v : Fin k → M₁), Submodule.span R (Set.range v) = ⊤ → (∀ m : M₁, x • m = 0) → ∀ (a b : ℕ) (Φ : Matrix (Fin a) (Fin a) R) (Ψ : Matrix (Fin b) (Fin b) R), Nonempty (M₂ ≃ₗ[R] ((Fin a → R) ⧸ LinearMap.range Φ.mulVecLin)) → Nonempty (M₃ ≃ₗ[R] ((Fin b → R) ⧸ LinearMap.range Ψ.mulVecLin)) → x ^ k * Ψ.det ∈ Ideal.span {Φ.det} ∧ (a = 0 ∨ ((∀ p q, x ^ k * Ψ.adjugate p q ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)) ∧ (b = 0 → x ^ k ∈ Ideal.span (Set.range fun p : Fin a × Fin a => Φ.adjugate p.1 p.2)))) := by
  intro R _ M₁ M₂ M₃ _ _ _ _ _ _ f g hfg hg k x v hv hx a b Φ Ψ ⟨e₂⟩ ⟨e₃⟩
  let π : (Fin a → R) →ₗ[R] M₂ := e₂.symm.toLinearMap ∘ₗ (LinearMap.range Φ.mulVecLin).mkQ
  have hπ : Function.Surjective π := e₂.symm.surjective.comp (Submodule.mkQ_surjective _)
  have hΦ : ∀ y, π y = 0 → ∃ z, Φ *ᵥ z = y := by
    intro y hy
    have hy' : (LinearMap.range Φ.mulVecLin).mkQ y = 0 := by
      simpa [π] using hy
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hy'
    obtain ⟨z, hz⟩ := hy'
    exact ⟨z, hz⟩
  let ρ : (Fin b → R) →ₗ[R] M₃ := e₃.symm.toLinearMap ∘ₗ (LinearMap.range Ψ.mulVecLin).mkQ
  have hρ : Function.Surjective ρ := e₃.symm.surjective.comp (Submodule.mkQ_surjective _)
  choose u hu using fun j : Fin b => hg (ρ (Pi.single j 1))
  let H : (Fin b → R) →ₗ[R] M₂ := Fintype.linearCombination R u
  have hgH : ∀ t, g (H t) = ρ t := by
    have h : g ∘ₗ H = ρ := by
      ext j
      simp [H, hu]
    exact fun t => LinearMap.congr_fun h t
  have hkerg : ∀ y, g y = 0 → ∃ c : Fin k → R, ∑ i, c i • f (v i) = y := by
    intro y hy
    obtain ⟨m₁, rfl⟩ := (hfg y).1 hy
    have hm : m₁ ∈ Submodule.span R (Set.range v) := hv ▸ Submodule.mem_top
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hm
    exact ⟨c, by simp [map_sum]⟩
  let q : (Fin k ⊕ Fin b → R) →ₗ[R] M₂ :=
    Fintype.linearCombination R (Sum.elim (fun i => f (v i)) u)
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨t, ht⟩ := hρ (g y)
    obtain ⟨c, hc⟩ := hkerg (y - H t) (by rw [map_sub, hgH, ht, sub_self])
    refine ⟨Sum.elim c t, ?_⟩
    rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr]
    rw [hc]
    simp [H, Fintype.linearCombination_apply]
  have hcolΨ : ∀ j, ∃ c : Fin k → R, ∑ i, c i • f (v i) = H (fun r => Ψ r j) := by
    intro j
    apply hkerg
    rw [hgH]
    simp only [ρ, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      Submodule.mkQ_apply]
    rw [(Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range.2 ⟨Pi.single j 1, by
      rw [mulVecLin_apply, mulVec_single_one]; rfl⟩), map_zero]
  choose C hC using hcolΨ
  let T : Matrix (Fin k ⊕ Fin b) (Fin k ⊕ Fin b) R :=
    fromBlocks (x • 1) (-Matrix.of fun i j => C j i) 0 Ψ
  have hT : ∀ y, q (T *ᵥ y) = 0 := by
    have h0 : q ∘ₗ T.mulVecLin = 0 := by
      ext c
      simp only [LinearMap.coe_comp, Function.comp_apply, mulVecLin_apply,
        LinearMap.single_apply, mulVec_single_one, LinearMap.zero_apply]
      rw [Fintype.linearCombination_apply, Fintype.sum_sum_type]
      rcases c with i | j
      · simp [T, col, one_apply]
        rw [← map_smul, hx, map_zero]
      · have hCj := hC j
        simp only [H, Fintype.linearCombination_apply] at hCj
        simp [T, col, neg_smul, Finset.sum_neg_distrib, hCj]
    exact fun y => LinearMap.congr_fun h0 y
  obtain ⟨h₁, h₂⟩ := _root_.GlobalTheory.FitSquare.relations_mem π hπ Φ hΦ q hq T hT
  have hdetT : T.det = x ^ k * Ψ.det := by simp [T, det_fromBlocks_zero₂₁, det_smul]
  rw [hdetT] at h₁
  refine ⟨h₁, ?_⟩
  rcases Nat.eq_zero_or_pos a with ha | ha
  · exact Or.inl ha
  · right
    haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
    refine ⟨fun p p' => ?_, fun hb0 => ?_⟩
    · have hadj : T.adjugate (Sum.inr p) (Sum.inr p') = x ^ k * Ψ.adjugate p p' := by
        rw [adjugate_apply, adjugate_apply, det_eq_mul_of_toBlocks₂₁_eq_zero]
        · have h₁₁ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₁₁ =
              x • 1 := by
            ext s t
            simp [T, toBlocks₁₁, updateRow_apply]
          have h₂₂ : (T.updateRow (Sum.inr p') (Pi.single (Sum.inr p) 1)).toBlocks₂₂ =
              Ψ.updateRow p' (Pi.single p 1) := by
            ext s t
            by_cases hs : s = p' <;> simp [T, toBlocks₂₂, updateRow_apply, hs, Pi.single_apply]
          rw [h₁₁, h₂₂, det_smul, det_one, mul_one, Fintype.card_fin]
        · ext s t
          simp [T, toBlocks₂₁, updateRow_apply]
      rw [← hadj]
      exact h₂ ‹_› _ _
    · subst hb0
      have h₃ : x ^ k ∈ Ideal.span {Φ.det} := by simpa [det_isEmpty] using h₁
      exact (Ideal.span_singleton_le_iff_mem _).2 (det_mem_span_adjugate_entries Φ) h₃
end _root_.GlobalTheory.FitSquare
end GlobalTheory.FitSquare
