-- Prove2me | solution 1 for KAdaptability.PolicyCount.mixed_eq_adaptability
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:33:15.5657+00:00
-- url     : https://prove2.me/submissions/4f820f12-5c91-4183-8662-5b30d49a12a7

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Mixed

set_option autoImplicit false
open Matrix KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

theorem Xi_compact' (P : Problem N M L nQ R) : IsCompact P.Xi := by
  have hc : IsClosed P.Xi := by
    have h : IsClosed {ξ : Fin nQ → ℝ | P.A *ᵥ ξ ≤ P.b} :=
      isClosed_le (continuous_const.matrix_mulVec continuous_id) continuous_const
    exact h
  exact Metric.isCompact_of_isClosed_isBounded hc P.Xi_bounded

theorem Xi_convex' (P : Problem N M L nQ R) : Convex ℝ P.Xi := by
  intro ξ hξ η hη a b ha hb hab
  show P.A *ᵥ (a • ξ + b • η) ≤ P.b
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  intro i
  have h1 : (P.A *ᵥ ξ) i ≤ P.b i := hξ i
  have h2 : (P.A *ᵥ η) i ≤ P.b i := hη i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have := mul_le_mul_of_nonneg_left h1 ha
  have := mul_le_mul_of_nonneg_left h2 hb
  have h3 : a * P.b i + b * P.b i = P.b i := by rw [← add_mul, hab, one_mul]
  linarith

theorem inf_attained' {K : ℕ} (hK : 0 < K) (a : Fin K → ℝ) :
    ∃ k0, (⨅ k, ((a k : ℝ) : EReal)) = ((a k0 : ℝ) : EReal) ∧ ∀ k, a k0 ≤ a k := by
  have : Nonempty (Fin K) := ⟨⟨0, hK⟩⟩
  obtain ⟨k0, hk0⟩ := Finite.exists_min a
  refine ⟨k0, le_antisymm (iInf_le _ k0) (le_iInf fun k => ?_), hk0⟩
  exact_mod_cast hk0 k

theorem ec1' (P : Problem N M L nQ R) (K : ℕ) (x : Fin N → ℝ)
    (ys : Fin K → Fin M → ℝ) :
    P.objPOK K x ys = ⨅ (lam : Fin K → ℝ) (_ : lam ∈ stdSimplex ℝ (Fin K)),
      P.objMixed K x ys lam := by
  obtain ⟨ξ0, hξ0⟩ := P.Xi_nonempty
  rcases Nat.eq_zero_or_pos K with hK | hK
  · subst hK
    have hsimp : ∀ lam : Fin 0 → ℝ, lam ∉ stdSimplex ℝ (Fin 0) := by
      intro lam hl
      have := hl.2
      simp at this
    have hR : (⨅ (lam : Fin 0 → ℝ) (_ : lam ∈ stdSimplex ℝ (Fin 0)), P.objMixed 0 x ys lam) = ⊤ := by
      simp only [iInf_eq_top]
      intro lam hl
      exact absurd hl (hsimp lam)
    rw [hR]
    unfold Problem.objPOK
    refine top_unique ?_
    refine le_iSup₂_of_le ξ0 hξ0 ?_
    rw [iInf_of_empty]
    exact (EReal.coe_add_top _).ge
  · set f : (Fin K → ℝ) → (Fin nQ → ℝ) → ℝ := fun lam ξ =>
      ξ ⬝ᵥ (P.C *ᵥ x) + ∑ k, lam k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) with hf
    have hΔne : (stdSimplex ℝ (Fin K)).Nonempty :=
      ⟨Pi.single ⟨0, hK⟩ 1, single_mem_stdSimplex ℝ _⟩
    have hfcont_l : ∀ ξ, Continuous (fun lam : Fin K → ℝ => f lam ξ) := by
      intro ξ; simp only [hf]; fun_prop
    have hfcont_x : ∀ lam, Continuous (fun ξ : Fin nQ → ℝ => f lam ξ) := by
      intro lam; simp only [hf]; fun_prop
    have hfconv_l : ∀ ξ, ConvexOn ℝ (stdSimplex ℝ (Fin K)) (fun lam : Fin K → ℝ => f lam ξ) := by
      intro ξ
      refine ⟨convex_stdSimplex ℝ _, ?_⟩
      intro l1 _ l2 _ a b ha hb hab
      simp only [hf, smul_eq_mul, Pi.add_apply, Pi.smul_apply]
      have h0 : ξ ⬝ᵥ (P.C *ᵥ x) = a * (ξ ⬝ᵥ (P.C *ᵥ x)) + b * (ξ ⬝ᵥ (P.C *ᵥ x)) := by
        rw [← add_mul, hab, one_mul]
      have h1 : ∑ k, (a * l1 k + b * l2 k) * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) =
          a * ∑ k, l1 k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) + b * ∑ k, l2 k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [h1]
      linarith
    have hfconc_x : ∀ lam, ConcaveOn ℝ P.Xi (fun ξ : Fin nQ → ℝ => f lam ξ) := by
      intro lam
      refine ⟨Xi_convex' P, ?_⟩
      intro ξ1 _ ξ2 _ a b ha hb hab
      simp only [hf, smul_eq_mul]
      have e1 : (a • ξ1 + b • ξ2) ⬝ᵥ (P.C *ᵥ x) =
          a * (ξ1 ⬝ᵥ (P.C *ᵥ x)) + b * (ξ2 ⬝ᵥ (P.C *ᵥ x)) := by
        rw [add_dotProduct, smul_dotProduct, smul_dotProduct]; simp
      have e2 : ∀ k, (a • ξ1 + b • ξ2) ⬝ᵥ (P.Q *ᵥ ys k) =
          a * (ξ1 ⬝ᵥ (P.Q *ᵥ ys k)) + b * (ξ2 ⬝ᵥ (P.Q *ᵥ ys k)) := by
        intro k
        rw [add_dotProduct, smul_dotProduct, smul_dotProduct]; simp
      simp only [e1, e2]
      have h1 : ∑ k, lam k * (a * (ξ1 ⬝ᵥ (P.Q *ᵥ ys k)) + b * (ξ2 ⬝ᵥ (P.Q *ᵥ ys k))) =
          a * ∑ k, lam k * (ξ1 ⬝ᵥ (P.Q *ᵥ ys k)) + b * ∑ k, lam k * (ξ2 ⬝ᵥ (P.Q *ᵥ ys k)) := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl (fun k _ => by ring)
      rw [h1]
      have h0 : (a + b) * (ξ1 ⬝ᵥ (P.C *ᵥ x)) = a * (ξ1 ⬝ᵥ (P.C *ᵥ x)) + b * (ξ1 ⬝ᵥ (P.C *ᵥ x)) := by ring
      nlinarith
    obtain ⟨a0, ha0, b0, hb0, hsad⟩ := Sion.exists_isSaddlePointOn hΔne (convex_stdSimplex ℝ _)
      (isCompact_stdSimplex ℝ (Fin K))
      (fun ξ _ => (hfcont_l ξ).lowerSemicontinuous.lowerSemicontinuousOn _)
      (fun ξ _ => (hfconv_l ξ).quasiconvexOn)
      (Xi_convex' P) ⟨ξ0, hξ0⟩ (Xi_compact' P)
      (fun lam _ => (hfcont_x lam).upperSemicontinuous.upperSemicontinuousOn _)
      (fun lam _ => (hfconc_x lam).quasiconcaveOn)
    unfold Problem.objPOK Problem.objMixed
    have hval : ∀ ξ : Fin nQ → ℝ, ∃ k0 : Fin K,
        ((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + ⨅ k, ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal)
          = ((f (Pi.single k0 1) ξ : ℝ) : EReal) ∧
        ∀ lam ∈ stdSimplex ℝ (Fin K), f (Pi.single k0 1) ξ ≤ f lam ξ := by
      intro ξ
      obtain ⟨k0, h1, h2⟩ := inf_attained' hK (fun k => ξ ⬝ᵥ (P.Q *ᵥ ys k))
      have hs : f (Pi.single k0 1) ξ = ξ ⬝ᵥ (P.C *ᵥ x) + ξ ⬝ᵥ (P.Q *ᵥ ys k0) := by
        simp [hf, Pi.single_apply]
      refine ⟨k0, ?_, ?_⟩
      · rw [h1, ← EReal.coe_add, hs]
      · intro lam hl
        rw [hs]
        simp only [hf]
        have : ξ ⬝ᵥ (P.Q *ᵥ ys k0) ≤ ∑ k, lam k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) := by
          calc ξ ⬝ᵥ (P.Q *ᵥ ys k0) = ∑ k, lam k * (ξ ⬝ᵥ (P.Q *ᵥ ys k0)) := by
                rw [← Finset.sum_mul, hl.2, one_mul]
            _ ≤ ∑ k, lam k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) :=
                Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_left (h2 k) (hl.1 k))
        linarith
    apply le_antisymm
    · refine le_iInf fun lam => le_iInf fun hl => iSup₂_le fun ξ hξ => ?_
      obtain ⟨k0, he, hle⟩ := hval ξ
      rw [he]
      exact le_iSup₂_of_le ξ hξ (by exact_mod_cast hle lam hl)
    · obtain ⟨ks, hes, hles⟩ := hval b0
      refine le_trans (iInf₂_le a0 ha0) ?_
      refine iSup₂_le fun ξ hξ => ?_
      have h1 : f a0 ξ ≤ f (Pi.single ks 1) b0 := hsad _ (single_mem_stdSimplex ℝ ks) ξ hξ
      refine le_trans ?_ (le_iSup₂_of_le b0 hb0 le_rfl)
      rw [hes]
      exact_mod_cast h1

theorem solution (P : Problem N M L nQ R) (K : ℕ) :
    P.optMixed K = P.optPOK K := by
  unfold Problem.optMixed Problem.optPOK
  refine iInf_congr fun x => iInf_congr fun ys => iInf_congr fun hf => ?_
  exact (ec1' P K x ys).symm
