-- Prove2me | solution 1 for KAdaptability.PolicyCount.ec2_rank
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T02:25:58.013039+00:00
-- url     : https://prove2.me/submissions/cf79a5bf-e572-4ff2-8c14-938e484e2b21

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_Mixed

set_option autoImplicit false
open Matrix KAdaptability.PolicyCount

variable {N M L nQ R : ℕ}

theorem dot_lin' {E : Type} [AddCommGroup E] [Module ℝ E] {ι : Type} [Fintype ι]
    (Lm : E →ₗ[ℝ] (Fin nQ → ℝ)) (ξ : Fin nQ → ℝ) (w : ι → ℝ) (v : ι → E) :
    ξ ⬝ᵥ Lm (∑ i, w i • v i) = ∑ i, w i * (ξ ⬝ᵥ Lm (v i)) := by
  rw [map_sum]
  simp only [map_smul, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem sum_extend' {ι : Type} [Fintype ι] {K' : ℕ} (e : ι ↪ Fin K') (g : ι → ℝ) (F : Fin K' → ℝ)
    (hF : ∀ j, (¬∃ i, e i = j) → F j = 0) (hFe : ∀ i, F (e i) = g i) :
    ∑ j, F j = ∑ i, g i := by
  classical
  have h := Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) (f := F) (by
    intro j _ hj
    apply hF
    rintro ⟨i, hi⟩
    exact hj (Finset.mem_map.2 ⟨i, Finset.mem_univ _, hi⟩))
  rw [← h, Finset.sum_map]
  exact Finset.sum_congr rfl (fun i _ => hFe i)

open Classical in
theorem reduce' {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : Problem N M L nQ R)
    (ψ : (Fin M → ℝ) →ₗ[ℝ] E) (Lm : E →ₗ[ℝ] (Fin nQ → ℝ))
    (hL : ∀ y, P.Q *ᵥ y = Lm (ψ y)) (B : ℕ)
    (hB : Module.finrank ℝ (vectorSpan ℝ (ψ '' (P.Y : Set (Fin M → ℝ)))) ≤ B)
    (K K' : ℕ) (hK' : min (B + 1) P.Y.card ≤ K') (x : Fin N → ℝ) (ys : Fin K → Fin M → ℝ)
    (lam : Fin K → ℝ) (hf : P.FeasibleK K x ys) (hl : lam ∈ stdSimplex ℝ (Fin K)) :
    ∃ (ys' : Fin K' → Fin M → ℝ) (lam' : Fin K' → ℝ), P.FeasibleK K' x ys' ∧
      lam' ∈ stdSimplex ℝ (Fin K') ∧
      ∀ ξ : Fin nQ → ℝ, ∑ k, lam' k * (ξ ⬝ᵥ (P.Q *ᵥ ys' k)) = ∑ k, lam k * (ξ ⬝ᵥ (P.Q *ᵥ ys k)) := by
  set z : E := ∑ k, lam k • ψ (ys k) with hz
  have hzmem : z ∈ convexHull ℝ (ψ '' Set.range ys) := by
    apply (convex_convexHull ℝ _).sum_mem (fun k _ => hl.1 k) hl.2
    intro k _
    exact subset_convexHull ℝ _ ⟨ys k, ⟨k, rfl⟩, rfl⟩
  obtain ⟨ι, _, v, w, hv, hAI, hwpos, hw1, hwz⟩ := eq_pos_convex_span_of_mem_convexHull hzmem
  have hkk : ∀ i, ∃ k, ψ (ys k) = v i := by
    intro i
    obtain ⟨y, ⟨k, rfl⟩, hy⟩ := hv ⟨i, rfl⟩
    exact ⟨k, hy⟩
  choose kk hkk using hkk
  have hcard1 : Fintype.card ι ≤ B + 1 :=
    hAI.card_le_finrank_succ.trans (Nat.succ_le_succ ((Submodule.finrank_mono (vectorSpan_mono ℝ
      (by rintro _ ⟨i, rfl⟩; obtain ⟨y, ⟨k, rfl⟩, hy⟩ := hv ⟨i, rfl⟩;
          exact ⟨ys k, hf.2 k |>.1, hy⟩))).trans hB))
  have hcard2 : Fintype.card ι ≤ P.Y.card := by
    have hinj : Function.Injective (fun i => (⟨ys (kk i), (hf.2 (kk i)).1⟩ : P.Y)) := by
      intro i j hij
      have : ys (kk i) = ys (kk j) := congrArg Subtype.val hij
      apply hAI.injective
      rw [← hkk i, ← hkk j, this]
    simpa using Fintype.card_le_of_injective _ hinj
  have hcard : Fintype.card ι ≤ K' := le_trans (le_min hcard1 hcard2) hK'
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le (α := ι) (β := Fin K') (by simpa using hcard)
  have hne : Nonempty ι := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hw1
  obtain ⟨i0⟩ := hne
  refine ⟨Function.extend e (fun i => ys (kk i)) (fun _ => ys (kk i0)),
    Function.extend e w 0, ?_, ?_, ?_⟩
  · refine ⟨hf.1, fun j => ?_⟩
    by_cases hj : ∃ i, e i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [e.injective.extend_apply]
      exact hf.2 _
    · rw [Function.extend_apply' _ _ _ hj]
      exact hf.2 _
  · refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply]; exact (hwpos i).le
      · rw [Function.extend_apply' _ _ _ hj]; exact le_rfl
    · rw [sum_extend' e w _ (fun j hj => by rw [Function.extend_apply' _ _ _ hj]; rfl)
        (fun i => by rw [e.injective.extend_apply])]
      exact hw1
  · intro ξ
    have hext : ∀ j, (¬∃ i, e i = j) → Function.extend e w 0 j *
        (ξ ⬝ᵥ (P.Q *ᵥ Function.extend e (fun i => ys (kk i)) (fun _ => ys (kk i0)) j)) = 0 := by
      intro j hj
      rw [Function.extend_apply' _ _ _ hj]; simp
    rw [sum_extend' e (fun i => w i * (ξ ⬝ᵥ Lm (v i))) _ hext (fun i => by
      rw [e.injective.extend_apply, e.injective.extend_apply, hL, hkk])]
    rw [← dot_lin' Lm ξ w v, hwz, hz]
    rw [dot_lin' Lm ξ lam (fun k => ψ (ys k))]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hL]

theorem optMixed_le' {E : Type} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (P : Problem N M L nQ R)
    (ψ : (Fin M → ℝ) →ₗ[ℝ] E) (Lm : E →ₗ[ℝ] (Fin nQ → ℝ))
    (hL : ∀ y, P.Q *ᵥ y = Lm (ψ y)) (B : ℕ)
    (hB : Module.finrank ℝ (vectorSpan ℝ (ψ '' (P.Y : Set (Fin M → ℝ)))) ≤ B)
    (K K' : ℕ) (hK' : min (B + 1) P.Y.card ≤ K') : P.optMixed K' ≤ P.optMixed K := by
  unfold Problem.optMixed
  refine le_iInf fun x => le_iInf fun ys => le_iInf fun hf => le_iInf fun lam =>
    le_iInf fun hl => ?_
  obtain ⟨ys', lam', hf', hl', heq⟩ := reduce' P ψ Lm hL B hB K K' hK' x ys lam hf hl
  refine le_trans ((iInf_le _ x).trans ((iInf_le _ ys').trans ((iInf_le _ hf').trans
    ((iInf_le _ lam').trans (iInf_le _ hl'))))) ?_
  unfold Problem.objMixed
  refine le_of_eq (iSup_congr fun ξ => iSup_congr fun hξ => ?_)
  rw [heq ξ]

theorem optMixed_dim_le' (P : Problem N M L nQ R) (K K' : ℕ)
    (hK' : min (P.dimY + 1) P.Y.card ≤ K') : P.optMixed K' ≤ P.optMixed K := by
  refine optMixed_le' P (LinearMap.id) (Matrix.mulVecLin P.Q) (fun y => rfl) P.dimY ?_ K K' hK'
  rw [LinearMap.id_coe, Set.image_id]
  exact le_rfl

theorem optMixed_rank_le' (P : Problem N M L nQ R) (K K' : ℕ)
    (hK' : min (P.Q.rank + 1) P.Y.card ≤ K') : P.optMixed K' ≤ P.optMixed K := by
  refine optMixed_le' P (Matrix.mulVecLin P.Q) (LinearMap.id) (fun y => rfl) P.Q.rank ?_ K K' hK'
  unfold Matrix.rank
  refine Submodule.finrank_mono ?_
  rw [vectorSpan_def]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨a, ⟨y, hy, rfl⟩, b, ⟨y', hy', rfl⟩, rfl⟩
  exact ⟨y - y', by simp [Matrix.mulVec_sub]⟩

theorem solution (P : Problem N M L nQ R) :
    P.optMixed P.Y.card = P.optMixed (P.Q.rank + 1) :=
  le_antisymm (optMixed_rank_le' P _ _ (min_le_right _ _)) (optMixed_rank_le' P _ _ (min_le_left _ _))
