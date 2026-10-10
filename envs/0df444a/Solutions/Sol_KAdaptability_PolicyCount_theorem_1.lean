-- Prove2me | solution 1 for KAdaptability.PolicyCount.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T18:15:40.051006+00:00
-- url     : https://prove2.me/submissions/b40decba-4638-4ef0-9da4-e1daa19ec7ee

import Mathlib
import Definitions.Def_KAdaptability_PolicyCount_PO
import Definitions.Def_KAdaptability_PolicyCount_POK

open Matrix

namespace RRAux_KAdaptability_PolicyCount_theorem_1

-- the affine dimension of Q·Ys is at most min(dim Y, rk Q)
theorem finrank_image_le {M nQ : ℕ} (Q : Matrix (Fin nQ) (Fin M) ℝ) (Ys Y : Set (Fin M → ℝ))
    (hsub : Ys ⊆ Y) :
    Module.finrank ℝ (vectorSpan ℝ ((fun y => Q *ᵥ y) '' Ys)) ≤
      min (Module.finrank ℝ (vectorSpan ℝ Y)) Q.rank := by
  have himg : (fun y => Q *ᵥ y) '' Ys = Q.mulVecLin.toAffineMap '' Ys := by
    ext v; simp
  rw [himg, ← AffineMap.map_vectorSpan, LinearMap.toAffineMap_linear]
  refine le_min ?_ ?_
  · exact (Submodule.finrank_map_le _ _).trans (Submodule.finrank_mono (vectorSpan_mono ℝ hsub))
  · exact Submodule.finrank_mono (LinearMap.map_le_range)

theorem Xi_convex {nQ R : ℕ} (A : Matrix (Fin R) (Fin nQ) ℝ) (b : Fin R → ℝ) :
    Convex ℝ {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b} := by
  intro ξ1 h1 ξ2 h2 s t hs ht hst
  show A *ᵥ (s • ξ1 + t • ξ2) ≤ b
  rw [mulVec_add, mulVec_smul, mulVec_smul]
  intro r
  have e1 := mul_le_mul_of_nonneg_left (h1 r) hs
  have e2 := mul_le_mul_of_nonneg_left (h2 r) ht
  have e3 : s * b r + t * b r = b r := by rw [← add_mul, hst, one_mul]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

theorem Xi_compact {nQ R : ℕ} (A : Matrix (Fin R) (Fin nQ) ℝ) (b : Fin R → ℝ)
    (hb : Bornology.IsBounded {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b}) :
    IsCompact {ξ : Fin nQ → ℝ | A *ᵥ ξ ≤ b} := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ hb
  have hc : Continuous fun ξ : Fin nQ → ℝ => A *ᵥ ξ := by
    exact LinearMap.continuous_of_finiteDimensional A.mulVecLin
  exact isClosed_le hc continuous_const

-- minimax + Carathéodory, in pure vector form
theorem main {M nQ K : ℕ} (Q : Matrix (Fin nQ) (Fin M) ℝ) (c : Fin nQ → ℝ)
    (Yx : Finset (Fin M → ℝ)) (hYx : Yx.Nonempty) (Ξ : Set (Fin nQ → ℝ)) (ne_Ξ : Ξ.Nonempty)
    (cΞ : Convex ℝ Ξ) (kΞ : IsCompact Ξ)
    (hK : Module.finrank ℝ (vectorSpan ℝ ((fun y => Q *ᵥ y) '' (Yx : Set (Fin M → ℝ)))) + 1 ≤ K) :
    ∃ ys : Fin K → Fin M → ℝ, (∀ k, ys k ∈ Yx) ∧ ∃ b ∈ Ξ, ∀ ξ ∈ Ξ, ∃ k, ∀ y ∈ Yx,
      ξ ⬝ᵥ c + ξ ⬝ᵥ (Q *ᵥ ys k) ≤ b ⬝ᵥ c + b ⬝ᵥ (Q *ᵥ y) := by
  classical
  let ι := ↥Yx
  let w : ι → Fin nQ → ℝ := fun i => c + Q *ᵥ i.1
  let f : (ι → ℝ) → (Fin nQ → ℝ) → ℝ := fun l ξ => ∑ i, l i * (ξ ⬝ᵥ w i)
  let Ll : (Fin nQ → ℝ) → (ι → ℝ) →ₗ[ℝ] ℝ := fun ξ =>
    { toFun := fun l => f l ξ
      map_add' := by intro l1 l2; simp [f, add_mul, Finset.sum_add_distrib]
      map_smul' := by intro r l; simp [f, Finset.mul_sum, mul_assoc] }
  let Lx : (ι → ℝ) → (Fin nQ → ℝ) →ₗ[ℝ] ℝ := fun l =>
    { toFun := fun ξ => f l ξ
      map_add' := by intro ξ1 ξ2; simp [f, add_dotProduct, mul_add, Finset.sum_add_distrib]
      map_smul' := by intro r ξ; simp [f, smul_dotProduct, Finset.mul_sum, mul_left_comm] }
  have hι : Nonempty ι := by obtain ⟨y, hy⟩ := hYx; exact ⟨⟨y, hy⟩⟩
  have ne_S : (stdSimplex ℝ ι).Nonempty := by
    obtain ⟨i⟩ := hι; exact ⟨_, single_mem_stdSimplex ℝ i⟩
  obtain ⟨a, ha, b, hb, hsad⟩ := Sion.exists_isSaddlePointOn (f := f)
    (ne_X := ne_S) (cX := convex_stdSimplex ℝ ι) (kX := isCompact_stdSimplex ℝ ι)
    (hfy := fun ξ _ => (LinearMap.continuous_of_finiteDimensional (Ll ξ)).lowerSemicontinuous
      |>.lowerSemicontinuousOn _)
    (hfy' := fun ξ _ => ((Ll ξ).convexOn (convex_stdSimplex ℝ ι)).quasiconvexOn)
    (cY := cΞ) (ne_Y := ne_Ξ) (kY := kΞ)
    (hfx := fun l _ => (LinearMap.continuous_of_finiteDimensional (Lx l)).upperSemicontinuous
      |>.upperSemicontinuousOn _)
    (hfx' := fun l _ => ((Lx l).concaveOn cΞ).quasiconcaveOn)
  -- value of f at a vertex of the simplex
  have hvert : ∀ i : ι, f (Pi.single i 1) b = b ⬝ᵥ c + b ⬝ᵥ (Q *ᵥ i.1) := by
    intro i
    simp only [f, w, dotProduct_add]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  -- the barycentre p
  let p : Fin nQ → ℝ := ∑ i, a i • (Q *ᵥ i.1)
  have hfa : ∀ ξ, f a ξ = ξ ⬝ᵥ c + ξ ⬝ᵥ p := by
    intro ξ
    simp only [f, w, p, dotProduct_add, mul_add, Finset.sum_add_distrib, dotProduct_sum,
      dotProduct_smul, smul_eq_mul]
    rw [← Finset.sum_mul, ha.2, one_mul]
  have hpS : p ∈ convexHull ℝ ((fun y => Q *ᵥ y) '' (Yx : Set (Fin M → ℝ))) :=
    (convex_convexHull ℝ _).sum_mem (fun i _ => ha.1 i) ha.2
      (fun i _ => subset_convexHull ℝ _ ⟨i.1, i.2, rfl⟩)
  obtain ⟨ι', hfin, z, wt, hzS, hai, hwpos, hwsum, hwp⟩ :=
    eq_pos_convex_span_of_mem_convexHull hpS
  have hcard : Fintype.card ι' ≤ Fintype.card (Fin K) := by
    rw [Fintype.card_fin]
    refine hai.card_le_finrank_succ.trans (le_trans ?_ hK)
    exact Nat.succ_le_succ (Submodule.finrank_mono (vectorSpan_mono ℝ hzS))
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hz : ∀ j, ∃ y ∈ Yx, Q *ᵥ y = z j := by
    intro j
    obtain ⟨y, hy, hyz⟩ := hzS ⟨j, rfl⟩
    exact ⟨y, hy, hyz⟩
  choose yj hyjY hyjz using hz
  have hne : Nonempty ι' := by
    by_contra h
    rw [not_nonempty_iff] at h
    simp at hwsum
  obtain ⟨j0⟩ := hne
  let ys : Fin K → Fin M → ℝ := fun k =>
    if h : ∃ j, e j = k then yj (Classical.choose h) else yj j0
  have hysY : ∀ k, ys k ∈ Yx := by
    intro k; simp only [ys]; split_ifs <;> exact hyjY _
  have hyse : ∀ j, ys (e j) = yj j := by
    intro j
    have h : ∃ j', e j' = e j := ⟨j, rfl⟩
    simp only [ys, dif_pos h]
    rw [e.injective (Classical.choose_spec h)]
  refine ⟨ys, hysY, b, hb, fun ξ hξ => ?_⟩
  obtain ⟨jm, -, hjm⟩ := Finset.exists_min_image Finset.univ (fun j => ξ ⬝ᵥ z j)
    ⟨j0, Finset.mem_univ _⟩
  refine ⟨e jm, fun y hy => ?_⟩
  have h1 : ξ ⬝ᵥ (Q *ᵥ ys (e jm)) ≤ ξ ⬝ᵥ p := by
    rw [hyse, hyjz, ← hwp, dotProduct_sum]
    calc ξ ⬝ᵥ z jm = ∑ j, wt j * (ξ ⬝ᵥ z jm) := by rw [← Finset.sum_mul, hwsum, one_mul]
      _ ≤ ∑ j, ξ ⬝ᵥ (wt j • z j) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [dotProduct_smul, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (hjm j (Finset.mem_univ _)) (hwpos j).le
  have h2 : f a ξ ≤ f (Pi.single ⟨y, hy⟩ 1) b := hsad _ (single_mem_stdSimplex ℝ _) ξ hξ
  rw [hfa, hvert] at h2
  linarith

end RRAux_KAdaptability_PolicyCount_theorem_1

variable {N M L nQ R : ℕ}

open KAdaptability.PolicyCount in
theorem solution (P : Problem N M L nQ R) (K : ℕ)
    (hK : min P.dimY P.Q.rank + 1 ≤ K) :
    P.optPOK K = P.optPO := by
  classical
  apply le_antisymm
  · unfold Problem.optPO
    refine le_iInf₂ fun x hx => ?_
    set Yx := P.Y.filter (fun y => P.T *ᵥ x + P.W *ᵥ y ≤ P.h) with hYxdef
    by_cases hYx : Yx.Nonempty
    · obtain ⟨ys, hys, b, hb, hmain⟩ := RRAux_KAdaptability_PolicyCount_theorem_1.main P.Q
        (P.C *ᵥ x) Yx hYx P.Xi P.Xi_nonempty
        (RRAux_KAdaptability_PolicyCount_theorem_1.Xi_convex P.A P.b)
        (RRAux_KAdaptability_PolicyCount_theorem_1.Xi_compact P.A P.b P.Xi_bounded)
        (le_trans (Nat.succ_le_succ (RRAux_KAdaptability_PolicyCount_theorem_1.finrank_image_le
          P.Q _ _ (by intro y hy; exact (Finset.mem_filter.1 hy).1))) hK)
      have hfeas : P.FeasibleK K x ys :=
        ⟨hx, fun k => Finset.mem_filter.1 (hys k)⟩
      have hle : P.optPOK K ≤ P.objPOK K x ys := by
        unfold Problem.optPOK
        exact iInf_le_of_le x (iInf_le_of_le ys (iInf_le_of_le hfeas le_rfl))
      refine hle.trans ?_
      unfold Problem.objPOK Problem.objPO
      refine iSup₂_le fun ξ hξ => ?_
      obtain ⟨k, hk⟩ := hmain ξ hξ
      refine le_trans ?_ (le_iSup₂_of_le b hb le_rfl)
      have hinf : (((ξ ⬝ᵥ (P.C *ᵥ x) + ξ ⬝ᵥ (P.Q *ᵥ ys k) - b ⬝ᵥ (P.C *ᵥ x) : ℝ)) : EReal) ≤
          ⨅ y ∈ P.Y, ⨅ (_ : P.T *ᵥ x + P.W *ᵥ y ≤ P.h), ((b ⬝ᵥ (P.Q *ᵥ y) : ℝ) : EReal) := by
        refine le_iInf₂ fun y hy => le_iInf fun hf => EReal.coe_le_coe_iff.2 ?_
        have := hk y (Finset.mem_filter.2 ⟨hy, hf⟩)
        linarith
      calc ((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + ⨅ k, ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal)
          ≤ ((ξ ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) + ((ξ ⬝ᵥ (P.Q *ᵥ ys k) : ℝ) : EReal) :=
            add_le_add_right (iInf_le _ k) _
        _ = ((b ⬝ᵥ (P.C *ᵥ x) : ℝ) : EReal) +
            (((ξ ⬝ᵥ (P.C *ᵥ x) + ξ ⬝ᵥ (P.Q *ᵥ ys k) - b ⬝ᵥ (P.C *ᵥ x) : ℝ)) : EReal) := by
            norm_cast; ring_nf
        _ ≤ _ := add_le_add_right hinf _
    · -- no feasible second-stage decision: objPO x = ⊤
      rw [Finset.not_nonempty_iff_eq_empty] at hYx
      refine le_top.trans (le_of_eq ?_)
      symm
      unfold Problem.objPO
      obtain ⟨ξ0, hξ0⟩ := P.Xi_nonempty
      refine eq_top_iff.2 (le_iSup₂_of_le ξ0 hξ0 (le_of_eq ?_))
      have : (⨅ y ∈ P.Y, ⨅ (_ : P.T *ᵥ x + P.W *ᵥ y ≤ P.h),
          ((ξ0 ⬝ᵥ (P.Q *ᵥ y) : ℝ) : EReal)) = ⊤ := by
        refine iInf₂_eq_top.2 fun y hy => iInf_eq_top.2 fun hf => ?_
        have : y ∈ Yx := Finset.mem_filter.2 ⟨hy, hf⟩
        rw [hYx] at this
        exact absurd this (Finset.notMem_empty y)
      rw [this, EReal.coe_add_top]
  · unfold Problem.optPOK
    refine le_iInf fun x => le_iInf fun ys => le_iInf fun hF => ?_
    refine (iInf₂_le x hF.1).trans ?_
    unfold Problem.objPO Problem.objPOK
    refine iSup₂_mono fun ξ _ => add_le_add_right ?_ _
    refine le_iInf fun k => ?_
    exact (iInf₂_le (ys k) (hF.2 k).1).trans (iInf_le _ (hF.2 k).2)

#print axioms solution
