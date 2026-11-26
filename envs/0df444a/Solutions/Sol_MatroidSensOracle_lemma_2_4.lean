-- Prove2me | solution 1 for MatroidSensOracle.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:53:17.268496+00:00
-- url     : https://prove2.me/submissions/fb3c3819-48c9-4042-af7f-ae045b5b18d4

import Mathlib
import Definitions.Def_MatroidSensOracle_LinearMatroid

set_option autoImplicit false
namespace MatroidSensOracle

/-- **Lemma 2.4 (Cauchy–Binet).** Choudhary, Kumar, Saggi, arXiv:2609.01283 (held version, sha256
0de50841…), p.12 (PDF p.15): "Let A and B be two r × m matrices with m ⩾ r. Then
det(AB^T) = Σ_{S⊆[m], |S|=r} det(A_S) det(B_S), where the sum ranges over all (m choose r) subsets S of
size r, and A_S, B_S denote the corresponding r × r submatrices."

**Formalization Note.** Stated over any commutative ring `R` (the paper uses a field). `A_S` is
`colSub A S`, the columns of `S` in increasing order; the sum runs over the `r`-element subsets
`S ⊆ Fin m`. -/
theorem p2m_cauchyBinet {R : Type*} [CommRing R] (r : ℕ) {K : Type*} [Fintype K] [LinearOrder K]
    (M : Matrix (Fin r) K R) (N : Matrix K (Fin r) R) :
    (M * N).det = ∑ J ∈ (Finset.univ : Finset K).powersetCard r,
      if h : J.card = r then (M.submatrix id (J.orderEmbOfFin h)).det * (N.submatrix (J.orderEmbOfFin h) id).det else 0 := by
  classical
  have hexp : (M * N).det = ∑ f : Fin r → K, (∏ i, M i (f i)) * (N.submatrix f id).det := by
    have hrow : (fun i => (M * N) i) = fun i => ∑ k, M i k • N k := by
      funext i j
      simp [Matrix.mul_apply, Finset.sum_apply, Pi.smul_apply]
    show Matrix.detRowAlternating (fun i => (M * N) i) = _
    rw [hrow]
    have := (Matrix.detRowAlternating (R := R) (n := Fin r)).toMultilinearMap.map_sum (g := fun i k => M i k • N k)
    rw [show (Matrix.detRowAlternating (fun i => ∑ k, M i k • N k) : R)
        = (Matrix.detRowAlternating (R := R) (n := Fin r)).toMultilinearMap (fun i => ∑ k, M i k • N k) from rfl, this]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [MultilinearMap.map_smul_univ]
    rfl
  have hzero : ∀ f : Fin r → K, ¬ Function.Injective f → (N.submatrix f id).det = 0 := by
    intro f hf
    rw [Function.Injective] at hf
    push Not at hf
    obtain ⟨a, b, hab, hne⟩ := hf
    exact Matrix.det_zero_of_row_eq hne (funext fun j => by simp [Matrix.submatrix_apply, hab])
  rw [hexp, ← Finset.sum_filter_of_ne (p := fun f : Fin r → K => Function.Injective f)
    (fun f _ h => by
      by_contra hf
      exact h (by rw [hzero f hf, mul_zero]))]
  have hmaps : ∀ f ∈ (Finset.univ.filter fun f : Fin r → K => Function.Injective f),
      Finset.univ.image f ∈ (Finset.univ : Finset K).powersetCard r := by
    intro f hf
    rw [Finset.mem_filter] at hf
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, by rw [Finset.card_image_of_injective _ hf.2, Finset.card_univ, Fintype.card_fin]⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun J hJ => ?_
  have h : J.card = r := (Finset.mem_powersetCard.1 hJ).2
  rw [dif_pos h]
  set e := J.orderEmbOfFin h with he
  have hbij : ∑ f ∈ (Finset.univ.filter fun f : Fin r → K => Function.Injective f).filter (fun f => Finset.univ.image f = J),
        (∏ i, M i (f i)) * (N.submatrix f id).det
      = ∑ σ : Equiv.Perm (Fin r), (∏ i, M i (e (σ i))) * (N.submatrix (fun i => e (σ i)) id).det := by
    symm
    refine Finset.sum_bij (fun σ _ => fun i => e (σ i)) ?_ ?_ ?_ ?_
    · intro σ _
      rw [Finset.mem_filter, Finset.mem_filter]
      have hinj : Function.Injective fun i => e (σ i) := e.injective.comp σ.injective
      refine ⟨⟨Finset.mem_univ _, hinj⟩, ?_⟩
      refine Finset.eq_of_subset_of_card_le (fun x hx => ?_) ?_
      · obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hx
        exact J.orderEmbOfFin_mem h _
      · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin, h]
    · intro σ _ τ _ hst
      exact Equiv.ext fun i => e.injective (congrFun hst i)
    · intro f hf
      rw [Finset.mem_filter, Finset.mem_filter] at hf
      obtain ⟨⟨_, hinj⟩, himg⟩ := hf
      have hmem : ∀ i, ∃ k, e k = f i := by
        intro i
        have : f i ∈ J := himg ▸ Finset.mem_image_of_mem f (Finset.mem_univ i)
        have hr : f i ∈ Set.range e := by rw [he, Finset.range_orderEmbOfFin]; exact this
        exact hr
      choose g hg using hmem
      have ginj : Function.Injective g := fun a b hab => hinj (by rw [← hg a, ← hg b, hab])
      refine ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.1 ginj), Finset.mem_univ _, ?_⟩
      funext i; exact hg i
    · intro σ _; rfl
  rw [hbij]
  have hdetN : ∀ σ : Equiv.Perm (Fin r), (N.submatrix (fun i => e (σ i)) id).det
      = (Equiv.Perm.sign σ : R) * (N.submatrix e id).det := by
    intro σ
    have : N.submatrix (fun i => e (σ i)) id = (N.submatrix e id).submatrix σ id := rfl
    rw [this, Matrix.det_permute]
  simp only [hdetN]
  have hM : (M.submatrix id e).det = ∑ σ : Equiv.Perm (Fin r), (Equiv.Perm.sign σ : R) * ∏ i, M i (e (σ i)) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  rw [hM, Finset.sum_mul]
  exact Finset.sum_congr rfl fun σ _ => by ring


theorem _root_.solution {R : Type*} [CommRing R] {r m : ℕ} (hrm : r ≤ m) (A B : Matrix (Fin r) (Fin m) R) :
    (A * B.transpose).det =
      ∑ S : {S : Finset (Fin m) // S.card = r}, (colSub A S.1 S.2).det * (colSub B S.1 S.2).det := by
  rw [p2m_cauchyBinet r A B.transpose, Finset.sum_subtype ((Finset.univ : Finset (Fin m)).powersetCard r) (p := fun S => S.card = r) (fun S => by simp)]
  refine Finset.sum_congr rfl fun S _ => ?_
  rw [dif_pos S.2, ← Matrix.det_transpose (MatroidSensOracle.colSub B S.1 S.2)]
  rfl


end MatroidSensOracle

