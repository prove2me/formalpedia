-- Prove2me | solution 1 for L1Sparsifiers.Main.lemma_16
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:49:08.886006+00:00
-- url     : https://prove2.me/submissions/ed059fcb-9209-4401-992b-f348e38bf640
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_L1Sparsifiers_Main_Zonotope
import Definitions.Def_L1Sparsifiers_Main_SeparatelyConvex
import Definitions.Def_L1Sparsifiers_Main_ConvexBodyVolumes
import Theorems.Thm_L1Sparsifiers_Main_lemma_15

open MeasureTheory L1Sparsifiers.Main

namespace AuxLemma16

lemma segment_symm_eq {n : ℕ} (v : Fin n → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    segment ℝ (-(u • v)) (u • v) = {w | ∃ c : ℝ, |c| ≤ u ∧ w = c • v} := by
  ext w
  simp only [segment, Set.mem_ofPred]
  constructor
  · rintro ⟨a, b, ha, hb, hab, rfl⟩
    refine ⟨(b - a) * u, ?_, ?_⟩
    · have habs : |b - a| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      calc |(b - a) * u| = |b - a| * |u| := abs_mul _ _
        _ = |b - a| * u := by rw [abs_of_nonneg hu]
        _ ≤ 1 * u := mul_le_mul_of_nonneg_right habs hu
        _ = u := one_mul u
    · ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
  · rintro ⟨c, hc, rfl⟩
    by_cases hu0 : u = 0
    · have hc0 : c = 0 := abs_nonpos_iff.mp (hc.trans_eq hu0)
      subst hu0 hc0
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      simp
    · have hu_pos : 0 < u := lt_of_le_of_ne hu (Ne.symm hu0)
      have hcu := abs_le.mp hc
      refine ⟨(u - c) / (2 * u), (u + c) / (2 * u),
        div_nonneg (by linarith) (by positivity),
        div_nonneg (by linarith) (by positivity),
        by field_simp [hu_pos.ne']; ring, ?_⟩
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      field_simp [hu_pos.ne']
      ring

lemma minkowskiSub_compact_convex {n : ℕ} {K L : Set (Fin n → ℝ)}
    (hKc : IsCompact K) (hKcv : Convex ℝ K) (h0L : (0 : Fin n → ℝ) ∈ L) :
    IsCompact (minkowskiSub K L) ∧ Convex ℝ (minkowskiSub K L) := by
  have hsub : minkowskiSub K L ⊆ K := by
    intro x hx
    simpa using hx 0 h0L
  have hclosed : IsClosed (minkowskiSub K L) := by
    have heq : minkowskiSub K L = ⋂ y ∈ L, (fun x : Fin n → ℝ => x + y) ⁻¹' K := by
      ext x
      simp [minkowskiSub]
    rw [heq]
    exact isClosed_biInter (fun y _ => hKc.isClosed.preimage (continuous_id.add continuous_const))
  refine ⟨Metric.isCompact_of_isClosed_isBounded hclosed (hKc.isBounded.subset hsub), ?_⟩
  intro x1 hx1 x2 hx2 a b ha hb hab y hy
  have h1 : x1 + y ∈ K := hx1 y hy
  have h2 : x2 + y ∈ K := hx2 y hy
  have hcomb : (a • x1 + b • x2) + y = a • (x1 + y) + b • (x2 + y) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc a * x1 i + b * x2 i + y i
        = a * x1 i + b * x2 i + (a + b) * y i := by rw [hab, one_mul]
      _ = a * (x1 i + y i) + b * (x2 i + y i) := by ring
  rw [hcomb]
  exact hKcv h1 h2 ha hb hab

lemma minkowskiSub_zonotope_update {m n : ℕ} (K : Set (Fin n → ℝ))
    (A : Matrix (Fin m) (Fin n) ℝ) (t : Fin m → ℝ)
    (j : Fin m) {u : ℝ} (hu : 0 ≤ u) :
    minkowskiSub K (zonotope A (Function.update t j u)) =
      minkowskiSub (minkowskiSub K (zonotope A (Function.update t j 0)))
        (segment ℝ (-(u • A j)) (u • A j)) := by
  classical
  have hseg := segment_symm_eq (A j) hu
  have hdecomp : zonotope A (Function.update t j u) =
      {z | ∃ y1 ∈ zonotope A (Function.update t j 0),
        ∃ y2 ∈ segment ℝ (-(u • A j)) (u • A j), z = y1 + y2} := by
    ext z
    rw [hseg]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨∑ i, (Function.update y j 0) i • A i, ⟨Function.update y j 0, ?_, rfl⟩,
        y j • A j, ⟨y j, ?_, rfl⟩, ?_⟩
      · intro i
        by_cases hij : i = j
        · subst hij; simp
        · simp only [Function.update_of_ne hij]
          simpa [hij] using hy i
      · simpa using hy j
      · have hsplit : ∀ i : Fin m,
            y i • A i = (Function.update y j 0) i • A i + (if i = j then y j • A j else 0) := by
          intro i
          by_cases hij : i = j
          · subst hij; simp
          · simp [hij]
        calc ∑ i, y i • A i
            = ∑ i, ((Function.update y j 0) i • A i + (if i = j then y j • A j else 0)) :=
                Finset.sum_congr rfl (fun i _ => hsplit i)
          _ = (∑ i, (Function.update y j 0) i • A i) + y j • A j := by
                rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j]
                simp
    · rintro ⟨y1, ⟨y', hy', rfl⟩, y2, ⟨c, hc, rfl⟩, rfl⟩
      have hy'j : y' j = 0 := abs_nonpos_iff.mp (by simpa using hy' j)
      refine ⟨Function.update y' j c, ?_, ?_⟩
      · intro i
        by_cases hij : i = j
        · subst hij; simp [hc]
        · simp only [Function.update_of_ne hij]
          simpa [hij] using hy' i
      · have hsplit : ∀ i : Fin m,
            (Function.update y' j c) i • A i = y' i • A i + (if i = j then c • A j else 0) := by
          intro i
          by_cases hij : i = j
          · subst hij; simp [hy'j]
          · simp [hij]
        calc (∑ i, y' i • A i) + c • A j
            = ∑ i, (y' i • A i + (if i = j then c • A j else 0)) := by
                rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ j]
                simp
          _ = ∑ i, (Function.update y' j c) i • A i :=
                Finset.sum_congr rfl (fun i _ => (hsplit i).symm)
  ext x
  rw [hdecomp]
  simp only [minkowskiSub, Set.mem_ofPred]
  constructor
  · intro hx y2 hy2 y1 hy1
    have hsum : (x + y2) + y1 = x + (y1 + y2) := by abel
    rw [hsum]
    exact hx (y1 + y2) ⟨y1, hy1, y2, hy2, rfl⟩
  · rintro hx _ ⟨y1, hy1, y2, hy2, rfl⟩
    have hsum : x + (y1 + y2) = (x + y2) + y1 := by abel
    rw [hsum]
    exact hx y2 hy2 y1 hy1

end AuxLemma16

theorem solution {m n : ℕ} (K : Set (Fin n → ℝ)) (hK : IsConvexBody K)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    SepConvexOn (Set.Ici (0 : ℝ))
      (fun t : Fin m → ℝ => (volume (minkowskiSub K (zonotope A t))).toReal) := by
  intro t ht j
  let L : Set (Fin n → ℝ) := zonotope A (Function.update t j 0)
  have h0L : (0 : Fin n → ℝ) ∈ L := by
    refine ⟨0, fun i => ?_, by simp⟩
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Set.mem_Ici.mp (ht i)]
  obtain ⟨hKc', hKcv'⟩ := AuxLemma16.minkowskiSub_compact_convex hK.2.1 hK.1 h0L
  have h15 := L1Sparsifiers.Main.lemma_15 (minkowskiSub K L) hKc' hKcv' (A j)
  refine h15.congr ?_
  intro u hu
  dsimp only
  congr 2
  exact (AuxLemma16.minkowskiSub_zonotope_update K A t j
    (Set.mem_Ici.mp hu)).symm
