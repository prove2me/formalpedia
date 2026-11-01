-- Prove2me | solution 1 for KarpPapadimitriou.SmallFacial.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-31T14:37:45.68399+00:00
-- url     : https://prove2.me/submissions/3f361be0-a0ac-4b94-bbc2-5ab23579c107

import Mathlib
import Definitions.Def_KarpPapadimitriou_SmallFacial_COP

set_option autoImplicit false

namespace KPSF

open Matrix

/-- Move from `y` along `w` until a new row becomes tight. -/
lemma move_step {d : ℕ} {ι : Type} [Fintype ι] (a : ι → Fin d → ℚ) (b : ι → ℚ)
    (y w : Fin d → ℚ) (hy : ∀ i, a i ⬝ᵥ y ≤ b i)
    (hw : ∀ i, a i ⬝ᵥ y = b i → a i ⬝ᵥ w = 0) (hpos : ∃ i, 0 < a i ⬝ᵥ w) :
    ∃ t : ℚ, 0 < t ∧ (∀ i, a i ⬝ᵥ (y + t • w) ≤ b i) ∧
      (∀ i, a i ⬝ᵥ y = b i → a i ⬝ᵥ (y + t • w) = b i) ∧
      ∃ i, a i ⬝ᵥ y < b i ∧ a i ⬝ᵥ (y + t • w) = b i := by
  classical
  set P := Finset.univ.filter (fun i => 0 < a i ⬝ᵥ w) with hP
  have hPne : P.Nonempty := by
    obtain ⟨i, hi⟩ := hpos
    exact ⟨i, by simp [hP, hi]⟩
  obtain ⟨i0, hi0, hmin⟩ :=
    P.exists_min_image (fun i => (b i - a i ⬝ᵥ y) / (a i ⬝ᵥ w)) hPne
  have hi0' : 0 < a i0 ⬝ᵥ w := by simpa [hP] using hi0
  have hslack : a i0 ⬝ᵥ y < b i0 := by
    rcases (hy i0).lt_or_eq with h | h
    · exact h
    · exact absurd (hw i0 h) (ne_of_gt hi0')
  have ht : 0 < (b i0 - a i0 ⬝ᵥ y) / (a i0 ⬝ᵥ w) := div_pos (by linarith) hi0'
  refine ⟨(b i0 - a i0 ⬝ᵥ y) / (a i0 ⬝ᵥ w), ht, ?_, ?_, i0, hslack, ?_⟩
  · intro i
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    by_cases hi : 0 < a i ⬝ᵥ w
    · have h1 := hmin i (by simp [hP, hi])
      have h2 := (le_div_iff₀ hi).1 h1
      linarith
    · have : (b i0 - a i0 ⬝ᵥ y) / (a i0 ⬝ᵥ w) * (a i ⬝ᵥ w) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos ht.le (not_lt.1 hi)
      linarith [hy i]
  · intro i hi
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hw i hi, mul_zero, add_zero, hi]
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul, div_mul_cancel₀ _ (ne_of_gt hi0')]
    ring

/-- A vertex: feasible, and the tight rows have trivial common null space. -/
def IsVert {d : ℕ} {ι : Type} (a : ι → Fin d → ℚ) (b : ι → ℚ) (v : Fin d → ℚ) : Prop :=
  (∀ i, a i ⬝ᵥ v ≤ b i) ∧ ∀ w : Fin d → ℚ, (∀ i, a i ⬝ᵥ v = b i → a i ⬝ᵥ w = 0) → w = 0

/-- Every point of a "bounded" system is a convex combination of vertices. -/
theorem vert_decomp {d : ℕ} {ι : Type} [Fintype ι] (a : ι → Fin d → ℚ) (b : ι → ℚ)
    (hbd : ∀ w : Fin d → ℚ, w ≠ 0 → ∃ i, 0 < a i ⬝ᵥ w) :
    ∀ y, (∀ i, a i ⬝ᵥ y ≤ b i) → y ∈ convexHull ℚ {v | IsVert a b v} := by
  classical
  suffices H : ∀ N : ℕ, ∀ y, (∀ i, a i ⬝ᵥ y ≤ b i) →
      (Finset.univ.filter (fun i => a i ⬝ᵥ y < b i)).card ≤ N →
        y ∈ convexHull ℚ {v | IsVert a b v} from
    fun y hy => H _ y hy le_rfl
  intro N
  induction N with
  | zero =>
    intro y hy hc
    apply subset_convexHull
    refine ⟨hy, fun w hw => ?_⟩
    by_contra hne
    obtain ⟨i, hi⟩ := hbd w hne
    have hz := Finset.card_eq_zero.1 (Nat.le_zero.1 hc)
    have : a i ⬝ᵥ y = b i := by
      rcases (hy i).lt_or_eq with h | h
      · have hm : i ∈ Finset.univ.filter (fun i => a i ⬝ᵥ y < b i) :=
          Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩
        rw [hz] at hm
        exact absurd hm (Finset.notMem_empty i)
      · exact h
    linarith [hw i this]
  | succ N ih =>
    intro y hy hc
    by_cases hv : IsVert a b y
    · exact subset_convexHull ℚ _ hv
    · have hex : ∃ w, (∀ i, a i ⬝ᵥ y = b i → a i ⬝ᵥ w = 0) ∧ w ≠ 0 := by
        by_contra h
        push_neg at h
        exact hv ⟨hy, h⟩
      obtain ⟨w, hw, hw0⟩ := hex
      obtain ⟨t1, ht1, hf1, hk1, i1, hs1, he1⟩ := move_step a b y w hy hw (hbd w hw0)
      obtain ⟨t2, ht2, hf2, hk2, i2, hs2, he2⟩ := move_step a b y (-w) hy
        (fun i hi => by rw [dotProduct_neg, hw i hi, neg_zero]) (hbd (-w) (neg_ne_zero.2 hw0))
      have hcard : ∀ y' : Fin d → ℚ, (∀ i, a i ⬝ᵥ y = b i → a i ⬝ᵥ y' = b i) →
          (∃ i, a i ⬝ᵥ y < b i ∧ a i ⬝ᵥ y' = b i) →
          (Finset.univ.filter (fun i => a i ⬝ᵥ y' < b i)).card ≤ N := by
        intro y' hk ⟨i, hs, he⟩
        have hsub : Finset.univ.filter (fun i => a i ⬝ᵥ y' < b i) ⊂
            Finset.univ.filter (fun i => a i ⬝ᵥ y < b i) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨i, by simp [hs], by simp [he]⟩
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            by_contra hne
            have heq : a j ⬝ᵥ y = b j := le_antisymm (hy j) (not_lt.1 hne)
            rw [hk j heq] at hj
            exact lt_irrefl _ hj
        have := Finset.card_lt_card hsub
        omega
      have h1 := ih _ hf1 (hcard _ hk1 ⟨i1, hs1, he1⟩)
      have h2 := ih _ hf2 (hcard _ hk2 ⟨i2, hs2, he2⟩)
      have hconv := convex_convexHull ℚ {v | IsVert a b v}
      have hsum : 0 < t1 + t2 := by linarith
      have key : y = (t2 / (t1 + t2)) • (y + t1 • w) + (t1 / (t1 + t2)) • (y + t2 • -w) := by
        ext j
        simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
        field_simp
        ring
      rw [key]
      exact hconv h1 h2 (div_nonneg ht2.le hsum.le) (div_nonneg ht1.le hsum.le)
        (by field_simp; ring)

/-- Size bound used for vertices. -/
def Xb {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) (b : ι → ℤ) : ℤ :=
  1 + ∑ i, (∑ j, |A i j| + |b i|) ^ 2

def Bv (d : ℕ) (X : ℤ) : ℤ := (Nat.factorial d : ℤ) * X ^ d * (d * ((Nat.factorial d : ℤ) * X ^ d * X))

lemma Xb_pos {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) (b : ι → ℤ) : 1 ≤ Xb A b := by
  unfold Xb
  have : 0 ≤ ∑ i, (∑ j, |A i j| + |b i|) ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

lemma row_le {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) (b : ι → ℤ) (i : ι) (j : Fin d) :
    |A i j| ≤ ∑ j, |A i j| + |b i| := by
  have := Finset.single_le_sum (f := fun j => |A i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)
  linarith [abs_nonneg (b i)]

lemma rhs_le {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) (b : ι → ℤ) (i : ι) :
    |b i| ≤ ∑ j, |A i j| + |b i| := by
  have : 0 ≤ ∑ j, |A i j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  linarith

/-- Integrality of vertices: a positive multiple of a vertex is a small integer vector. -/
theorem vert_int {d : ℕ} {ι : Type} [Fintype ι] (A : ι → Fin d → ℤ) (b : ι → ℤ)
    (v : Fin d → ℚ) (hv : IsVert (fun i j => (A i j : ℚ)) (fun i => (b i : ℚ)) v) :
    ∃ (r : Fin d → ℤ) (N : ℚ), 0 < N ∧ (fun j => (r j : ℚ)) = N • v ∧
      ∀ j, |r j| ≤ Bv d (Xb A b) := by
  classical
  set a : ι → Fin d → ℚ := fun i j => (A i j : ℚ) with ha
  set T := Finset.univ.filter (fun i => a i ⬝ᵥ v = (b i : ℚ)) with hT
  let H : Matrix (Fin d) (Fin d) ℤ := Matrix.of fun j k => ∑ i ∈ T, A i j * A i k
  let β : Fin d → ℤ := fun k => ∑ i ∈ T, b i * A i k
  let Hq : Matrix (Fin d) (Fin d) ℚ := (Int.castRingHom ℚ).mapMatrix H
  have hHq : ∀ j k, Hq j k = ∑ i ∈ T, a i j * a i k := by
    intro j k
    simp [Hq, H, a]
  have hmul : ∀ w : Fin d → ℚ, Hq *ᵥ w = fun j => ∑ i ∈ T, a i j * (a i ⬝ᵥ w) := by
    intro w
    ext j
    simp only [mulVec, dotProduct, hHq, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => by ring))
  have hHv : Hq *ᵥ v = fun k => (β k : ℚ) := by
    rw [hmul]
    ext k
    simp only [β, Int.cast_sum, Int.cast_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    have : a i ⬝ᵥ v = (b i : ℚ) := (Finset.mem_filter.1 hi).2
    rw [this, mul_comm]
  have hdet : Hq.det ≠ 0 := by
    intro h0
    obtain ⟨w, hw0, hw⟩ := (Matrix.exists_mulVec_eq_zero_iff).2 h0
    apply hw0
    apply hv.2
    intro i hi
    have hiT : i ∈ T := Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩
    have hq : w ⬝ᵥ (Hq *ᵥ w) = ∑ i ∈ T, (a i ⬝ᵥ w) ^ 2 := by
      rw [hmul]
      simp only [dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [sq, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => by ring)
    rw [hw, dotProduct_zero] at hq
    have hnn : ∀ i ∈ T, 0 ≤ (a i ⬝ᵥ w) ^ 2 := fun i _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hq.symm i hiT
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  have hdetZ : (H.det : ℚ) = Hq.det := by
    exact RingHom.map_det (Int.castRingHom ℚ) H
  have hadj : Hq.adjugate = (Int.castRingHom ℚ).mapMatrix H.adjugate :=
    (RingHom.map_adjugate (Int.castRingHom ℚ) H).symm
  -- det • v = adj *ᵥ β
  have hcr : Hq.det • v = Hq.adjugate *ᵥ (fun k => (β k : ℚ)) := by
    rw [← hHv, mulVec_mulVec, adjugate_mul, smul_mulVec, one_mulVec]
  let r : Fin d → ℤ := H.det • (H.adjugate *ᵥ β)
  have hdet0 : (H.det : ℚ) ≠ 0 := by rw [hdetZ]; exact hdet
  refine ⟨r, (H.det : ℚ) ^ 2, by positivity, ?_, ?_⟩
  · have e2 : (fun k => ((H.adjugate *ᵥ β) k : ℚ)) = Hq.adjugate *ᵥ (fun k => (β k : ℚ)) := by
      rw [hadj]
      ext k
      simp [mulVec, dotProduct]
    ext j
    have := congrFun hcr j
    rw [← e2] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this ⊢
    simp only [r, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [← this, hdetZ]
    ring
  · intro j
    set X := Xb A b with hX
    have hX1 : 1 ≤ X := Xb_pos A b
    have hS : ∀ i, (∑ j, |A i j| + |b i|) ^ 2 ≤ X - 1 := by
      intro i
      have := Finset.single_le_sum (f := fun i => (∑ j, |A i j| + |b i|) ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ i)
      simp only [hX, Xb]
      linarith
    have hRnn : ∀ i, 0 ≤ ∑ j, |A i j| + |b i| := fun i =>
      add_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)) (abs_nonneg _)
    have hsumS : ∑ i, (∑ j, |A i j| + |b i|) ^ 2 ≤ X := by simp only [hX, Xb]; linarith
    have hH : ∀ j k, |H j k| ≤ X := by
      intro j k
      calc |H j k| = |∑ i ∈ T, A i j * A i k| := rfl
        _ ≤ ∑ i ∈ T, |A i j * A i k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ T, (∑ j, |A i j| + |b i|) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul, sq]
          exact mul_le_mul (row_le A b i j) (row_le A b i k) (abs_nonneg _) (hRnn i)
        _ ≤ ∑ i, (∑ j, |A i j| + |b i|) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => sq_nonneg _)
        _ ≤ X := hsumS
    have hβ : ∀ k, |β k| ≤ X := by
      intro k
      calc |β k| = |∑ i ∈ T, b i * A i k| := rfl
        _ ≤ ∑ i ∈ T, |b i * A i k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ T, (∑ j, |A i j| + |b i|) ^ 2 := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [abs_mul, sq]
          exact mul_le_mul (rhs_le A b i) (row_le A b i k) (abs_nonneg _) (hRnn i)
        _ ≤ ∑ i, (∑ j, |A i j| + |b i|) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun i _ _ => sq_nonneg _)
        _ ≤ X := hsumS
    have hdetb : |H.det| ≤ (Nat.factorial d : ℤ) * X ^ d := by
      have := Matrix.det_le (A := H) (abv := AbsoluteValue.abs) (x := X) hH
      simpa [Fintype.card_fin, nsmul_eq_mul] using this
    have hadjb : ∀ j k, |H.adjugate j k| ≤ (Nat.factorial d : ℤ) * X ^ d := by
      intro j k
      rw [adjugate_apply]
      have := Matrix.det_le (A := H.updateRow k (Pi.single j 1)) (abv := AbsoluteValue.abs)
        (x := X) (by
          intro p q
          by_cases hp : p = k
          · subst hp
            simp only [updateRow_self]
            by_cases hq : q = j
            · subst hq; simp; exact hX1
            · simp [Pi.single_apply, hq]; linarith
          · simp only [updateRow_ne hp]
            exact hH p q)
      simpa [Fintype.card_fin, nsmul_eq_mul] using this
    have hav : |(H.adjugate *ᵥ β) j| ≤ d * ((Nat.factorial d : ℤ) * X ^ d * X) := by
      calc |(H.adjugate *ᵥ β) j| = |∑ k, H.adjugate j k * β k| := rfl
        _ ≤ ∑ k, |H.adjugate j k * β k| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin d, ((Nat.factorial d : ℤ) * X ^ d * X) := by
          refine Finset.sum_le_sum (fun k _ => ?_)
          rw [abs_mul]
          exact mul_le_mul (hadjb j k) (hβ k) (abs_nonneg _) (by positivity)
        _ = d * ((Nat.factorial d : ℤ) * X ^ d * X) := by simp
    calc |r j| = |H.det| * |(H.adjugate *ᵥ β) j| := by
          simp [r, abs_mul]
      _ ≤ ((Nat.factorial d : ℤ) * X ^ d) * (d * ((Nat.factorial d : ℤ) * X ^ d * X)) :=
          mul_le_mul hdetb hav (abs_nonneg _) (by positivity)
      _ = Bv d X := by unfold Bv; ring

/-- Box-bounded integer generators of the cone `{r | A r ≤ 0}`. -/
noncomputable def gens {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) (B : ℤ) : Finset (Fin d → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.Icc (-B) B).filter (fun r => ∀ i, A i ⬝ᵥ r ≤ 0)

lemma mem_gens {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) (B : ℤ) (r : Fin d → ℤ) :
    r ∈ gens A B ↔ (∀ j, |r j| ≤ B) ∧ ∀ i, A i ⬝ᵥ r ≤ 0 := by
  classical
  unfold gens
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc, abs_le]

/-- Nonnegative combination of a finite set of integer vectors. -/
def InCone {d : ℕ} (G : Finset (Fin d → ℤ)) (u : Fin d → ℚ) : Prop :=
  ∃ μ : (Fin d → ℤ) → ℚ, (∀ r ∈ G, 0 ≤ μ r) ∧ u = ∑ r ∈ G, μ r • (fun j => (r j : ℚ))

lemma inCone_zero {d : ℕ} (G : Finset (Fin d → ℤ)) : InCone G 0 :=
  ⟨fun _ => 0, fun _ _ => le_rfl, by simp⟩

lemma inCone_add {d : ℕ} {G : Finset (Fin d → ℤ)} {u v : Fin d → ℚ}
    (hu : InCone G u) (hv : InCone G v) : InCone G (u + v) := by
  obtain ⟨μ, hμ, rfl⟩ := hu
  obtain ⟨ν, hν, rfl⟩ := hv
  refine ⟨μ + ν, fun r hr => add_nonneg (hμ r hr) (hν r hr), ?_⟩
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Pi.add_apply, add_smul]

lemma inCone_smul {d : ℕ} {G : Finset (Fin d → ℤ)} {u : Fin d → ℚ} (t : ℚ) (ht : 0 ≤ t)
    (hu : InCone G u) : InCone G (t • u) := by
  obtain ⟨μ, hμ, rfl⟩ := hu
  refine ⟨t • μ, fun r hr => mul_nonneg ht (hμ r hr), ?_⟩
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, mul_smul]

lemma inCone_convex {d : ℕ} (G : Finset (Fin d → ℤ)) : Convex ℚ {u | InCone G u} := by
  intro x hx y hy s t hs ht _
  exact inCone_add (inCone_smul s hs hx) (inCone_smul t ht hy)

lemma inCone_mono {d : ℕ} {G G' : Finset (Fin d → ℤ)} (h : G ⊆ G') {u : Fin d → ℚ}
    (hu : InCone G u) : InCone G' u := by
  classical
  obtain ⟨μ, hμ, rfl⟩ := hu
  refine ⟨fun r => if r ∈ G then μ r else 0, fun r _ => ?_, ?_⟩
  · dsimp only
    split_ifs with h1
    · exact hμ r h1
    · exact le_rfl
  · rw [← Finset.sum_subset h (fun r _ hr => by simp [hr])]
    refine Finset.sum_congr rfl (fun r hr => by simp [hr])

lemma inCone_gen {d : ℕ} {G : Finset (Fin d → ℤ)} {r : Fin d → ℤ} (hr : r ∈ G) :
    InCone G (fun j => (r j : ℚ)) := by
  classical
  refine ⟨fun r' => if r' = r then 1 else 0, fun r' _ => by dsimp only; split_ifs <;> norm_num, ?_⟩
  rw [Finset.sum_eq_single r]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd hr h

lemma cast_dot {d : ℕ} (x y : Fin d → ℤ) :
    ((x ⬝ᵥ y : ℤ) : ℚ) = (fun j => (x j : ℚ)) ⬝ᵥ (fun j => (y j : ℚ)) := by
  simp [dotProduct]

/-- Slice rows of a cone. -/
def sliceA {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) : ι ⊕ Bool → Fin d → ℤ :=
  Sum.elim A (fun t => if t then -∑ i, A i else ∑ i, A i)

def sliceB {ι : Type} : ι ⊕ Bool → ℤ := Sum.elim (fun _ => 0) (fun t => if t then 1 else -1)

/-- The generator bound of the cone `{u | A u ≤ 0}`. -/
def Bc {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) : ℤ :=
  Bv d (Xb (sliceA A) (sliceB (ι := ι)))

lemma csum_dot {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ) (u : Fin d → ℚ) :
    (fun j => ((∑ i, A i) j : ℚ)) ⬝ᵥ u = ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u := by
  simp only [dotProduct, Finset.sum_apply, Int.cast_sum, Finset.sum_mul]
  exact Finset.sum_comm

/-- Pointed rational cones are generated by small integer vectors. -/
theorem cone_gen {ι : Type} [Fintype ι] {d : ℕ} (A : ι → Fin d → ℤ)
    (hpt : ∀ u : Fin d → ℚ, (∀ i, (fun j => (A i j : ℚ)) ⬝ᵥ u = 0) → u = 0) :
    ∀ u : Fin d → ℚ, (∀ i, (fun j => (A i j : ℚ)) ⬝ᵥ u ≤ 0) → InCone (gens A (Bc A)) u := by
  classical
  intro u hu
  set aS : ι ⊕ Bool → Fin d → ℚ := fun k j => (sliceA A k j : ℚ) with haS
  set bS : ι ⊕ Bool → ℚ := fun k => (sliceB (ι := ι) k : ℚ) with hbS
  have hrow_inl : ∀ i (w : Fin d → ℚ), aS (Sum.inl i) ⬝ᵥ w = (fun j => (A i j : ℚ)) ⬝ᵥ w := by
    intro i w; rfl
  have hrow_t : ∀ w : Fin d → ℚ, aS (Sum.inr true) ⬝ᵥ w = -∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ w := by
    intro w
    rw [← csum_dot]
    simp only [aS, sliceA, Sum.elim_inr, if_true]
    simp [dotProduct]
  have hrow_f : ∀ w : Fin d → ℚ, aS (Sum.inr false) ⬝ᵥ w = ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ w := by
    intro w
    rw [← csum_dot]
    simp only [aS, sliceA, Sum.elim_inr]
    simp [dotProduct]
  -- every slice vertex lies in the cone of generators
  have hvert : {v | IsVert aS bS v} ⊆ {u | InCone (gens A (Bc A)) u} := by
    intro v hv
    obtain ⟨r, N, hN, hr, hrb⟩ := vert_int (sliceA A) (sliceB (ι := ι)) v hv
    have hrg : r ∈ gens A (Bc A) := by
      rw [mem_gens]
      refine ⟨hrb, fun i => ?_⟩
      have h1 : ((A i ⬝ᵥ r : ℤ) : ℚ) = N * ((fun j => (A i j : ℚ)) ⬝ᵥ v) := by
        rw [cast_dot, hr, dotProduct_smul, smul_eq_mul]
      have h2 := hv.1 (Sum.inl i)
      rw [hrow_inl] at h2
      have h3 : (aS (Sum.inl i) ⬝ᵥ v ≤ bS (Sum.inl i)) := hv.1 (Sum.inl i)
      have hb0 : bS (Sum.inl i) = 0 := by simp [bS, sliceB]
      rw [hb0] at h3
      rw [hrow_inl] at h3
      have : ((A i ⬝ᵥ r : ℤ) : ℚ) ≤ 0 := by rw [h1]; exact mul_nonpos_of_nonneg_of_nonpos hN.le h3
      exact_mod_cast this
    have hv' : v = N⁻¹ • (fun j => (r j : ℚ)) := by
      rw [hr, smul_smul, inv_mul_cancel₀ (ne_of_gt hN), one_smul]
    rw [Set.mem_setOf_eq, hv']
    exact inCone_smul _ (inv_nonneg.2 hN.le) (inCone_gen hrg)
  by_cases hu0 : u = 0
  · rw [hu0]; exact inCone_zero _
  have hs : 0 < -∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u := by
    have hle : ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u ≤ 0 := Finset.sum_nonpos (fun i _ => hu i)
    rcases hle.lt_or_eq with h | h
    · linarith
    · exfalso
      apply hu0
      apply hpt
      have := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => hu i)).1 h
      exact fun i => this i (Finset.mem_univ i)
  set s := -∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u with hsdef
  have hbd : ∀ w : Fin d → ℚ, w ≠ 0 → ∃ k, 0 < aS k ⬝ᵥ w := by
    intro w hw
    by_cases h : ∃ i, 0 < (fun j => (A i j : ℚ)) ⬝ᵥ w
    · obtain ⟨i, hi⟩ := h
      exact ⟨Sum.inl i, by rw [hrow_inl]; exact hi⟩
    · push_neg at h
      refine ⟨Sum.inr true, ?_⟩
      rw [hrow_t]
      have hle : ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ w ≤ 0 := Finset.sum_nonpos (fun i _ => h i)
      rcases hle.lt_or_eq with h' | h'
      · linarith
      · exfalso
        apply hw
        apply hpt
        have := (Finset.sum_eq_zero_iff_of_nonpos (fun i _ => h i)).1 h'
        exact fun i => this i (Finset.mem_univ i)
  have hv0 : ∀ k, aS k ⬝ᵥ (s⁻¹ • u) ≤ bS k := by
    intro k
    rcases k with i | t
    · rw [hrow_inl, dotProduct_smul, smul_eq_mul]
      have hb0 : bS (Sum.inl i) = 0 := by simp [bS, sliceB]
      rw [hb0]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hs.le) (hu i)
    · cases t
      · rw [hrow_f]
        have : bS (Sum.inr false) = -1 := by simp [bS, sliceB]
        rw [this]
        have e : ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ (s⁻¹ • u) = s⁻¹ * ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => by rw [dotProduct_smul, smul_eq_mul])
        rw [e]
        have : s⁻¹ * ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u = -1 := by
          rw [show ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u = -s by rw [hsdef]; ring]
          field_simp
        linarith
      · rw [hrow_t]
        have : bS (Sum.inr true) = 1 := by simp [bS, sliceB]
        rw [this]
        have e : ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ (s⁻¹ • u) = s⁻¹ * ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => by rw [dotProduct_smul, smul_eq_mul])
        rw [e]
        have : s⁻¹ * ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u = -1 := by
          rw [show ∑ i, (fun j => (A i j : ℚ)) ⬝ᵥ u = -s by rw [hsdef]; ring]
          field_simp
        linarith
  have hmem := vert_decomp aS bS hbd (s⁻¹ • u) hv0
  have hc := convexHull_min hvert (inCone_convex _) hmem
  have : u = s • (s⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hs), one_smul]
  rw [this]
  exact inCone_smul s hs.le hc

lemma exists_between_fin {ι : Type} (s r : Finset ι) (L U : ι → ℚ)
    (h : ∀ q ∈ s, ∀ p ∈ r, L q ≤ U p) :
    ∃ t : ℚ, (∀ q ∈ s, L q ≤ t) ∧ ∀ p ∈ r, t ≤ U p := by
  by_cases hs : s.Nonempty
  · refine ⟨s.sup' hs L, fun q hq => Finset.le_sup' L hq, fun p hp => ?_⟩
    exact Finset.sup'_le hs L (fun q hq => h q hq p hp)
  · by_cases hr : r.Nonempty
    · exact ⟨r.inf' hr U, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => Finset.inf'_le U hp⟩
    · exact ⟨0, fun q hq => absurd ⟨q, hq⟩ hs, fun p hp => absurd ⟨p, hp⟩ hr⟩

/-- Theorem of alternatives (Fourier–Motzkin), variables indexed by `Fin n`. -/
theorem fm_alt (n : ℕ) : ∀ {ι : Type} [Fintype ι] (a : ι → Fin n → ℚ) (b : ι → ℚ),
    (∃ x : Fin n → ℚ, ∀ i, ∑ s, a i s * x s ≤ b i) ∨
    (∃ l : ι → ℚ, (∀ i, 0 ≤ l i) ∧ (∀ s, ∑ i, l i * a i s = 0) ∧ ∑ i, l i * b i < 0) := by
  induction n with
  | zero =>
    intro ι _ a b
    classical
    by_cases h : ∀ i, 0 ≤ b i
    · left; exact ⟨0, fun i => by simpa using h i⟩
    · right
      push Not at h
      obtain ⟨i, hi⟩ := h
      refine ⟨fun j => if j = i then 1 else 0, fun j => ?_, fun s => s.elim0, ?_⟩
      · dsimp only; split_ifs <;> norm_num
      · simpa using hi
  | succ n ih =>
    intro ι _ a b
    classical
    let W : ι ⊕ (ι × ι) → ι → ℚ := Sum.elim (fun z i => if a z 0 = 0 ∧ i = z then 1 else 0)
      (fun pq i => if 0 < a pq.1 0 ∧ a pq.2 0 < 0 then
        (if i = pq.1 then -a pq.2 0 else 0) + (if i = pq.2 then a pq.1 0 else 0) else 0)
    have hW0 : ∀ k i, 0 ≤ W k i := by
      intro k i
      rcases k with z | ⟨p, q⟩
      · simp only [W, Sum.elim_inl]; split_ifs <;> norm_num
      · simp only [W, Sum.elim_inr]
        split_ifs with h1 h2 h3 h3 <;> subst_vars <;> first | linarith [h1.1, h1.2] | norm_num
    let C : ι ⊕ (ι × ι) → Fin (n + 1) → ℚ := fun k s => ∑ i, W k i * a i s
    let D : ι ⊕ (ι × ι) → ℚ := fun k => ∑ i, W k i * b i
    have hC0 : ∀ k, C k 0 = 0 := by
      intro k
      rcases k with z | ⟨p, q⟩
      · by_cases hz : a z 0 = 0
        · simp [C, W, hz]
        · simp [C, W, hz]
      · by_cases h : 0 < a p 0 ∧ a q 0 < 0
        · simp only [C, W, Sum.elim_inr, if_pos h, add_mul, ite_mul, zero_mul,
            Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
        · simp [C, W, h]
    rcases ih (fun k s => C k s.succ) D with ⟨y, hy⟩ | ⟨μ, hμ0, hμ1, hμ2⟩
    · left
      let r : ι → ℚ := fun i => b i - ∑ s : Fin n, a i s.succ * y s
      have key : ∀ k, 0 ≤ ∑ i, W k i * r i := by
        intro k
        have e : ∑ i, W k i * r i = D k - ∑ s, C k s.succ * y s := by
          simp only [r, D, C, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul,
            mul_assoc]
          congr 1
          exact Finset.sum_comm
        rw [e]; linarith [hy k]
      have kinl : ∀ z, a z 0 = 0 → 0 ≤ r z := by
        intro z hz
        have := key (Sum.inl z)
        simpa [W, hz] using this
      have kinr : ∀ p q, 0 < a p 0 → a q 0 < 0 → 0 ≤ -a q 0 * r p + a p 0 * r q := by
        intro p q hp hq
        have := key (Sum.inr (p, q))
        simp only [W, Sum.elim_inr, if_pos (And.intro hp hq), add_mul, ite_mul, zero_mul,
          Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
        exact this
      obtain ⟨t, ht1, ht2⟩ := exists_between_fin (Finset.univ.filter (fun q => a q 0 < 0))
        (Finset.univ.filter (fun p => 0 < a p 0)) (fun q => r q / a q 0) (fun p => r p / a p 0)
        (by
          intro q hq p hp
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq hp
          have h := kinr p q hp hq
          have e : -a q 0 * r p + a p 0 * r q =
              -(a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0)) := by
            have h1 : r p = (r p / a p 0) * a p 0 := (div_mul_cancel₀ _ hp.ne').symm
            have h2 : r q = (r q / a q 0) * a q 0 := (div_mul_cancel₀ _ hq.ne).symm
            set U := r p / a p 0
            set V := r q / a q 0
            rw [h1, h2]; ring
          by_contra hc
          push Not at hc
          have hpq : 0 < a p 0 * (-a q 0) * (r q / a q 0 - r p / a p 0) :=
            mul_pos (mul_pos hp (neg_pos.2 hq)) (sub_pos.2 hc)
          linarith)
      refine ⟨Fin.cons t y, fun i => ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      have hr : r i = b i - ∑ s : Fin n, a i s.succ * y s := rfl
      suffices a i 0 * t ≤ r i by linarith
      rcases lt_trichotomy (a i 0) 0 with hneg | hz | hpos
      · have := ht1 i (by simp [hneg])
        rw [div_le_iff_of_neg hneg] at this
        linarith
      · rw [hz, zero_mul]; exact kinl i hz
      · have := ht2 i (by simp [hpos])
        rw [le_div_iff₀ hpos] at this
        linarith
    · right
      refine ⟨fun i => ∑ k, μ k * W k i, fun i => Finset.sum_nonneg
        (fun k _ => mul_nonneg (hμ0 k) (hW0 k i)), fun s => ?_, ?_⟩
      · have e : ∑ i, (∑ k, μ k * W k i) * a i s = ∑ k, μ k * C k s := by
          simp only [C, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]
        refine Fin.cases ?_ (fun s => ?_) s
        · simp [hC0]
        · exact hμ1 s
      · have e : ∑ i, (∑ k, μ k * W k i) * b i = ∑ k, μ k * D k := by
          simp only [D, Finset.sum_mul, Finset.mul_sum, mul_assoc]
          exact Finset.sum_comm
        rw [e]; exact hμ2



def castv {n : ℕ} (w : Fin n → ℤ) : Fin n → ℚ := fun j => (w j : ℚ)

lemma snoc_dot {R : Type} [CommRing R] {n : ℕ} (a : Fin n → R) (c : R) (v : Fin (n + 1) → R) :
    (Fin.snoc a c : Fin (n + 1) → R) ⬝ᵥ v =
      a ⬝ᵥ (fun j => v (Fin.castSucc j)) + c * v (Fin.last n) := by
  simp [dotProduct, Fin.sum_univ_castSucc]

lemma cast_snoc {n : ℕ} (a : Fin n → ℤ) (c : ℤ) :
    (fun j => ((Fin.snoc a c : Fin (n + 1) → ℤ) j : ℚ)) =
      (Fin.snoc (castv a) (c : ℚ) : Fin (n + 1) → ℚ) := by
  ext j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp
  · simp [castv]

/-- Rows of the separation polytope (variables `(f, g)`, box `|f|,|g| ≤ 1`). -/
def sepA {n : ℕ} {κ τ : Type} (W : κ → Fin n → ℤ) (R : τ → Fin n → ℤ) :
    (κ ⊕ τ) ⊕ (Fin (n + 1) × Bool) → Fin (n + 1) → ℤ :=
  Sum.elim (Sum.elim (fun k => Fin.snoc (W k) (-1)) (fun t => Fin.snoc (R t) 0))
    (fun p => if p.2 then Pi.single p.1 1 else -Pi.single p.1 1)

def sepB {κ τ : Type} {n : ℕ} : (κ ⊕ τ) ⊕ (Fin (n + 1) × Bool) → ℤ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

def Bs {n : ℕ} {κ τ : Type} [Fintype κ] [Fintype τ] (W : κ → Fin n → ℤ) (R : τ → Fin n → ℤ) : ℤ :=
  Bv (n + 1) (Xb (sepA W R) (sepB (κ := κ) (τ := τ) (n := n)))

/-- Small separation from `conv W + cone R`. -/
theorem sep {n : ℕ} {κ τ : Type} [Fintype κ] [Fintype τ] (W : κ → Fin n → ℤ) (R : τ → Fin n → ℤ)
    (x : Fin n → ℚ)
    (hx : ¬ ∃ (α : κ → ℚ) (ν : τ → ℚ), (∀ k, 0 ≤ α k) ∧ (∀ t, 0 ≤ ν t) ∧ ∑ k, α k = 1 ∧
        x = ∑ k, α k • castv (W k) + ∑ t, ν t • castv (R t)) :
    ∃ (f : Fin n → ℤ) (g : ℤ), (∀ j, |f j| ≤ Bs W R) ∧ |g| ≤ Bs W R ∧
      (∀ k, f ⬝ᵥ W k ≤ g) ∧ (∀ t, f ⬝ᵥ R t ≤ 0) ∧ (g : ℚ) < castv f ⬝ᵥ x := by
  classical
  -- Step 1: Farkas
  let a : (κ ⊕ τ) ⊕ Unit → Fin (n + 1) → ℚ :=
    Sum.elim (Sum.elim (fun k => Fin.snoc (castv (W k)) (-1)) (fun t => Fin.snoc (castv (R t)) 0))
      (fun _ => Fin.snoc (-x) 1)
  let bb : (κ ⊕ τ) ⊕ Unit → ℚ := Sum.elim (fun _ => 0) (fun _ => -1)
  obtain ⟨y, hy⟩ : ∃ y : Fin (n + 1) → ℚ, ∀ i, ∑ s, a i s * y s ≤ bb i := by
    rcases fm_alt (n + 1) a bb with h | ⟨l, hl0, hl1, hl2⟩
    · exact h
    · exfalso
      apply hx
      set lx := l (Sum.inr ()) with hlx
      have hb : ∑ i, l i * bb i = -lx := by
        simp [bb, Fintype.sum_sum_type, hlx]
      rw [hb] at hl2
      have hlxp : 0 < lx := by linarith
      have hlast := hl1 (Fin.last n)
      have hcs : ∀ j, ∑ i, l i * a i (Fin.castSucc j) = 0 := fun j => hl1 _
      simp only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.snoc_last,
        Fin.snoc_castSucc] at hlast hcs
      refine ⟨fun k => l (Sum.inl (Sum.inl k)) / lx, fun t => l (Sum.inl (Sum.inr t)) / lx,
        fun k => div_nonneg (hl0 _) hlxp.le, fun t => div_nonneg (hl0 _) hlxp.le, ?_, ?_⟩
      · rw [← Finset.sum_div, div_eq_one_iff_eq (ne_of_gt hlxp)]
        simp only [Finset.univ_unique, Finset.sum_singleton, mul_neg, mul_one, mul_zero,
          Finset.sum_const_zero, add_zero, Finset.sum_neg_distrib] at hlast
        rw [← hlx] at hlast
        linarith
      · ext j
        have h := hcs j
        simp only [Finset.univ_unique, Finset.sum_singleton, Pi.neg_apply] at h
        rw [← hlx] at h
        simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, castv]
        have e1 : ∑ k, l (Sum.inl (Sum.inl k)) / lx * (W k j : ℚ) =
            (∑ k, l (Sum.inl (Sum.inl k)) * castv (W k) j) / lx := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun k _ => by simp [castv]; ring)
        have e2 : ∑ t, l (Sum.inl (Sum.inr t)) / lx * (R t j : ℚ) =
            (∑ t, l (Sum.inl (Sum.inr t)) * castv (R t) j) / lx := by
          rw [Finset.sum_div]; refine Finset.sum_congr rfl (fun t _ => by simp [castv]; ring)
        rw [e1, e2, ← add_div, eq_div_iff (ne_of_gt hlxp)]
        linarith
  -- Step 2: scale into the box
  set M : ℚ := 1 + ∑ s, |y s| with hM
  have hMp : 0 < M := by
    have : 0 ≤ ∑ s, |y s| := Finset.sum_nonneg (fun s _ => abs_nonneg _)
    linarith
  have hyM : ∀ s, |y s| ≤ M := by
    intro s
    have := Finset.single_le_sum (f := fun s => |y s|) (fun s _ => abs_nonneg _) (Finset.mem_univ s)
    linarith
  set y' := M⁻¹ • y with hy'
  set A := sepA W R with hA
  set bS := sepB (κ := κ) (τ := τ) (n := n) with hbS
  have hrowq : ∀ i, (fun j => (A i j : ℚ)) = Sum.elim (Sum.elim (fun k => Fin.snoc (castv (W k)) (-1))
      (fun t => Fin.snoc (castv (R t)) 0))
      (fun p => if p.2 then Pi.single p.1 1 else -Pi.single p.1 1) i := by
    intro i
    rcases i with (k | t) | ⟨s, b⟩
    · exact cast_snoc (W k) (-1)
    · exact cast_snoc (R t) 0
    · cases b
      · ext j; simp [hA, sepA, Pi.single_apply]; try (split_ifs <;> simp)
      · ext j; simp [hA, sepA, Pi.single_apply]; try (split_ifs <;> simp)
  have hdot : ∀ (v : Fin (n + 1) → ℚ) (i : (κ ⊕ τ) ⊕ Unit), ∑ s, a i s * v s = a i ⬝ᵥ v :=
    fun v i => rfl
  have hfeas : ∀ i, (fun j => (A i j : ℚ)) ⬝ᵥ y' ≤ (bS i : ℚ) := by
    intro i
    rw [hrowq i]
    rcases i with (k | t) | ⟨s, b⟩
    · have h0 : Fin.snoc (castv (W k)) (-1) ⬝ᵥ y ≤ 0 := hy (Sum.inl (Sum.inl k))
      have e : Fin.snoc (castv (W k)) (-1) ⬝ᵥ y' = M⁻¹ * (Fin.snoc (castv (W k)) (-1) ⬝ᵥ y) := by
        simp only [hy', dotProduct_smul, smul_eq_mul]
      have hb0 : (bS (Sum.inl (Sum.inl k)) : ℚ) = 0 := by simp [hbS, sepB]
      show Fin.snoc (castv (W k)) (-1) ⬝ᵥ y' ≤ (bS (Sum.inl (Sum.inl k)) : ℚ)
      rw [e, hb0]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hMp.le) h0
    · have h0 : Fin.snoc (castv (R t)) 0 ⬝ᵥ y ≤ 0 := hy (Sum.inl (Sum.inr t))
      have e : Fin.snoc (castv (R t)) 0 ⬝ᵥ y' = M⁻¹ * (Fin.snoc (castv (R t)) 0 ⬝ᵥ y) := by
        simp only [hy', dotProduct_smul, smul_eq_mul]
      have hb0 : (bS (Sum.inl (Sum.inr t)) : ℚ) = 0 := by simp [hbS, sepB]
      show Fin.snoc (castv (R t)) 0 ⬝ᵥ y' ≤ (bS (Sum.inl (Sum.inr t)) : ℚ)
      rw [e, hb0]
      exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hMp.le) h0
    · have hb1 : (bS (Sum.inr (s, b)) : ℚ) = 1 := by simp [hbS, sepB]
      rw [hb1]
      have habs : |y' s| ≤ 1 := by
        rw [hy', Pi.smul_apply, smul_eq_mul, abs_mul, abs_inv, abs_of_pos hMp]
        rw [inv_mul_le_iff₀ hMp, mul_one]; exact hyM s
      cases b
      · simp only [Sum.elim_inr, Bool.false_eq_true, if_false]
        rw [neg_dotProduct, single_dotProduct, one_mul]
        linarith [neg_abs_le (y' s)]
      · simp only [Sum.elim_inr, if_true]
        rw [single_dotProduct, one_mul]
        linarith [le_abs_self (y' s)]
  -- objective
  let φ : (Fin (n + 1) → ℚ) → ℚ := fun v => (Fin.snoc x (-1) : Fin (n + 1) → ℚ) ⬝ᵥ v
  have hφy : 0 < φ y' := by
    have this : Fin.snoc (-x) 1 ⬝ᵥ y ≤ -1 := hy (Sum.inr ())
    have e : (Fin.snoc (-x) 1 : Fin (n + 1) → ℚ) = -(Fin.snoc x (-1) : Fin (n + 1) → ℚ) := by
      ext j; refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [e, neg_dotProduct] at this
    have e2 : φ y' = M⁻¹ * ((Fin.snoc x (-1) : Fin (n + 1) → ℚ) ⬝ᵥ y) := by
      simp only [φ, hy', dotProduct_smul, smul_eq_mul]
    rw [e2]
    exact mul_pos (inv_pos.2 hMp) (by linarith)
  have hbd : ∀ w : Fin (n + 1) → ℚ, w ≠ 0 → ∃ i, 0 < (fun j => (A i j : ℚ)) ⬝ᵥ w := by
    intro w hw
    obtain ⟨s, hs⟩ : ∃ s, w s ≠ 0 := by
      by_contra h; push_neg at h; exact hw (funext h)
    rcases lt_or_gt_of_ne hs with h | h
    · refine ⟨Sum.inr (s, false), ?_⟩
      rw [hrowq]
      simp only [Sum.elim_inr, Bool.false_eq_true, if_false]
      rw [neg_dotProduct, single_dotProduct, one_mul]
      linarith
    · refine ⟨Sum.inr (s, true), ?_⟩
      rw [hrowq]
      simp only [Sum.elim_inr, if_true]
      rw [single_dotProduct, one_mul]
      exact h
  have hmem := vert_decomp (fun i j => (A i j : ℚ)) (fun i => (bS i : ℚ)) hbd y' hfeas
  obtain ⟨v, hv, hφv⟩ : ∃ v, IsVert (fun i j => (A i j : ℚ)) (fun i => (bS i : ℚ)) v ∧ 0 < φ v := by
    by_contra hcon
    push_neg at hcon
    have hsub : {v | IsVert (fun i j => (A i j : ℚ)) (fun i => (bS i : ℚ)) v} ⊆ {v | φ v ≤ 0} :=
      fun v hv => hcon v hv
    have hcv : Convex ℚ {v : Fin (n + 1) → ℚ | φ v ≤ 0} := by
      intro p hp q hq s t hs ht _
      simp only [Set.mem_setOf_eq, φ, dotProduct_add, dotProduct_smul, smul_eq_mul] at hp hq ⊢
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hs hp, mul_nonpos_of_nonneg_of_nonpos ht hq]
    have := convexHull_min hsub hcv hmem
    simp only [Set.mem_setOf_eq] at this
    linarith
  obtain ⟨r, N, hN, hr, hrb⟩ := vert_int A bS v hv
  refine ⟨fun j => r (Fin.castSucc j), r (Fin.last n), fun j => hrb _, hrb _, ?_, ?_, ?_⟩
  · intro k
    have hb0 : (bS (Sum.inl (Sum.inl k)) : ℚ) = 0 := by simp [hbS, sepB]
    have h1 : (fun j => (A (Sum.inl (Sum.inl k)) j : ℚ)) ⬝ᵥ v ≤ 0 := le_of_le_of_eq (hv.1 _) hb0
    have hz : ((A (Sum.inl (Sum.inl k)) ⬝ᵥ r : ℤ) : ℚ) ≤ 0 := by
      rw [cast_dot, hr, dotProduct_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hN.le h1
    have hz' : A (Sum.inl (Sum.inl k)) ⬝ᵥ r ≤ 0 := by exact_mod_cast hz
    simp only [hA, sepA, Sum.elim_inl] at hz'
    rw [snoc_dot] at hz'
    rw [dotProduct_comm]
    linarith
  · intro t
    have hb0 : (bS (Sum.inl (Sum.inr t)) : ℚ) = 0 := by simp [hbS, sepB]
    have h1 : (fun j => (A (Sum.inl (Sum.inr t)) j : ℚ)) ⬝ᵥ v ≤ 0 := le_of_le_of_eq (hv.1 _) hb0
    have hz : ((A (Sum.inl (Sum.inr t)) ⬝ᵥ r : ℤ) : ℚ) ≤ 0 := by
      rw [cast_dot, hr, dotProduct_smul, smul_eq_mul]
      exact mul_nonpos_of_nonneg_of_nonpos hN.le h1
    have hz' : A (Sum.inl (Sum.inr t)) ⬝ᵥ r ≤ 0 := by exact_mod_cast hz
    simp only [hA, sepA, Sum.elim_inl, Sum.elim_inr] at hz'
    rw [snoc_dot] at hz'
    rw [dotProduct_comm]
    linarith
  · have h2 : 0 < φ (castv r) := by
      have : castv r = N • v := hr
      simp only [φ]
      rw [this, dotProduct_smul, smul_eq_mul]
      exact mul_pos hN hφv
    simp only [φ] at h2
    rw [snoc_dot] at h2
    have e : (fun j => castv r (Fin.castSucc j)) = castv (fun j => r (Fin.castSucc j)) := rfl
    rw [e, dotProduct_comm] at h2
    simp only [castv] at h2 ⊢
    linarith

/-- The paper's hull of an integer set. -/
def hullZ {n : ℕ} (S : Set (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  convexHull ℚ {x | ∃ y ∈ S, x = fun i => (y i : ℚ)}

/-- Separation for a set whose hull is `conv W + cone R`. -/
theorem key_sep {n : ℕ} (S : Set (Fin n → ℤ)) {κ τ : Type} [Fintype κ] [Fintype τ]
    (W : κ → Fin n → ℤ) (R : τ → Fin n → ℤ) (hW : ∀ k, W k ∈ S)
    (hR : ∀ p ∈ hullZ S, ∀ t, ∀ c : ℚ, 0 ≤ c → p + c • castv (R t) ∈ hullZ S)
    (hval : ∀ (f : Fin n → ℤ) (g : ℤ), (∀ k, f ⬝ᵥ W k ≤ g) → (∀ t, f ⬝ᵥ R t ≤ 0) →
      ∀ y ∈ S, f ⬝ᵥ y ≤ g)
    (x : Fin n → ℚ) (hx : x ∉ hullZ S) :
    ∃ (f : Fin n → ℤ) (g : ℤ), (∀ j, |f j| ≤ Bs W R) ∧ |g| ≤ Bs W R ∧
      (∀ y ∈ S, f ⬝ᵥ y ≤ g) ∧ (g : ℚ) < castv f ⬝ᵥ x := by
  classical
  have hx' : ¬ ∃ (α : κ → ℚ) (ν : τ → ℚ), (∀ k, 0 ≤ α k) ∧ (∀ t, 0 ≤ ν t) ∧ ∑ k, α k = 1 ∧
      x = ∑ k, α k • castv (W k) + ∑ t, ν t • castv (R t) := by
    rintro ⟨α, ν, hα, hν, h1, hxe⟩
    apply hx
    have h0 : ∑ k, α k • castv (W k) ∈ hullZ S :=
      (convex_convexHull ℚ _).sum_mem (fun k _ => hα k) h1
        (fun k _ => subset_convexHull ℚ _ ⟨W k, hW k, rfl⟩)
    have hall : ∀ s : Finset τ, ∑ k, α k • castv (W k) + ∑ t ∈ s, ν t • castv (R t) ∈ hullZ S := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using h0
      | insert t s ht ih =>
        rw [Finset.sum_insert ht, add_left_comm]
        rw [add_comm]
        exact hR _ ih t (ν t) (hν t)
    rw [hxe]
    exact hall Finset.univ
  obtain ⟨f, g, hf, hg, hWv, hRv, hlt⟩ := sep W R x hx'
  exact ⟨f, g, hf, hg, hval f g hWv hRv, hlt⟩

lemma Bv_mono (d : ℕ) {X X' : ℤ} (h0 : 0 ≤ X) (h : X ≤ X') : Bv d X ≤ Bv d X' := by
  unfold Bv
  have h0' : 0 ≤ X' := le_trans h0 h
  gcongr

lemma sum_abs_snoc {n : ℕ} (a : Fin n → ℤ) (c : ℤ) :
    ∑ j, |(Fin.snoc a c : Fin (n + 1) → ℤ) j| = ∑ j, |a j| + |c| := by
  simp [Fin.sum_univ_castSucc]

lemma Xb_sep_le {n : ℕ} {κ τ : Type} [Fintype κ] [Fintype τ] (W : κ → Fin n → ℤ)
    (R : τ → Fin n → ℤ) (c : ℤ) (hc : 0 ≤ c) (hWc : ∀ k j, |W k j| ≤ c) (hRc : ∀ t j, |R t j| ≤ c) :
    Xb (sepA W R) (sepB (κ := κ) (τ := τ) (n := n)) ≤
      1 + ((Fintype.card κ + Fintype.card τ + 2 * (n + 1) : ℕ) : ℤ) * ((n + 1) * c + 2) ^ 2 := by
  classical
  unfold Xb
  have hterm : ∀ i, (∑ j, |sepA W R i j| + |sepB (κ := κ) (τ := τ) (n := n) i|) ^ 2 ≤
      ((n + 1) * c + 2) ^ 2 := by
    intro i
    have hnn : 0 ≤ ∑ j, |sepA W R i j| + |sepB (κ := κ) (τ := τ) (n := n) i| :=
      add_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _)) (abs_nonneg _)
    apply pow_le_pow_left₀ hnn
    have hsumc : ∀ a : Fin n → ℤ, (∀ j, |a j| ≤ c) → ∑ j, |a j| ≤ n * c := by
      intro a ha
      have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => ha j)
      simpa using this
    rcases i with (k | t) | ⟨s, b⟩
    · simp only [sepA, sepB, Sum.elim_inl]
      rw [sum_abs_snoc]
      have := hsumc _ (hWc k)
      simp only [abs_neg, abs_one, abs_zero]
      nlinarith
    · simp only [sepA, sepB, Sum.elim_inl, Sum.elim_inr]
      rw [sum_abs_snoc]
      have := hsumc _ (hRc t)
      simp only [abs_zero]
      nlinarith
    · have h1 : ∑ j, |(if b then Pi.single s 1 else -Pi.single s 1 : Fin (n + 1) → ℤ) j| = 1 := by
        cases b <;> simp [Pi.single_apply, apply_ite]
      simp only [sepA, sepB, Sum.elim_inr]
      rw [h1]
      simp only [abs_one]
      nlinarith
  calc 1 + ∑ i, (∑ j, |sepA W R i j| + |sepB (κ := κ) (τ := τ) (n := n) i|) ^ 2
      ≤ 1 + ∑ _i : (κ ⊕ τ) ⊕ (Fin (n + 1) × Bool), ((n + 1) * c + 2) ^ 2 := by
        linarith [Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hterm i)]
    _ = 1 + ((Fintype.card κ + Fintype.card τ + 2 * (n + 1) : ℕ) : ℤ) * ((n + 1) * c + 2) ^ 2 := by
        simp [Finset.card_univ, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
          Fintype.card_bool]
        left; ring

/-- The zero-one bound. -/
def B01 (n : ℕ) : ℤ := Bv (n + 1) (1 + ((2 ^ n + 0 + 2 * (n + 1) : ℕ) : ℤ) * ((n + 1) * 1 + 2) ^ 2)

theorem zeroOne_sep {n : ℕ} (S : Set (Fin n → ℤ)) (h01 : ∀ y ∈ S, ∀ i, y i = 0 ∨ y i = 1)
    (x : Fin n → ℚ) (hx : x ∉ hullZ S) :
    ∃ (f : Fin n → ℤ) (g : ℤ), (∀ j, |f j| ≤ B01 n) ∧ |g| ≤ B01 n ∧
      (∀ y ∈ S, f ⬝ᵥ y ≤ g) ∧ (g : ℚ) < castv f ⬝ᵥ x := by
  classical
  let T : Finset (Fin n → ℤ) := (Fintype.piFinset fun _ => ({0, 1} : Finset ℤ)).filter (· ∈ S)
  have hT : ∀ y, y ∈ T ↔ y ∈ S := by
    intro y
    simp only [T, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_insert,
      Finset.mem_singleton, and_iff_right_iff_imp]
    exact fun hy i => h01 y hy i
  let W : T → Fin n → ℤ := fun w => w.1
  let R : Empty → Fin n → ℤ := fun e => e.elim
  obtain ⟨f, g, hf, hg, hv, hlt⟩ := key_sep S W R (fun k => (hT _).1 k.2)
    (fun p _ t => t.elim)
    (fun f g hW _ y hy => hW ⟨y, (hT y).2 hy⟩) x hx
  have hcard : Fintype.card T ≤ 2 ^ n := by
    rw [Fintype.card_coe]
    calc T.card ≤ (Fintype.piFinset fun _ : Fin n => ({0, 1} : Finset ℤ)).card :=
          Finset.card_filter_le _ _
      _ = 2 ^ n := by simp [Fintype.card_piFinset]
  have hXb := Xb_sep_le W R 1 zero_le_one
    (fun k j => by
      have := (hT _).2 ((hT _).1 k.2)
      rcases h01 _ ((hT _).1 k.2) j with h | h <;> simp [W, h])
    (fun t _ => t.elim)
  have hB : Bs W R ≤ B01 n := by
    unfold Bs B01
    apply Bv_mono _ (le_trans zero_le_one (Xb_pos _ _))
    refine le_trans hXb ?_
    have hc : ((Fintype.card T + Fintype.card Empty + 2 * (n + 1) : ℕ) : ℤ) ≤
        ((2 ^ n + 0 + 2 * (n + 1) : ℕ) : ℤ) := by
      simp only [Fintype.card_empty, add_zero]
      exact_mod_cast (by omega)
    gcongr
  exact ⟨f, g, fun j => le_trans (hf j) hB, le_trans hg hB, hv, hlt⟩

/-- Homogenized rows of `{x ≥ 0, A x ≤ b}`. -/
def homA {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : Fin m ⊕ Fin (n + 1) → Fin (n + 1) → ℤ :=
  Sum.elim (fun i => Fin.snoc (A i) (-b i)) (fun k => -Pi.single k 1)

def ipS {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : Set (Fin n → ℤ) :=
  {x | (∀ j, 0 ≤ x j) ∧ ∀ i, A i ⬝ᵥ x ≤ b i}

lemma homA_dot {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (y : Fin n → ℤ) (c : ℤ) :
    (∀ i, homA A b i ⬝ᵥ (Fin.snoc y c : Fin (n + 1) → ℤ) ≤ 0) ↔
      (∀ i, A i ⬝ᵥ y ≤ b i * c) ∧ (∀ j, 0 ≤ y j) ∧ 0 ≤ c := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun j => ?_, ?_⟩
    · have := h (Sum.inl i)
      simp only [homA, Sum.elim_inl] at this
      rw [snoc_dot] at this
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at this
      have e : (fun j => (Fin.snoc y c : Fin (n + 1) → ℤ) (Fin.castSucc j)) = y := by
        ext j; simp
      try simp only [e] at this
      linarith
    · have := h (Sum.inr (Fin.castSucc j))
      simp only [homA, Sum.elim_inr, neg_dotProduct, single_dotProduct, one_mul,
        Fin.snoc_castSucc] at this
      linarith
    · have := h (Sum.inr (Fin.last n))
      simp only [homA, Sum.elim_inr, neg_dotProduct, single_dotProduct, one_mul,
        Fin.snoc_last] at this
      linarith
  · rintro ⟨h1, h2, h3⟩ i
    rcases i with i | k
    · simp only [homA, Sum.elim_inl]
      rw [snoc_dot]
      have e : (fun j => (Fin.snoc y c : Fin (n + 1) → ℤ) (Fin.castSucc j)) = y := by
        ext j; simp
      rw [e]
      simp only [Fin.snoc_last]
      linarith [h1 i]
    · simp only [homA, Sum.elim_inr, neg_dotProduct, single_dotProduct, one_mul]
      refine Fin.lastCases ?_ (fun j => ?_) k
      · simp only [Fin.snoc_last]; linarith
      · simp only [Fin.snoc_castSucc]; linarith [h2 j]

lemma homA_pointed {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) :
    ∀ u : Fin (n + 1) → ℚ, (∀ i, (fun j => (homA A b i j : ℚ)) ⬝ᵥ u = 0) → u = 0 := by
  intro u hu
  ext k
  have := hu (Sum.inr k)
  have e : (fun j => (homA A b (Sum.inr k) j : ℚ)) = -Pi.single k 1 := by
    ext j; simp [homA, Pi.single_apply, apply_ite]
  rw [e, neg_dotProduct, single_dotProduct, one_mul] at this
  simpa using this

/-- Recession: integer recession directions keep the hull. -/
lemma hull_recession {n : ℕ} (S : Set (Fin n → ℤ)) (r : Fin n → ℤ)
    (hS : ∀ s ∈ S, ∀ K : ℕ, s + K • r ∈ S) :
    ∀ p ∈ hullZ S, ∀ c : ℚ, 0 ≤ c → p + c • castv r ∈ hullZ S := by
  have hsub : {x | ∃ y ∈ S, x = fun i => (y i : ℚ)} ⊆
      {p | ∀ c : ℚ, 0 ≤ c → p + c • castv r ∈ hullZ S} := by
    rintro _ ⟨s, hs, rfl⟩ c hc
    set K := ⌈c⌉₊ with hK
    rcases Nat.eq_zero_or_pos K with h0 | hpos
    · have : c = 0 := by
        have := Nat.le_ceil c
        rw [← hK, h0] at this
        push_cast at this
        linarith
      subst this
      simp only [zero_smul, add_zero]
      exact subset_convexHull ℚ _ ⟨s, hs, rfl⟩
    · have hKq : (0 : ℚ) < K := by exact_mod_cast hpos
      have hcK : c ≤ K := Nat.le_ceil c
      have h1 : (fun i => (s i : ℚ)) ∈ hullZ S := subset_convexHull ℚ _ ⟨s, hs, rfl⟩
      have h2 : (fun i => ((s + K • r) i : ℚ)) ∈ hullZ S :=
        subset_convexHull ℚ _ ⟨s + K • r, hS s hs K, rfl⟩
      have e : (fun i => (s i : ℚ)) + c • castv r =
          (1 - c / K) • (fun i => (s i : ℚ)) + (c / K) • (fun i => ((s + K • r) i : ℚ)) := by
        ext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, castv, nsmul_eq_mul, Int.cast_add,
          Int.cast_mul, Int.cast_natCast, Pi.mul_apply, Pi.natCast_apply]
        field_simp
        ring
      rw [e]
      exact convex_convexHull ℚ _ h1 h2 (by rw [sub_nonneg, div_le_one hKq]; exact hcK)
        (div_nonneg hc hKq.le) (by ring)
  have hconv : Convex ℚ {p : Fin n → ℚ | ∀ c : ℚ, 0 ≤ c → p + c • castv r ∈ hullZ S} := by
    intro p hp q hq a bb ha hb hab c hc
    have e : a • p + bb • q + c • castv r = a • (p + c • castv r) + bb • (q + c • castv r) := by
      rw [smul_add, smul_add, smul_smul, smul_smul]
      have : a * c + bb * c = c := by rw [← add_mul, hab, one_mul]
      ext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      linear_combination (castv r i) * this.symm
    rw [e]
    exact convex_convexHull ℚ _ (hp c hc) (hq c hc) ha hb hab
  intro p hp
  exact convexHull_min hsub hconv hp

def ipB1 {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : ℤ := Bc (homA A b)

noncomputable def ipG {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : Finset (Fin (n + 1) → ℤ) :=
  gens (homA A b) (ipB1 A b)

noncomputable def ipB2 {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : ℤ :=
  (ipG A b).card * ipB1 A b

noncomputable def ipWset {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : Finset (Fin n → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ => Finset.Icc (-ipB2 A b) (ipB2 A b)).filter (· ∈ ipS A b)

noncomputable def ipRset {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) :
    Finset (Fin (n + 1) → ℤ) := by
  classical
  exact (ipG A b).filter (fun r => r (Fin.last n) = 0)

def ipW {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : ipWset A b → Fin n → ℤ := fun k => k.1

def ipR {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : ipRset A b → Fin n → ℤ :=
  fun t => Fin.init t.1

lemma mem_ipG {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (r : Fin (n + 1) → ℤ)
    (hr : r ∈ ipG A b) :
    (∀ j, |r j| ≤ ipB1 A b) ∧ (∀ i, A i ⬝ᵥ Fin.init r ≤ b i * r (Fin.last n)) ∧
      (∀ j, 0 ≤ Fin.init r j) ∧ 0 ≤ r (Fin.last n) := by
  have h := (mem_gens _ _ r).1 hr
  have e : (Fin.snoc (Fin.init r) (r (Fin.last n)) : Fin (n + 1) → ℤ) = r := Fin.snoc_init_self r
  have h2 := h.2
  rw [← e] at h2
  have := (homA_dot A b (Fin.init r) (r (Fin.last n))).1 h2
  exact ⟨h.1, this.1, this.2.1, this.2.2⟩

theorem ip_sep {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (x : Fin n → ℚ)
    (hx : x ∉ hullZ (ipS A b)) :
    ∃ (f : Fin n → ℤ) (g : ℤ), (∀ j, |f j| ≤ Bs (ipW A b) (ipR A b)) ∧
      |g| ≤ Bs (ipW A b) (ipR A b) ∧
      (∀ y ∈ ipS A b, f ⬝ᵥ y ≤ g) ∧ (g : ℚ) < castv f ⬝ᵥ x := by
  classical
  refine key_sep (ipS A b) (ipW A b) (ipR A b) ?_ ?_ ?_ x hx
  · intro k
    have := k.2
    simp only [ipWset, Finset.mem_filter] at this
    exact this.2
  · intro p hp t
    have ht := t.2
    simp only [ipRset, Finset.mem_filter] at ht
    obtain ⟨-, hA, hnn, -⟩ := mem_ipG A b t.1 ht.1
    apply hull_recession (ipS A b) (ipR A b t) _ p hp
    intro s hs K
    refine ⟨fun j => ?_, fun i => ?_⟩
    · simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
      have h1 := hs.1 j
      have h2 := hnn j
      simp only [ipR]
      exact add_nonneg h1 (mul_nonneg (Nat.cast_nonneg K) h2)
    · rw [dotProduct_add, dotProduct_smul]
      have h1 := hs.2 i
      have h2 := hA i
      rw [ht.2, mul_zero] at h2
      simp only [ipR, nsmul_eq_mul]
      nlinarith
  · intro f g hWv hRv y hy
    set Ah := homA A b with hAh
    set G := ipG A b with hG
    have hsn : (fun j => ((Fin.snoc y (1 : ℤ) : Fin (n + 1) → ℤ) j : ℚ)) =
        (Fin.snoc (castv y) 1 : Fin (n + 1) → ℚ) := by
      rw [cast_snoc]; simp
    have hu : ∀ i, (fun j => (Ah i j : ℚ)) ⬝ᵥ (Fin.snoc (castv y) 1 : Fin (n + 1) → ℚ) ≤ 0 := by
      intro i
      have hz : Ah i ⬝ᵥ (Fin.snoc y 1 : Fin (n + 1) → ℤ) ≤ 0 :=
        (homA_dot A b y 1).2 ⟨fun i => by simpa using hy.2 i, hy.1, zero_le_one⟩ i
      have := cast_dot (Ah i) (Fin.snoc y 1)
      rw [hsn] at this
      rw [← this]
      exact_mod_cast hz
    obtain ⟨μ, hμ, hrep⟩ : InCone G (Fin.snoc (castv y) 1 : Fin (n + 1) → ℚ) :=
      cone_gen Ah (homA_pointed A b) _ hu
    have hcoord : ∀ j, (y j : ℚ) = ∑ r ∈ G, μ r * (r (Fin.castSucc j) : ℚ) := by
      intro j
      have := congrFun hrep (Fin.castSucc j)
      simpa [Finset.sum_apply, castv] using this
    have hlast : (1 : ℚ) = ∑ r ∈ G, μ r * (r (Fin.last n) : ℚ) := by
      have := congrFun hrep (Fin.last n)
      simpa [Finset.sum_apply] using this
    let fl : (Fin (n + 1) → ℤ) → ℤ := fun r => if r (Fin.last n) = 0 then ⌊μ r⌋ else 0
    have hfl : ∀ r ∈ G, 0 ≤ fl r := by
      intro r hr
      simp only [fl]
      split_ifs
      · exact Int.floor_nonneg.2 (hμ r hr)
      · exact le_rfl
    let μ' : (Fin (n + 1) → ℤ) → ℚ := fun r => μ r - fl r
    have hflz : ∀ r, (fl r : ℚ) * (r (Fin.last n) : ℚ) = 0 := by
      intro r
      simp only [fl]
      split_ifs with h
      · rw [h]; simp
      · simp
    have hμ'nn : ∀ r ∈ G, 0 ≤ μ' r := by
      intro r hr
      simp only [μ', fl]
      split_ifs
      · linarith [Int.floor_le (μ r)]
      · simp only [Int.cast_zero, sub_zero]; exact hμ r hr
    have hlast' : (1 : ℚ) = ∑ r ∈ G, μ' r * (r (Fin.last n) : ℚ) := by
      rw [hlast]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [μ']
      rw [sub_mul, hflz, sub_zero]
    have hμ'le : ∀ r ∈ G, μ' r ≤ 1 := by
      intro r hr
      by_cases h0 : r (Fin.last n) = 0
      · simp only [μ', fl, h0, if_true]
        linarith [Int.lt_floor_add_one (μ r)]
      · have hl := (mem_ipG A b r hr).2.2.2
        have hl1 : (1 : ℚ) ≤ r (Fin.last n) := by
          have : 1 ≤ r (Fin.last n) := by omega
          exact_mod_cast this
        have hle : μ' r * (r (Fin.last n) : ℚ) ≤ 1 := by
          rw [hlast']
          exact Finset.single_le_sum (f := fun r => μ' r * (r (Fin.last n) : ℚ))
            (fun r hr => mul_nonneg (hμ'nn r hr) (by exact_mod_cast (mem_ipG A b r hr).2.2.2)) hr
        have := hμ'nn r hr
        nlinarith
    let y' : Fin n → ℤ := y - ∑ r ∈ G, fl r • Fin.init r
    have hy'c : ∀ j, (y' j : ℚ) = ∑ r ∈ G, μ' r * (r (Fin.castSucc j) : ℚ) := by
      intro j
      simp only [y', Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub,
        Int.cast_sum, Int.cast_mul, Fin.init]
      rw [hcoord j, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun r _ => ?_)
      simp only [μ']
      ring
    have hy'nn : ∀ j, 0 ≤ y' j := by
      intro j
      have : (0 : ℚ) ≤ y' j := by
        rw [hy'c j]
        exact Finset.sum_nonneg (fun r hr => mul_nonneg (hμ'nn r hr)
          (by exact_mod_cast (mem_ipG A b r hr).2.2.1 j))
      exact_mod_cast this
    have hy'A : ∀ i, A i ⬝ᵥ y' ≤ b i := by
      intro i
      have : ((A i ⬝ᵥ y' : ℤ) : ℚ) ≤ (b i : ℚ) := by
        have e1 : ((A i ⬝ᵥ y' : ℤ) : ℚ) =
            ∑ r ∈ G, μ' r * ((A i ⬝ᵥ Fin.init r : ℤ) : ℚ) := by
          simp only [dotProduct, Int.cast_sum, Int.cast_mul]
          simp_rw [hy'c, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => ?_))
          simp only [Fin.init]
          ring
        have e2 : (b i : ℚ) = ∑ r ∈ G, μ' r * ((b i * r (Fin.last n) : ℤ) : ℚ) := by
          rw [← mul_one (b i : ℚ), hlast', Finset.mul_sum]
          refine Finset.sum_congr rfl (fun r _ => ?_)
          push_cast
          ring
        rw [e1, e2]
        refine Finset.sum_le_sum (fun r hr => ?_)
        apply mul_le_mul_of_nonneg_left _ (hμ'nn r hr)
        exact_mod_cast (mem_ipG A b r hr).2.1 i
      exact_mod_cast this
    have hy'b : ∀ j, |y' j| ≤ ipB2 A b := by
      intro j
      have : |(y' j : ℚ)| ≤ (ipB2 A b : ℚ) := by
        rw [hy'c j]
        calc |∑ r ∈ G, μ' r * (r (Fin.castSucc j) : ℚ)|
            ≤ ∑ r ∈ G, |μ' r * (r (Fin.castSucc j) : ℚ)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _r ∈ G, (ipB1 A b : ℚ) := by
            refine Finset.sum_le_sum (fun r hr => ?_)
            rw [abs_mul, abs_of_nonneg (hμ'nn r hr)]
            have h1 : |(r (Fin.castSucc j) : ℚ)| ≤ ipB1 A b := by
              exact_mod_cast (mem_ipG A b r hr).1 _
            have h2 := hμ'le r hr
            have h3 := hμ'nn r hr
            have h4 : 0 ≤ |(r (Fin.castSucc j) : ℚ)| := abs_nonneg _
            nlinarith
          _ = (ipB2 A b : ℚ) := by simp [ipB2, hG]
      rw [← Int.cast_abs] at this
      exact_mod_cast this
    have hy'W : y' ∈ ipWset A b := by
      simp only [ipWset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
      exact ⟨fun j => abs_le.1 (hy'b j), hy'nn, hy'A⟩
    have h1 : f ⬝ᵥ y' ≤ g := hWv ⟨y', hy'W⟩
    have hyd : y = y' + ∑ r ∈ G, fl r • Fin.init r := by simp [y']
    have h2 : f ⬝ᵥ (∑ r ∈ G, fl r • Fin.init r) ≤ 0 := by
      have e : f ⬝ᵥ (∑ r ∈ G, fl r • Fin.init r) = ∑ r ∈ G, fl r * (f ⬝ᵥ Fin.init r) := by
        simp only [dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun j _ => by ring))
      rw [e]
      refine Finset.sum_nonpos (fun r hr => ?_)
      by_cases h0 : r (Fin.last n) = 0
      · have hrR : r ∈ ipRset A b := by
          simp only [ipRset, Finset.mem_filter]; exact ⟨hr, h0⟩
        have := hRv ⟨r, hrR⟩
        exact mul_nonpos_of_nonneg_of_nonpos (hfl r hr) this
      · simp [fl, h0]
    rw [hyd, dotProduct_add]
    linarith

end KPSF

namespace KPSF

open Matrix KarpPapadimitriou.SmallFacial

/-! ## Explicit bound arithmetic -/

lemma tp_mono {p q : ℕ} (h : p ≤ q) : (2:ℤ) ^ p ≤ 2 ^ q :=
  pow_le_pow_right₀ (by norm_num) h

lemma one_le_tp (p : ℕ) : (1:ℤ) ≤ 2 ^ p := one_le_pow₀ (by norm_num)

lemma tp_mul {a b : ℤ} {p q : ℕ} (ha0 : 0 ≤ a) (ha : a ≤ 2 ^ p) (hb0 : 0 ≤ b) (hb : b ≤ 2 ^ q) :
    a * b ≤ 2 ^ (p + q) := by
  rw [pow_add]; exact mul_le_mul ha hb hb0 (by positivity)

lemma tp_add {a b : ℤ} {p q : ℕ} (ha : a ≤ 2 ^ p) (hb : b ≤ 2 ^ q) : a + b ≤ 2 ^ (p + q + 1) := by
  have h1 : (2:ℤ) ^ p ≤ 2 ^ (p + q) := tp_mono (by omega)
  have h2 : (2:ℤ) ^ q ≤ 2 ^ (p + q) := tp_mono (by omega)
  rw [pow_succ]; linarith

lemma tp_pow {a : ℤ} {p : ℕ} (m : ℕ) (ha0 : 0 ≤ a) (ha : a ≤ 2 ^ p) : a ^ m ≤ 2 ^ (p * m) := by
  rw [pow_mul]; exact pow_le_pow_left₀ ha0 ha m

lemma tp_add1 {a : ℤ} {p : ℕ} (ha : a ≤ 2 ^ p) : a + 1 ≤ 2 ^ (p + 1) := by
  rw [pow_succ]; linarith [one_le_tp p]

lemma tp_add2 {a : ℤ} {p : ℕ} (ha : a ≤ 2 ^ p) : a + 2 ≤ 2 ^ (p + 2) := by
  have : (2:ℤ) ^ (p + 2) = 2 ^ p * 4 := by rw [pow_add]; norm_num
  rw [this]; linarith [one_le_tp p]

lemma tp_lin {a : ℤ} {p : ℕ} (ha0 : 0 ≤ a) (ha : a ≤ 2 ^ p) : 2 * a + 1 ≤ 2 ^ (p + 2) := by
  have : (2:ℤ) ^ (p + 2) = 2 ^ p * 4 := by rw [pow_add]; norm_num
  rw [this]; linarith [one_le_tp p]

lemma nat_le_tp (n : ℕ) : (n : ℤ) ≤ 2 ^ n := by
  have : n < 2 ^ n := Nat.lt_two_pow_self
  exact_mod_cast this.le

lemma succ_le_tp (n : ℕ) : (n : ℤ) + 1 ≤ 2 ^ n := by
  have : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  exact_mod_cast this

lemma fact_le_tp (d : ℕ) : ((Nat.factorial d : ℕ) : ℤ) ≤ 2 ^ (d * d) := by
  have h1 : Nat.factorial d ≤ d ^ d := Nat.factorial_le_pow d
  have h2 : d ^ d ≤ (2 ^ d) ^ d := Nat.pow_le_pow_left (Nat.lt_two_pow_self (n := d)).le d
  have h3 : Nat.factorial d ≤ 2 ^ (d * d) := by rw [pow_mul]; omega
  exact_mod_cast h3

lemma Bv_nonneg (d : ℕ) {X : ℤ} (h0 : 0 ≤ X) : 0 ≤ Bv d X := by unfold Bv; positivity

lemma Bv_le (d Q c e : ℕ) (hd : d ≤ Q) (hQ : 1 ≤ Q) (he : 1 ≤ e) {X : ℤ} (h0 : 0 ≤ X)
    (hX : X ≤ 2 ^ (c * Q ^ e)) : Bv d X ≤ 2 ^ ((3 + 3 * c) * Q ^ (e + 1)) := by
  unfold Bv
  have hf := fact_le_tp d
  have hXd : X ^ d ≤ 2 ^ (c * Q ^ e * d) := tp_pow d h0 hX
  have hdd : (d : ℤ) ≤ 2 ^ d := nat_le_tp d
  have hf0 : (0:ℤ) ≤ (Nat.factorial d : ℤ) := by positivity
  have hXd0 : 0 ≤ X ^ d := pow_nonneg h0 d
  have h1 : (Nat.factorial d : ℤ) * X ^ d ≤ 2 ^ (d * d + c * Q ^ e * d) := tp_mul hf0 hf hXd0 hXd
  have h10 : 0 ≤ (Nat.factorial d : ℤ) * X ^ d := mul_nonneg hf0 hXd0
  have h2 : (Nat.factorial d : ℤ) * X ^ d * X ≤ 2 ^ (d * d + c * Q ^ e * d + c * Q ^ e) :=
    tp_mul h10 h1 h0 hX
  have h3 : (d : ℤ) * ((Nat.factorial d : ℤ) * X ^ d * X) ≤
      2 ^ (d + (d * d + c * Q ^ e * d + c * Q ^ e)) :=
    tp_mul (by positivity) hdd (mul_nonneg h10 h0) h2
  have h4 := tp_mul h10 h1 (mul_nonneg (by positivity) (mul_nonneg h10 h0)) h3
  refine le_trans h4 (tp_mono ?_)
  have hP2 : Q ^ 2 ≤ Q ^ (e + 1) := Nat.pow_le_pow_right hQ (by omega)
  have hP1 : Q ≤ Q ^ (e + 1) := by
    calc Q = Q ^ 1 := (pow_one Q).symm
      _ ≤ Q ^ (e + 1) := Nat.pow_le_pow_right hQ (by omega)
  have hdd' : d * d ≤ Q ^ (e + 1) :=
    le_trans (Nat.mul_le_mul hd hd) (by rw [← pow_two]; exact hP2)
  have hc1 : c * Q ^ e * d ≤ c * Q ^ (e + 1) := by
    calc c * Q ^ e * d ≤ c * Q ^ e * Q := Nat.mul_le_mul le_rfl hd
      _ = c * Q ^ (e + 1) := by rw [pow_succ, mul_assoc]
  have hc2 : c * Q ^ e ≤ c * Q ^ (e + 1) :=
    Nat.mul_le_mul le_rfl (Nat.pow_le_pow_right hQ (by omega))
  have hd' : d ≤ Q ^ (e + 1) := le_trans hd hP1
  have : (3 + 3 * c) * Q ^ (e + 1) = 3 * Q ^ (e + 1) + 3 * (c * Q ^ (e + 1)) := by ring
  rw [this]
  linarith

lemma Xb_slice_le {ι : Type} [Fintype ι] {d : ℕ} (H : ι → Fin d → ℤ) :
    Xb (sliceA H) (sliceB (ι := ι)) ≤ 4 * (∑ i, ∑ j, |H i j| + 1) ^ 2 := by
  classical
  have hr0 : ∀ i, 0 ≤ ∑ j, |H i j| := fun i => Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hM0 : 0 ≤ ∑ i, ∑ j, |H i j| := Finset.sum_nonneg (fun i _ => hr0 i)
  have hcol : ∑ j, |(∑ i, H i) j| ≤ ∑ i, ∑ j, |H i j| := by
    rw [Finset.sum_comm]
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Finset.sum_apply]
    exact Finset.abs_sum_le_sum_abs _ _
  have hcol' : ∑ j, |(-∑ i, H i) j| ≤ ∑ i, ∑ j, |H i j| := by
    simpa only [Pi.neg_apply, abs_neg] using hcol
  have hsq : ∑ i, (∑ j, |H i j|) ^ 2 ≤ (∑ i, ∑ j, |H i j|) ^ 2 :=
    Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => hr0 i)
  have e1 : (∑ j, |(-∑ i, H i) j| + 1) ^ 2 ≤ (∑ i, ∑ j, |H i j| + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have e2 : (∑ j, |(∑ i, H i) j| + 1) ^ 2 ≤ (∑ i, ∑ j, |H i j| + 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  unfold Xb
  calc 1 + ∑ x, (∑ j, |sliceA H x j| + |sliceB (ι := ι) x|) ^ 2
      = 1 + (∑ i, (∑ j, |H i j|) ^ 2 +
          ((∑ j, |(-∑ i, H i) j| + 1) ^ 2 + (∑ j, |(∑ i, H i) j| + 1) ^ 2)) := by
        rw [Fintype.sum_sum_type, Fintype.sum_bool]
        simp [sliceA, sliceB]
    _ ≤ 4 * (∑ i, ∑ j, |H i j| + 1) ^ 2 := by nlinarith

lemma homA_abs_sum {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) :
    ∑ i, ∑ j, |homA A b i j| = ∑ i, (∑ j, |A i j| + |b i|) + ((n : ℤ) + 1) := by
  rw [Fintype.sum_sum_type]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [homA, Sum.elim_inl]
    rw [sum_abs_snoc, abs_neg]
  · simp only [homA, Sum.elim_inr]
    have : ∀ k : Fin (n + 1), ∑ j, |(-Pi.single k (1:ℤ) : Fin (n + 1) → ℤ) j| = 1 := by
      intro k; simp [Pi.single_apply, apply_ite]
    rw [Finset.sum_congr rfl (fun k _ => this k)]
    simp

lemma one_add_sum_le {ι : Type} (s : Finset ι) (x : ι → ℤ) (e : ι → ℕ) (h0 : ∀ i, 0 ≤ x i)
    (h : ∀ i, 1 + x i ≤ 2 ^ e i) : 1 + ∑ i ∈ s, x i ≤ 2 ^ (∑ i ∈ s, e i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, pow_add]
    have hs0 : 0 ≤ ∑ i ∈ s, x i := Finset.sum_nonneg (fun i _ => h0 i)
    have := mul_le_mul (h a) ih (by linarith) (by positivity)
    nlinarith [h0 a]

lemma entry_le (a : ℤ) : 1 + |a| ≤ 2 ^ (entrySize a) := by
  unfold entrySize
  have := Nat.le_pow_clog (by norm_num : 1 < 2) (1 + a.natAbs)
  have h2 : ((1 + a.natAbs : ℕ) : ℤ) ≤ ((2 ^ Nat.clog 2 (1 + a.natAbs) : ℕ) : ℤ) := by
    exact_mod_cast this
  push_cast at h2
  simpa [Int.natCast_natAbs] using h2

lemma input_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) :
    1 + ∑ i, (∑ j, |A i j| + |b i|) ≤ 2 ^ (inputSize (m := m) (n := n) A b) := by
  unfold inputSize
  have hA : 1 + ∑ i, ∑ j, |A i j| ≤ 2 ^ (∑ i, ∑ j, entrySize (A i j)) :=
    one_add_sum_le _ _ _ (fun i => Finset.sum_nonneg (fun j _ => abs_nonneg _))
      (fun i => one_add_sum_le _ _ _ (fun j => abs_nonneg _) (fun j => entry_le _))
  have hb : 1 + ∑ i, |b i| ≤ 2 ^ (∑ i, entrySize (b i)) :=
    one_add_sum_le _ _ _ (fun i => abs_nonneg _) (fun i => entry_le _)
  rw [Finset.sum_add_distrib, pow_add]
  have h1 : 0 ≤ ∑ i, ∑ j, |A i j| :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _))
  have h2 : 0 ≤ ∑ i, |b i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  nlinarith [mul_le_mul hA hb (by linarith) (by positivity)]

lemma homX_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (len : ℕ)
    (hs : inputSize (m := m) (n := n) A b ≤ len) :
    Xb (sliceA (homA A b)) (sliceB (ι := Fin m ⊕ Fin (n + 1))) ≤ 2 ^ (4 * (len + n + 1) ^ 1) := by
  have h1 := Xb_slice_le (homA A b)
  rw [homA_abs_sum] at h1
  have h2 := input_le A b
  have h3 : (2:ℤ) ^ (inputSize (m := m) (n := n) A b) ≤ 2 ^ len := tp_mono hs
  have h4 := succ_le_tp n
  have h5 : ∑ i, (∑ j, |A i j| + |b i|) + ((n : ℤ) + 1) + 1 ≤ 2 ^ (len + n + 1) := by
    have := tp_add (p := len) (q := n) (a := 1 + ∑ i, (∑ j, |A i j| + |b i|)) (b := (n : ℤ) + 1)
      (by linarith) h4
    linarith
  have h0 : 0 ≤ ∑ i, (∑ j, |A i j| + |b i|) + ((n : ℤ) + 1) + 1 := by positivity
  calc _ ≤ 4 * (∑ i, (∑ j, |A i j| + |b i|) + ((n : ℤ) + 1) + 1) ^ 2 := h1
    _ ≤ 2 ^ 2 * (2 ^ (len + n + 1)) ^ 2 := by gcongr; norm_num
    _ = 2 ^ (2 + 2 * (len + n + 1)) := by rw [← pow_mul, ← pow_add, mul_comm (len + n + 1) 2]
    _ ≤ 2 ^ (4 * (len + n + 1) ^ 1) := tp_mono (by rw [pow_one]; omega)

lemma ipB1_nonneg {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : 0 ≤ ipB1 A b :=
  Bv_nonneg _ (by linarith [Xb_pos (sliceA (homA A b)) (sliceB (ι := Fin m ⊕ Fin (n + 1)))])

lemma ipB1_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (len : ℕ)
    (hs : inputSize (m := m) (n := n) A b ≤ len) :
    ipB1 A b ≤ 2 ^ (15 * (len + n + 1) ^ 2) := by
  have := Bv_le (n + 1) (len + n + 1) 4 1 (by omega) (by omega) le_rfl
    (by linarith [Xb_pos (sliceA (homA A b)) (sliceB (ι := Fin m ⊕ Fin (n + 1)))])
    (homX_le A b len hs)
  have e : (3 + 3 * 4) * (len + n + 1) ^ (1 + 1) = 15 * (len + n + 1) ^ 2 := by norm_num
  rw [e] at this
  exact this

lemma card_box_le {k : ℕ} (B : ℤ) (hB : 0 ≤ B) (s : Finset (Fin k → ℤ))
    (hs : ∀ r ∈ s, ∀ j, |r j| ≤ B) : (s.card : ℤ) ≤ (2 * B + 1) ^ k := by
  have hsub : s ⊆ Fintype.piFinset fun _ : Fin k => Finset.Icc (-B) B := by
    intro r hr
    simp only [Fintype.mem_piFinset, Finset.mem_Icc]
    exact fun j => abs_le.1 (hs r hr j)
  have h := Finset.card_le_card hsub
  rw [Fintype.card_piFinset] at h
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have e : ((B + 1 - -B).toNat : ℤ) = 2 * B + 1 := by
    rw [Int.toNat_of_nonneg (by linarith)]; ring
  calc (s.card : ℤ) ≤ (((B + 1 - -B).toNat ^ k : ℕ) : ℤ) := by exact_mod_cast h
    _ = (2 * B + 1) ^ k := by rw [Nat.cast_pow, e]

lemma ipG_card_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (len : ℕ)
    (hs : inputSize (m := m) (n := n) A b ≤ len) :
    ((ipG A b).card : ℤ) ≤ 2 ^ (17 * (len + n + 1) ^ 3) := by
  have hQ : 1 ≤ len + n + 1 := by omega
  have hB := ipB1_le A b len hs
  have h0 := ipB1_nonneg A b
  have hc := card_box_le (k := n + 1) (ipB1 A b) h0 (ipG A b) (fun r hr => (mem_ipG A b r hr).1)
  have hp := tp_pow (n + 1) (by linarith) (tp_lin h0 hB)
  refine le_trans hc (le_trans hp (tp_mono ?_))
  have hn : n + 1 ≤ len + n + 1 := by omega
  have hQ2 : 1 ≤ (len + n + 1) ^ 2 := Nat.one_le_pow _ _ hQ
  calc (15 * (len + n + 1) ^ 2 + 2) * (n + 1) ≤ (17 * (len + n + 1) ^ 2) * (len + n + 1) :=
        Nat.mul_le_mul (by linarith) hn
    _ = 17 * (len + n + 1) ^ 3 := by ring

lemma ipB2_nonneg {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) : 0 ≤ ipB2 A b :=
  mul_nonneg (Nat.cast_nonneg _) (ipB1_nonneg A b)

lemma ipB2_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (len : ℕ)
    (hs : inputSize (m := m) (n := n) A b ≤ len) :
    ipB2 A b ≤ 2 ^ (32 * (len + n + 1) ^ 3) := by
  have hQ : 1 ≤ len + n + 1 := by omega
  have h := tp_mul (Nat.cast_nonneg _) (ipG_card_le A b len hs) (ipB1_nonneg A b)
    (ipB1_le A b len hs)
  show ((ipG A b).card : ℤ) * ipB1 A b ≤ _
  refine le_trans h (tp_mono ?_)
  have : (len + n + 1) ^ 2 ≤ (len + n + 1) ^ 3 := Nat.pow_le_pow_right hQ (by norm_num)
  linarith

lemma ipWset_mem {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (w : Fin n → ℤ)
    (hw : w ∈ ipWset A b) (j : Fin n) : |w j| ≤ ipB2 A b := by
  simp only [ipWset, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Icc] at hw
  exact abs_le.2 (hw.1 j)

lemma ipWset_card_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (len : ℕ)
    (hs : inputSize (m := m) (n := n) A b ≤ len) :
    ((ipWset A b).card : ℤ) ≤ 2 ^ (34 * (len + n + 1) ^ 4) := by
  have hQ : 1 ≤ len + n + 1 := by omega
  have hB := ipB2_le A b len hs
  have h0 := ipB2_nonneg A b
  have hc := card_box_le (k := n) (ipB2 A b) h0 (ipWset A b) (fun w hw j => ipWset_mem A b w hw j)
  have hp := tp_pow n (by linarith) (tp_lin h0 hB)
  refine le_trans hc (le_trans hp (tp_mono ?_))
  have hn : n ≤ len + n + 1 := by omega
  have h3 : 1 ≤ (len + n + 1) ^ 3 := Nat.one_le_pow _ _ hQ
  calc (32 * (len + n + 1) ^ 3 + 2) * n ≤ (34 * (len + n + 1) ^ 3) * (len + n + 1) :=
        Nat.mul_le_mul (by linarith) hn
    _ = 34 * (len + n + 1) ^ 4 := by ring

lemma ipRset_card_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (len : ℕ)
    (hs : inputSize (m := m) (n := n) A b ≤ len) :
    ((ipRset A b).card : ℤ) ≤ 2 ^ (34 * (len + n + 1) ^ 4) := by
  have hQ : 1 ≤ len + n + 1 := by omega
  have h1 : (ipRset A b).card ≤ (ipG A b).card := by
    classical
    unfold ipRset
    exact Finset.card_filter_le _ _
  have h2 : ((ipRset A b).card : ℤ) ≤ (ipG A b).card := by exact_mod_cast h1
  refine le_trans h2 (le_trans (ipG_card_le A b len hs) (tp_mono ?_))
  have : (len + n + 1) ^ 3 ≤ (len + n + 1) ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
  linarith [Nat.zero_le ((len + n + 1) ^ 3)]

lemma sepX_arith (Q : ℕ) (hQ : 1 ≤ Q) (cW cR n1 B2 : ℤ) (hcW : cW ≤ 2 ^ (34 * Q ^ 4))
    (hcR : cR ≤ 2 ^ (34 * Q ^ 4)) (hn : n1 ≤ 2 ^ Q) (hn0 : 0 ≤ n1)
    (hn2 : 2 * n1 ≤ 2 ^ (34 * Q ^ 4)) (hB : B2 ≤ 2 ^ (32 * Q ^ 3)) (hB0 : 0 ≤ B2)
    (hc0 : 0 ≤ cW) (hr0 : 0 ≤ cR) :
    1 + (cW + cR + 2 * n1) * (n1 * B2 + 2) ^ 2 ≤ 2 ^ (110 * Q ^ 4) := by
  have e4 : (2:ℤ) ^ (34 * Q ^ 4 + 2) = 2 ^ (34 * Q ^ 4) * 4 := by rw [pow_add]; norm_num
  have hS : cW + cR + 2 * n1 ≤ 2 ^ (34 * Q ^ 4 + 2) := by
    rw [e4]; linarith [one_le_tp (34 * Q ^ 4)]
  have hT : n1 * B2 + 2 ≤ 2 ^ (Q + 32 * Q ^ 3 + 2) := tp_add2 (tp_mul hn0 hn hB0 hB)
  have hT2 := tp_pow 2 (by positivity) hT
  have hP := tp_mul (by positivity) hS (by positivity) hT2
  have hP1 := tp_add1 hP
  calc 1 + (cW + cR + 2 * n1) * (n1 * B2 + 2) ^ 2
      = (cW + cR + 2 * n1) * (n1 * B2 + 2) ^ 2 + 1 := by ring
    _ ≤ _ := hP1
    _ ≤ 2 ^ (110 * Q ^ 4) := by
        refine tp_mono ?_
        have h1 : Q ≤ Q ^ 4 := by
          calc Q = Q ^ 1 := (pow_one Q).symm
            _ ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
        have h3 : Q ^ 3 ≤ Q ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
        have h0 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ
        linarith

lemma ipBs_le {m n : ℕ} (A : Fin m → Fin n → ℤ) (b : Fin m → ℤ) (len : ℕ)
    (hs : inputSize (m := m) (n := n) A b ≤ len) :
    Bs (ipW A b) (ipR A b) ≤ 2 ^ (333 * (len + n + 1) ^ 5) := by
  have hQ : 1 ≤ len + n + 1 := by omega
  have hB2 := ipB2_le A b len hs
  have h20 := ipB2_nonneg A b
  have hW : ∀ k j, |ipW A b k j| ≤ ipB2 A b := fun k j => ipWset_mem A b k.1 k.2 j
  have hR : ∀ t j, |ipR A b t j| ≤ ipB2 A b := by
    intro t j
    have ht := t.2
    simp only [ipRset, Finset.mem_filter] at ht
    have h1 := (mem_ipG A b t.1 ht.1).1 (Fin.castSucc j)
    have hc : (1:ℤ) ≤ (ipG A b).card := by exact_mod_cast Finset.card_pos.2 ⟨t.1, ht.1⟩
    have hb0 := ipB1_nonneg A b
    show |t.1 (Fin.castSucc j)| ≤ ((ipG A b).card : ℤ) * ipB1 A b
    nlinarith
  have hX0 := Xb_sep_le (ipW A b) (ipR A b) (ipB2 A b) h20 hW hR
  have hX : Xb (sepA (ipW A b) (ipR A b)) (sepB (κ := ipWset A b) (τ := ipRset A b) (n := n)) ≤
      1 + (((ipWset A b).card : ℤ) + ((ipRset A b).card : ℤ) + 2 * ((n : ℤ) + 1)) *
        (((n : ℤ) + 1) * ipB2 A b + 2) ^ 2 := by
    simp only [Fintype.card_coe] at hX0
    push_cast at hX0
    exact hX0
  have hcW := ipWset_card_le A b len hs
  have hcR := ipRset_card_le A b len hs
  have hn : ((n : ℤ) + 1) ≤ 2 ^ (len + n + 1) :=
    le_trans (succ_le_tp n) (tp_mono (by omega))
  have hn2 : 2 * ((n : ℤ) + 1) ≤ 2 ^ (34 * (len + n + 1) ^ 4) := by
    have h1 : 2 * ((n : ℤ) + 1) ≤ 2 ^ (n + 1) := by rw [pow_succ]; linarith [succ_le_tp n]
    refine le_trans h1 (tp_mono ?_)
    have : len + n + 1 ≤ (len + n + 1) ^ 4 := by
      calc len + n + 1 = (len + n + 1) ^ 1 := (pow_one _).symm
        _ ≤ (len + n + 1) ^ 4 := Nat.pow_le_pow_right hQ (by norm_num)
    omega
  have hn0 : (0:ℤ) ≤ (n : ℤ) + 1 := by omega
  have hc1 : (0:ℤ) ≤ ((ipWset A b).card : ℤ) := Nat.cast_nonneg _
  have hc2 : (0:ℤ) ≤ ((ipRset A b).card : ℤ) := Nat.cast_nonneg _
  have hS := sepX_arith (len + n + 1) hQ ((ipWset A b).card : ℤ) ((ipRset A b).card : ℤ)
    ((n : ℤ) + 1) (ipB2 A b) hcW hcR hn hn0 hn2 hB2 h20 hc1 hc2
  have hX2 := le_trans hX hS
  have := Bv_le (n + 1) (len + n + 1) 110 4 (by omega) hQ (by norm_num)
    (by linarith [Xb_pos (sepA (ipW A b) (ipR A b)) (sepB (κ := ipWset A b) (τ := ipRset A b) (n := n))])
    hX2
  unfold Bs
  have e : (3 + 3 * 110) * (len + n + 1) ^ (4 + 1) = 333 * (len + n + 1) ^ 5 := by norm_num
  rw [e] at this
  exact this

lemma B01_le (n len : ℕ) : B01 n ≤ 2 ^ (33 * (len + n + 1) ^ 2) := by
  have hQ : 1 ≤ len + n + 1 := by omega
  have ha1 : (1:ℤ) ≤ 2 ^ n := one_le_tp n
  have hn : (n:ℤ) + 1 ≤ 2 ^ n := succ_le_tp n
  have hX : (1 + ((2 ^ n + 0 + 2 * (n + 1) : ℕ) : ℤ) * ((n + 1) * 1 + 2) ^ 2) ≤
      2 ^ (10 * (len + n + 1) ^ 1) := by
    push_cast
    have hA : (2:ℤ) ^ n + 2 * ((n:ℤ) + 1) ≤ 3 * 2 ^ n := by linarith
    have hB : ((n:ℤ) + 1) + 2 ≤ 3 * 2 ^ n := by linarith
    have hB2 : (((n:ℤ) + 1) + 2) ^ 2 ≤ (3 * 2 ^ n) ^ 2 := pow_le_pow_left₀ (by positivity) hB 2
    have hP : ((2:ℤ) ^ n + 2 * ((n:ℤ) + 1)) * (((n:ℤ) + 1) + 2) ^ 2 ≤
        (3 * 2 ^ n) * (3 * 2 ^ n) ^ 2 :=
      mul_le_mul hA hB2 (by positivity) (by positivity)
    have e : (2:ℤ) ^ (5 + 3 * n) = 32 * (2 ^ n) ^ 3 := by rw [pow_add, pow_mul']; norm_num
    have h3 : (1:ℤ) ≤ (2 ^ n) ^ 3 := one_le_pow₀ ha1
    calc _ ≤ 1 + (3 * 2 ^ n) * (3 * 2 ^ n) ^ 2 := by nlinarith
      _ ≤ (2:ℤ) ^ (5 + 3 * n) := by rw [e]; nlinarith
      _ ≤ _ := tp_mono (by rw [pow_one]; omega)
  have := Bv_le (n + 1) (len + n + 1) 10 1 (by omega) hQ le_rfl (by positivity) hX
  unfold B01
  have e : (3 + 3 * 10) * (len + n + 1) ^ (1 + 1) = 33 * (len + n + 1) ^ 2 := by norm_num
  rw [e] at this
  exact this

lemma poly_absorb (c e : ℕ) : ∃ k : ℕ, ∀ L : ℕ, c * (L + 1) ^ e ≤ L ^ k + k := by
  refine ⟨c * 2 ^ e + e, fun L => ?_⟩
  have h2e : 1 ≤ 2 ^ e := Nat.one_le_two_pow
  rcases L with _ | _ | L
  · calc c * (0 + 1) ^ e = c := by simp
      _ ≤ c * 2 ^ e + e := by nlinarith
      _ ≤ 0 ^ (c * 2 ^ e + e) + (c * 2 ^ e + e) := Nat.le_add_left _ _
  · have : (0 + 1 + 1 : ℕ) ^ e = 2 ^ e := by norm_num
    rw [this, zero_add, one_pow]
    linarith
  · have hL2 : 2 ≤ L + 1 + 1 := by omega
    have h1 : (L + 1 + 1 + 1) ^ e ≤ (2 * (L + 1 + 1)) ^ e := Nat.pow_le_pow_left (by omega) e
    rw [mul_pow] at h1
    have h2 : c * 2 ^ e < 2 ^ (c * 2 ^ e) := Nat.lt_two_pow_self
    have h3 : 2 ^ (c * 2 ^ e) ≤ (L + 1 + 1) ^ (c * 2 ^ e) := Nat.pow_le_pow_left hL2 _
    calc c * (L + 1 + 1 + 1) ^ e ≤ c * (2 ^ e * (L + 1 + 1) ^ e) := Nat.mul_le_mul le_rfl h1
      _ = (L + 1 + 1) ^ e * (c * 2 ^ e) := by ring
      _ ≤ (L + 1 + 1) ^ e * (L + 1 + 1) ^ (c * 2 ^ e) := Nat.mul_le_mul le_rfl (by omega)
      _ = (L + 1 + 1) ^ (c * 2 ^ e + e) := by rw [← pow_add, Nat.add_comm e]
      _ ≤ (L + 1 + 1) ^ (c * 2 ^ e + e) + (c * 2 ^ e + e) := Nat.le_add_right _ _

theorem assemble (C : COP) (k : ℕ)
    (hsep : ∀ z ∈ C.L, ∀ x : Fin (C.n z) → ℚ, x ∉ hullZ (C.S z) →
      ∃ (f : Fin (C.n z) → ℤ) (g : ℤ), (∀ j, |f j| ≤ 2 ^ ((z.length + C.n z) ^ k + k)) ∧
        |g| ≤ 2 ^ ((z.length + C.n z) ^ k + k) ∧
        (∀ y ∈ C.S z, f ⬝ᵥ y ≤ g) ∧ (g : ℚ) < castv f ⬝ᵥ x) :
    ∃ F : Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ),
      IsFacialDescription C F ∧ IsSmall C F := by
  refine ⟨{t | t.1 ∈ C.L ∧ (∀ i, |t.2.1 i| ≤ 2 ^ ((t.1.length + C.n t.1) ^ k + k)) ∧
      |t.2.2| ≤ 2 ^ ((t.1.length + C.n t.1) ^ k + k) ∧ ∀ y ∈ C.S t.1, t.2.1 ⬝ᵥ y ≤ t.2.2},
      ⟨?_, ?_⟩, ?_⟩
  · intro t ht; exact ht.1
  · intro z hz x
    constructor
    · intro hx f g hF
      obtain ⟨_, _, _, hv⟩ := hF
      have hconv : Convex ℚ {x : Fin (C.n z) → ℚ | (∑ i, (f i : ℚ) * x i) ≤ (g : ℚ)} := by
        intro u hu v hv' a c ha hc hac
        simp only [Set.mem_setOf_eq] at hu hv' ⊢
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
        have e1 : ∑ i, (f i : ℚ) * (a * u i) = a * ∑ i, (f i : ℚ) * u i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
        have e2 : ∑ i, (f i : ℚ) * (c * v i) = c * ∑ i, (f i : ℚ) * v i := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)
        rw [e1, e2]
        have hg : a * (g : ℚ) + c * g = g := by rw [← add_mul, hac, one_mul]
        nlinarith [mul_le_mul_of_nonneg_left hu ha, mul_le_mul_of_nonneg_left hv' hc]
      have hsub : {x : Fin (C.n z) → ℚ | ∃ y ∈ C.S z, x = fun i => (y i : ℚ)} ⊆
          {x | (∑ i, (f i : ℚ) * x i) ≤ (g : ℚ)} := by
        rintro _ ⟨y, hy, rfl⟩
        have := hv y hy
        simp only [Set.mem_setOf_eq]
        have e : (∑ i, (f i : ℚ) * (y i : ℚ)) = ((f ⬝ᵥ y : ℤ) : ℚ) := by
          simp [dotProduct]
        rw [e]; exact_mod_cast this
      exact convexHull_min hsub hconv hx
    · intro hall
      by_contra hx
      obtain ⟨f, g, hf, hg, hv, hlt⟩ := hsep z hz x hx
      have := hall f g ⟨hz, hf, hg, hv⟩
      have e : castv f ⬝ᵥ x = ∑ i, (f i : ℚ) * x i := rfl
      linarith
  · refine ⟨k, fun t ht => ⟨fun i => ?_, ?_⟩⟩
    · have h := ht.2.1 i
      rw [← Int.natCast_natAbs] at h
      exact_mod_cast h
    · have h := ht.2.2.1
      rw [← Int.natCast_natAbs] at h
      exact_mod_cast h

lemma ip_bridge {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (S : Set (Fin n → ℤ))
    (hS : S = {x | (∀ j, 0 ≤ x j) ∧ (fun j => (x j : ℚ)) ∈
          CookSensitivity.ChvatalRank.polyhedron A (fun i => (b i : ℚ))}) :
    S = ipS A b := by
  rw [hS]; ext x
  simp only [Set.mem_setOf_eq, ipS, CookSensitivity.ChvatalRank.polyhedron]
  refine and_congr_right (fun _ => ?_)
  rw [Pi.le_def]
  refine forall_congr' (fun i => ?_)
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

end KPSF

open KarpPapadimitriou.SmallFacial in
theorem solution (C : COP) (hC : IsZeroOne C ∨ IsIPType C) :
    ∃ F : Set (Σ z : List Bool, (Fin (C.n z) → ℤ) × ℤ),
      IsFacialDescription C F ∧ IsSmall C F := by
  rcases hC with h01 | ⟨m, A, b, hAb⟩
  · obtain ⟨k, hk⟩ := KPSF.poly_absorb 33 2
    refine KPSF.assemble C k (fun z hz x hx => ?_)
    obtain ⟨f, g, hf, hg, hv, hlt⟩ := KPSF.zeroOne_sep (C.S z) (h01 z hz) x hx
    have hB : KPSF.B01 (C.n z) ≤ 2 ^ ((z.length + C.n z) ^ k + k) :=
      le_trans (KPSF.B01_le (C.n z) z.length) (KPSF.tp_mono (hk _))
    exact ⟨f, g, fun j => le_trans (hf j) hB, le_trans hg hB, hv, hlt⟩
  · obtain ⟨k, hk⟩ := KPSF.poly_absorb 333 5
    refine KPSF.assemble C k (fun z hz x hx => ?_)
    have hS := KPSF.ip_bridge (A z) (b z) (C.S z) (hAb z hz).2
    rw [hS] at hx ⊢
    obtain ⟨f, g, hf, hg, hv, hlt⟩ := KPSF.ip_sep (A z) (b z) x hx
    have hB := le_trans (KPSF.ipBs_le (A z) (b z) z.length (hAb z hz).1) (KPSF.tp_mono (hk _))
    exact ⟨f, g, fun j => le_trans (hf j) hB, le_trans hg hB, hv, hlt⟩
