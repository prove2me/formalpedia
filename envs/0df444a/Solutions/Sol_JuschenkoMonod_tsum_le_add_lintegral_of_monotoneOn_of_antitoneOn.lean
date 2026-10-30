-- Prove2me | solution 1 for JuschenkoMonod.tsum_le_add_lintegral_of_monotoneOn_of_antitoneOn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T20:38:19.237529+00:00
-- url     : https://prove2.me/submissions/3bf345e2-a473-4cd7-93e3-24c5608f3dc5

import Mathlib
open MeasureTheory
open scoped ENNReal NNReal
namespace JuschenkoMonod

/-- A constant lower bound on an interval gives a lower bound on the set lintegral. -/
lemma const_mul_le_setLIntegral_Ico (φ : ℝ → ℝ≥0) (a b : ℝ) (c : ℝ≥0)
    (h : ∀ x ∈ Set.Ico a b, c ≤ φ x) :
    (c : ℝ≥0∞) * ENNReal.ofReal (b - a) ≤ ∫⁻ t in Set.Ico a b, (φ t : ℝ≥0∞) := by
  rw [← Real.volume_Ico, ← setLIntegral_const]
  exact setLIntegral_mono' measurableSet_Ico fun x hx => by exact_mod_cast h x hx

lemma iUnion_Ico_nat : (⋃ k : ℕ, Set.Ico (k : ℝ) (k + 1)) = Set.Ici 0 := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_Ico, Set.mem_Ici]
  constructor
  · rintro ⟨k, hk, -⟩
    exact le_trans (Nat.cast_nonneg k) hk
  · intro hx
    exact ⟨⌊x⌋₊, Nat.floor_le hx, Nat.lt_floor_add_one x⟩

lemma pairwise_disjoint_Ico_nat :
    Pairwise (Function.onFun Disjoint (fun k : ℕ => Set.Ico (k : ℝ) (k + 1))) := by
  intro i j hij
  refine Set.disjoint_left.mpr fun x hi hj => hij ?_
  have hx : 0 ≤ x := le_trans (Nat.cast_nonneg i) hi.1
  rw [← (Nat.floor_eq_iff hx).mpr hi, ← (Nat.floor_eq_iff hx).mpr hj]

/-- Combinatorial assembly of the termwise bounds. -/
lemma tsum_assemble (f g : ℕ → ℝ≥0∞) (c : ℝ≥0∞) (N : ℕ)
    (hlow : ∀ k < N, f k ≤ g k) (hmid : f N + f (N + 1) ≤ c + g N)
    (hhigh : ∀ k, N + 1 ≤ k → f (k + 1) ≤ g k) :
    ∑' j, f j ≤ c + ∑' k, g k := by
  rw [← (ENNReal.summable (f := fun n => f (n + (N + 2)))).sum_add_tsum_nat_add',
    ← (ENNReal.summable (f := fun n => g (n + (N + 1)))).sum_add_tsum_nat_add',
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
  have hS : ∑ x ∈ Finset.range N, f x ≤ ∑ x ∈ Finset.range N, g x :=
    Finset.sum_le_sum fun k hk => hlow k (Finset.mem_range.mp hk)
  have hT : ∑' i, f (i + (N + 2)) ≤ ∑' i, g (i + (N + 1)) :=
    ENNReal.tsum_le_tsum fun i => by
      have := hhigh (i + (N + 1)) (by omega)
      rwa [show i + (N + 1) + 1 = i + (N + 2) by omega] at this
  calc ∑ x ∈ Finset.range N, f x + f N + f (N + 1) + ∑' i, f (i + (N + 2))
      = ∑ x ∈ Finset.range N, f x + (f N + f (N + 1)) + ∑' i, f (i + (N + 2)) := by
        rw [add_assoc (∑ x ∈ Finset.range N, f x)]
    _ ≤ ∑ x ∈ Finset.range N, g x + (c + g N) + ∑' i, g (i + (N + 1)) := by
        gcongr
    _ = c + (∑ x ∈ Finset.range N, g x + g N + ∑' i, g (i + (N + 1))) := by
        abel

/-- Real-arithmetic core of the middle estimate. -/
lemma mid_real (x y z l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hx : x ≤ z) (hy : y ≤ z) :
    x + y ≤ z + (x * l + y * (1 - l)) := by
  nlinarith [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hl1), mul_le_mul_of_nonneg_left hy hl0]

lemma mid_ennreal (x y z : ℝ≥0) (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (hx : x ≤ z) (hy : y ≤ z) :
    (x : ℝ≥0∞) + y ≤ z + ((x : ℝ≥0∞) * ENNReal.ofReal l + (y : ℝ≥0∞) * ENNReal.ofReal (1 - l)) := by
  have key := mid_real x y z l hl0 hl1 (by exact_mod_cast hx) (by exact_mod_cast hy)
  have h1 : (0 : ℝ) ≤ 1 - l := by linarith
  have e1 : ((x : ℝ≥0∞) + y) = ENNReal.ofReal ((x : ℝ) + y) := by
    rw [ENNReal.ofReal_add x.coe_nonneg y.coe_nonneg, ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  have e2 : (z : ℝ≥0∞) + ((x : ℝ≥0∞) * ENNReal.ofReal l + (y : ℝ≥0∞) * ENNReal.ofReal (1 - l))
      = ENNReal.ofReal ((z : ℝ) + ((x : ℝ) * l + (y : ℝ) * (1 - l))) := by
    rw [ENNReal.ofReal_add z.coe_nonneg (add_nonneg (mul_nonneg x.coe_nonneg hl0) (mul_nonneg y.coe_nonneg h1)),
      ENNReal.ofReal_add (mul_nonneg x.coe_nonneg hl0) (mul_nonneg y.coe_nonneg h1),
      ENNReal.ofReal_mul x.coe_nonneg, ENNReal.ofReal_mul y.coe_nonneg, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_coe_nnreal]
  rw [e1, e2]
  exact ENNReal.ofReal_le_ofReal key

theorem integral_comp_aux (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (φ : ℝ → ℝ≥0)
    (hinc : MonotoneOn φ (Set.Icc 0 t₀)) (hdec : AntitoneOn φ (Set.Ici t₀)) :
    ∑' j : ℕ, (φ j : ℝ≥0∞) ≤ φ t₀ + ∫⁻ t in Set.Ici 0, φ t := by
  obtain ⟨N, hN⟩ : ∃ N, N = ⌊t₀⌋₊ := ⟨_, rfl⟩
  have hNle : (N : ℝ) ≤ t₀ := hN ▸ Nat.floor_le ht₀
  have hNlt : t₀ < (N : ℝ) + 1 := hN ▸ Nat.lt_floor_add_one t₀
  clear hN
  have hint : ∫⁻ t in Set.Ici 0, (φ t : ℝ≥0∞) =
      ∑' k : ℕ, ∫⁻ t in Set.Ico (k : ℝ) (k + 1), (φ t : ℝ≥0∞) := by
    rw [← iUnion_Ico_nat, lintegral_iUnion (fun _ => measurableSet_Ico) pairwise_disjoint_Ico_nat]
  rw [hint]
  refine tsum_assemble (fun j : ℕ => (φ j : ℝ≥0∞))
    (fun k : ℕ => ∫⁻ t in Set.Ico (k : ℝ) (k + 1), (φ t : ℝ≥0∞)) _ N ?_ ?_ ?_
  · intro k hk
    have hk' : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
    have := const_mul_le_setLIntegral_Ico φ k (k + 1) (φ k) (fun x hx =>
      hinc ⟨Nat.cast_nonneg k, by linarith⟩ ⟨le_trans (Nat.cast_nonneg k) hx.1, by
        linarith [hx.2]⟩ hx.1)
    simpa using this
  · have h1 := const_mul_le_setLIntegral_Ico φ N t₀ (φ N) (fun x hx =>
      hinc ⟨Nat.cast_nonneg N, hNle⟩ ⟨le_trans (Nat.cast_nonneg N) hx.1, hx.2.le⟩ hx.1)
    have h2 := const_mul_le_setLIntegral_Ico φ t₀ (N + 1) (φ ((N + 1 : ℕ) : ℝ)) (fun x hx =>
      hdec hx.1 (show t₀ ≤ ((N + 1 : ℕ) : ℝ) by push_cast; linarith)
        (by push_cast; exact hx.2.le))
    have hsplit : ∫⁻ t in Set.Ico (N : ℝ) (N + 1), (φ t : ℝ≥0∞) =
        (∫⁻ t in Set.Ico (N : ℝ) t₀, (φ t : ℝ≥0∞)) +
        ∫⁻ t in Set.Ico t₀ ((N : ℝ) + 1), (φ t : ℝ≥0∞) := by
      rw [← Set.Ico_union_Ico_eq_Ico hNle hNlt.le,
        lintegral_union measurableSet_Ico Set.Ico_disjoint_Ico_same]
    have hx : φ N ≤ φ t₀ := hinc ⟨Nat.cast_nonneg N, hNle⟩ ⟨ht₀, le_rfl⟩ hNle
    have hy : φ ((N + 1 : ℕ) : ℝ) ≤ φ t₀ :=
      hdec (Set.mem_Ici.mpr le_rfl) (show t₀ ≤ ((N + 1 : ℕ) : ℝ) by push_cast; linarith)
        (by push_cast; linarith)
    have hm := mid_ennreal (φ N) (φ ((N + 1 : ℕ) : ℝ)) (φ t₀) (t₀ - N) (by linarith)
      (by linarith) hx hy
    have e : (1 : ℝ) - (t₀ - N) = (N : ℝ) + 1 - t₀ := by ring
    rw [e] at hm
    refine hm.trans ?_
    rw [hsplit]
    gcongr
  · intro k hk
    have hk' : (N : ℝ) + 1 ≤ k := by exact_mod_cast hk
    have := const_mul_le_setLIntegral_Ico φ k (k + 1) (φ ((k + 1 : ℕ) : ℝ)) (fun x hx =>
      hdec (show t₀ ≤ x by linarith [hx.1]) (show t₀ ≤ ((k + 1 : ℕ) : ℝ) by
        push_cast; linarith) (by push_cast; exact hx.2.le))
    simpa using this

end JuschenkoMonod

theorem solution : ∀ (t₀ : ℝ) (ht₀ : 0 ≤ t₀) (φ : ℝ → ℝ≥0)
    (hinc : MonotoneOn φ (Set.Icc 0 t₀)) (hdec : AntitoneOn φ (Set.Ici t₀)),
    ∑' j : ℕ, (φ j : ℝ≥0∞) ≤ φ t₀ + ∫⁻ t in Set.Ici 0, φ t :=
  fun t₀ ht₀ φ hinc hdec => JuschenkoMonod.integral_comp_aux t₀ ht₀ φ hinc hdec
