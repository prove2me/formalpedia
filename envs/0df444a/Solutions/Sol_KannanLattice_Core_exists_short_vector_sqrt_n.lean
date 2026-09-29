-- Prove2me | solution 1 for KannanLattice.Core.exists_short_vector_sqrt_n
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:18:00.928003+00:00
-- url     : https://prove2.me/submissions/430d0ca7-c615-42c3-8443-d88414f52efd

import Mathlib
import Definitions.Def_KannanLattice_Core_Lattice



namespace KannanLattice.Core

open InnerProductSpace

lemma lattice_le_span {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    {v : EuclideanSpace ℝ (Fin k)} (hv : v ∈ lattice b) :
    v ∈ Submodule.span ℝ (Set.range b) := by
  unfold lattice at hv
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span hx
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ hx

lemma inner_gsN_lt {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) {t j : Fin m}
    (h : t < j) : inner ℝ (gramSchmidtNormed ℝ b j) (b t) = 0 := by
  simp [gramSchmidtNormed, inner_smul_left, gramSchmidt_inv_triangular ℝ b h]

lemma inner_gs_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidt ℝ b t) (b t) = ‖gramSchmidt ℝ b t‖ ^ 2 := by
  conv_lhs => rw [gramSchmidt_def'' ℝ b t]
  rw [inner_add_right, inner_sum, real_inner_self_eq_norm_sq]
  rw [Finset.sum_eq_zero, add_zero]
  intro i hi
  rw [inner_smul_right, gramSchmidt_orthogonal ℝ b (Finset.mem_Iio.1 hi).ne', mul_zero]

lemma inner_gsN_self {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (t : Fin m) :
    inner ℝ (gramSchmidtNormed ℝ b t) (b t) = gsLen b t := by
  unfold gramSchmidtNormed gsLen
  rw [inner_smul_left, inner_gs_self]
  simp only [RCLike.conj_to_real]
  by_cases h : ‖gramSchmidt ℝ b t‖ = 0
  · simp [h]
  · field_simp
    rfl

lemma gsLen_pos {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b)
    (t : Fin m) : 0 < gsLen b t := by
  unfold gsLen
  exact norm_pos_iff.2 (gramSchmidt_ne_zero t hb)

lemma norm_sq_eq_sum_inner {m k : ℕ} (b : Fin m → EuclideanSpace ℝ (Fin k))
    (hb : LinearIndependent ℝ b) (w : EuclideanSpace ℝ (Fin k))
    (hw : w ∈ Submodule.span ℝ (Set.range b)) :
    ‖w‖ ^ 2 = ∑ j, (inner ℝ (gramSchmidtNormed ℝ b j) w) ^ 2 := by
  have hu := gramSchmidtNormed_orthonormal (𝕜 := ℝ) hb
  rw [← span_gramSchmidt ℝ b, ← span_gramSchmidtNormed_range] at hw
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
  have hc : ∀ j, inner ℝ (gramSchmidtNormed ℝ b j) (∑ i, a i • gramSchmidtNormed ℝ b i) = a j :=
    fun j => hu.inner_right_fintype a j
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, hc]
  simp [sq]

open MeasureTheory

theorem short_core (m k : ℕ) (hm : 1 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ v ∈ lattice b, v ≠ 0 ∧
      ‖v‖ ≤ Real.sqrt m * latticeDet b ^ ((1 : ℝ) / m) := by
  set u := gramSchmidtNormed ℝ b with hu
  let β : Fin m → (Fin m → ℝ) := fun i j => inner ℝ (u j) (b i)
  have hlow : (Matrix.of β).IsLowerTriangular := by
    intro i j hij
    have : i < j := OrderDual.toDual_lt_toDual.1 hij
    simp only [Matrix.of_apply, β, hu]
    exact inner_gsN_lt b this
  have hdet : (Matrix.of β).det = latticeDet b := by
    rw [Matrix.det_of_isLowerTriangular _ hlow, latticeDet]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [Matrix.of_apply, β, hu]
    exact inner_gsN_self b i
  have hdpos : 0 < latticeDet b := Finset.prod_pos fun i _ => gsLen_pos b hb i
  have hli : LinearIndependent ℝ β := by
    have := Matrix.linearIndependent_rows_of_det_ne_zero (A := Matrix.of β)
      (by rw [hdet]; exact hdpos.ne')
    exact this
  haveI : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
  have hB : ⇑B = β := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  let L := (Submodule.span ℤ (Set.range B)).toAddSubgroup
  have fund : IsAddFundamentalDomain L (ZSpan.fundamentalDomain B) volume :=
    ZSpan.isAddFundamentalDomain' B volume
  have hvolF : volume (ZSpan.fundamentalDomain B) = ENNReal.ofReal (latticeDet b) := by
    rw [ZSpan.volume_fundamentalDomain, hB, hdet, abs_of_pos hdpos]
  set a : ℝ := latticeDet b ^ ((1 : ℝ) / m) with ha
  have ha0 : 0 ≤ a := Real.rpow_nonneg hdpos.le _
  have ham : a ^ m = latticeDet b := by
    rw [ha, one_div]; exact Real.rpow_inv_natCast_pow hdpos.le (by omega)
  let s : Set (Fin m → ℝ) := Set.univ.pi fun _ => Set.Icc (-a) a
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx j _
    have := hx j (Set.mem_univ _)
    simp only [Pi.neg_apply, Set.mem_Icc] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hconv : Convex ℝ s := convex_pi fun _ _ => convex_Icc _ _
  have hcpt : IsCompact s := isCompact_univ_pi fun _ => isCompact_Icc
  have hvol : volume (ZSpan.fundamentalDomain B) * 2 ^ Module.finrank ℝ (Fin m → ℝ) ≤
      volume s := by
    rw [hvolF, Module.finrank_fin_fun, volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [show a - -a = 2 * a by ring, ← ENNReal.ofReal_pow (by positivity), mul_pow, ham,
      mul_comm ((2:ℝ)^m), ENNReal.ofReal_mul hdpos.le, ENNReal.ofReal_pow (by norm_num)]
    simp
  haveI hcount : Countable L := by
    have : Countable (Submodule.span ℤ (Set.range B)) := inferInstance
    exact this
  obtain ⟨x, hx0, hxs⟩ :=
    exists_ne_zero_mem_lattice_of_measure_mul_two_pow_le_measure fund hsymm hconv hcpt hvol
  have hxmem : (x : Fin m → ℝ) ∈ Submodule.span ℤ (Set.range B) := x.2
  obtain ⟨z, hz⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).1 hxmem
  refine ⟨∑ i, z i • b i, ?_, ?_, ?_⟩
  · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · have hcoord : ∀ j, inner ℝ (u j) (∑ i, z i • b i) = (x : Fin m → ℝ) j := by
      intro j
      rw [← hz, inner_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hB, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, Pi.smul_apply]
      simp [β, zsmul_eq_mul]
    intro h0
    apply hx0
    ext j
    have := hcoord j
    rw [h0, inner_zero_right] at this
    simp [← this]
  · have hcoord : ∀ j, inner ℝ (u j) (∑ i, z i • b i) = (x : Fin m → ℝ) j := by
      intro j
      rw [← hz, inner_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hB, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, Pi.smul_apply]
      simp [β, zsmul_eq_mul]
    have hmem : ∑ i, z i • b i ∈ Submodule.span ℝ (Set.range b) :=
      lattice_le_span b (Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    have hn := norm_sq_eq_sum_inner b hb _ hmem
    have hsq : ‖∑ i, z i • b i‖ ^ 2 ≤ (m : ℝ) * a ^ 2 := by
      rw [hn]
      calc ∑ j, (inner ℝ (gramSchmidtNormed ℝ b j) (∑ i, z i • b i)) ^ 2
          ≤ ∑ _j : Fin m, a ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            rw [← hu, hcoord j]
            have := hxs j (Set.mem_univ _)
            rw [Set.mem_Icc] at this
            nlinarith [this.1, this.2]
        _ = (m : ℝ) * a ^ 2 := by simp
    have : Real.sqrt m * a = Real.sqrt ((m : ℝ) * a ^ 2) := by
      rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq ha0]
    rw [this]
    exact Real.le_sqrt_of_sq_le hsq

end KannanLattice.Core

open KannanLattice.Core


theorem solution (m k : ℕ) (hm : 1 ≤ m)
    (b : Fin m → EuclideanSpace ℝ (Fin k)) (hb : LinearIndependent ℝ b) :
    ∃ v ∈ lattice b, v ≠ 0 ∧
      ‖v‖ ≤ Real.sqrt m * latticeDet b ^ ((1 : ℝ) / m) := by
  exact short_core m k hm b hb
