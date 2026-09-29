-- Prove2me | solution 1 for MaxLatticeFree.Geometry.exists_lattice_point_near_halfLine
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:08:08.110359+00:00
-- url     : https://prove2.me/submissions/8c5f4491-6e32-4dfa-9d1a-4e929d20ddc2

import Mathlib
import Definitions.Def_MaxLatticeFree_Geometry_IsLatticeOf

namespace MaxLatticeFree.Geometry

end MaxLatticeFree.Geometry

open MaxLatticeFree.Geometry

theorem solution {n : ℕ} (Λ : AddSubgroup (EuclideanSpace ℝ (Fin n)))
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) (hΛ : IsLatticeOf Λ V)
    (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ Λ) (r : EuclideanSpace ℝ (Fin n)) (hrV : r ∈ V) (hr0 : r ≠ 0)
    (ε : ℝ) (hε : 0 < ε) (lam : ℝ) (hlam : 0 ≤ lam) :
    ∃ z ∈ Λ, z ≠ y ∧
      Metric.infDist z {p : EuclideanSpace ℝ (Fin n) | ∃ t : ℝ, lam ≤ t ∧ p = y + t • r} < ε := by
  obtain ⟨m, a, -, hspan, hcl⟩ := hΛ
  rw [← hspan] at hrV
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hrV
  have hrpos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
  set T : ℝ := lam + ε / ‖r‖ + 1 with hT
  have hεr : 0 < ε / ‖r‖ := div_pos hε hrpos
  have hTpos : 0 < T := by linarith
  have hTlam : lam ≤ T := by linarith
  have hTr : ε < T * ‖r‖ := by
    rw [hT, add_mul, add_mul, div_mul_cancel₀ _ hrpos.ne']
    nlinarith
  let f : (Fin m → ℝ) → EuclideanSpace ℝ (Fin n) := fun x => ∑ i, x i • a i
  have hf : Continuous f := by fun_prop
  let u : ℕ → (Fin m → ℝ) := fun k i => Int.fract ((k:ℝ) * T * c i)
  have hu : ∀ k, f (u k) ∈ f '' Set.Icc 0 1 := fun k =>
    ⟨u k, ⟨fun i => Int.fract_nonneg _, fun i => (Int.fract_lt_one _).le⟩, rfl⟩
  obtain ⟨p, -, φ, hφ, hlim⟩ := (isCompact_Icc.image hf).tendsto_subseq hu
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.mp hlim.cauchySeq ε hε
  have hd := hN (N+1) (by omega)
  have hk : φ N < φ (N+1) := hφ (by omega)
  set k1 := φ N
  set k2 := φ (N+1)
  set w : EuclideanSpace ℝ (Fin n) :=
    ∑ i, ((⌊(k2:ℝ) * T * c i⌋ - ⌊(k1:ℝ) * T * c i⌋ : ℤ) : ℝ) • a i with hwdef
  have hw : w ∈ Λ := by
    rw [hcl]
    refine AddSubgroup.sum_mem _ (fun i _ => ?_)
    rw [Int.cast_smul_eq_zsmul]
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self i)) _
  set t : ℝ := ((k2:ℝ) - k1) * T with htdef
  have hk' : (1:ℝ) ≤ (k2:ℝ) - k1 := by
    have : (k1:ℝ) + 1 ≤ k2 := by exact_mod_cast hk
    linarith
  have htT : T ≤ t := by nlinarith
  have ht : f (u k2) - f (u k1) = t • r - w := by
    simp only [f, u, hwdef, ← hc, Finset.smul_sum, ← Finset.sum_sub_distrib, smul_smul, ← sub_smul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 1
    simp only [Int.fract, htdef, Int.cast_sub]
    ring
  have hdist : dist (y + w) (y + t • r) < ε := by
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← norm_neg, neg_sub, ← ht, ← dist_eq_norm]
    exact hd
  refine ⟨y + w, AddSubgroup.add_mem _ hy hw, ?_, ?_⟩
  · intro h
    have hw0 : w = 0 := by
      have := congrArg (fun x => x - y) h
      simpa using this
    rw [hw0, add_zero, dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul,
      Real.norm_of_nonneg (by linarith)] at hdist
    nlinarith
  · exact lt_of_le_of_lt (Metric.infDist_le_dist_of_mem ⟨t, by linarith, rfl⟩) hdist
