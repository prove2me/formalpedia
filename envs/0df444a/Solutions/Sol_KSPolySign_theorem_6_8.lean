-- Prove2me | solution 1 for KSPolySign.theorem_6_8
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T14:28:30.00142+00:00
-- url     : https://prove2.me/submissions/fa0c19ae-1b8c-439a-bfb5-06c2e9598594
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AgnosticTNS_opNorm
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_VecBalPoly_Admissible
import Definitions.Def_VecBalPoly_realOps
import Definitions.Def_KSPolySign_IsRatC
import Definitions.Def_KSPolySign_layout
import Theorems.Thm_KSPolySign_theorem_6_8_a
import Theorems.Thm_KSPolySign_theorem_6_8_b
open Matrix
open scoped ComplexOrder

namespace KSPolySign.Main

section L2
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem opNorm_eq_l2 {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    AgnosticTNS.opNorm M = ‖M‖ := by
  rw [Matrix.cstar_norm_def, ← ContinuousLinearMap.sSup_unitClosedBall_eq_norm]
  unfold AgnosticTNS.opNorm
  congr 1
  ext r
  simp only [Set.mem_image, Set.mem_setOf_eq, Metric.mem_closedBall, dist_zero_right]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨WithLp.toLp 2 x, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq]; exact Real.sqrt_le_one.mpr hx
    · rw [EuclideanSpace.norm_eq]; simp
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.ofLp, ?_, ?_⟩
    · rw [EuclideanSpace.norm_eq] at hx
      simpa using (Real.sqrt_le_one (x := ∑ i, ‖x i‖ ^ 2)).mp hx
    · rw [EuclideanSpace.norm_eq]; simp

theorem algebraMap_eq {n : ℕ} (r : ℝ) :
    algebraMap ℝ (Matrix (Fin n) (Fin n) ℂ) r = ((r : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Algebra.algebraMap_eq_smul_one]
  ext i j
  simp [Matrix.smul_apply, one_apply]

theorem vv_sq {n : ℕ} (a : Fin n → ℂ) :
    vecMulVec a (star a) * vecMulVec a (star a) =
      (((∑ j, ‖a j‖ ^ 2 : ℝ)) : ℂ) • vecMulVec a (star a) := by
  ext i l
  simp only [mul_apply, vecMulVec_apply, Matrix.smul_apply, smul_eq_mul, Pi.star_apply]
  have : ((∑ j, ‖a j‖ ^ 2 : ℝ) : ℂ) = ∑ j, star (a j) * a j := by
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [this, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem part_c :
    ∀ (m n : ℕ) (a : Fin m → Fin n → ℂ) (α : ℝ),
      ∑ i, Matrix.vecMulVec (a i) (star (a i)) = 1 → (∀ i, ∑ j, ‖a i j‖ ^ 2 ≤ α) →
      ∀ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) →
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • Matrix.vecMulVec (a i) (star (a i))) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, Matrix.vecMulVec (a i) (star (a i)) * Matrix.vecMulVec (a i) (star (a i)))) →
        ∀ s : ℝ, (s = 1 ∨ s = -1) →
          AgnosticTNS.opNorm ((∑ i ∈ Finset.univ.filter (fun i => σ i = s), Matrix.vecMulVec (a i) (star (a i))) -
            (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 1.7407 * Real.sqrt α  := by
  intro m n a α hsum hα σ hσ hbound s hs
  set A : Fin m → Matrix (Fin n) (Fin n) ℂ := fun i => vecMulVec (a i) (star (a i)) with hA
  simp only [opNorm_eq_l2] at hbound ⊢
  have hss : s * s = 1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hid : (∑ i ∈ Finset.univ.filter (fun i => σ i = s), A i) - (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)
      = ((s / 2 : ℝ) : ℂ) • ∑ i, ((σ i : ℝ) : ℂ) • A i := by
    rw [← hsum, Finset.sum_filter, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    split_ifs with h
    · rw [h]
      have : ((s / 2 : ℝ) : ℂ) * (s : ℂ) = 1 / 2 := by
        have := congrArg (fun x : ℝ => (x : ℂ)) hss; push_cast at this ⊢
        linear_combination this / 2
      rw [this]; module
    · have hσ' : σ i = -s := by
        rcases hσ i with h1 | h1 <;> rcases hs with h2 | h2 <;> simp_all <;> norm_num
      rw [hσ']
      have : ((s / 2 : ℝ) : ℂ) * ((-s : ℝ) : ℂ) = -(1 / 2) := by
        have := congrArg (fun x : ℝ => (x : ℂ)) hss; push_cast at this ⊢
        linear_combination -this / 2
      rw [this]; module
  rw [hid, norm_smul, Complex.norm_real, Real.norm_eq_abs]
  have habs : |s / 2| = 1 / 2 := by rcases hs with h | h <;> rw [h] <;> norm_num
  rw [habs]
  -- variance bound
  set α' := max α 0
  have hα' : 0 ≤ α' := le_max_right _ _
  have hc : ∀ i, ∑ j, ‖a i j‖ ^ 2 ≤ α' := fun i => (hα i).trans (le_max_left _ _)
  have hAA : ∑ i, A i * A i = ∑ i, (((∑ j, ‖a i j‖ ^ 2 : ℝ)) : ℂ) • A i :=
    Finset.sum_congr rfl fun i _ => vv_sq (a i)
  have hpsd : ∀ i, (A i).PosSemidef := fun i => posSemidef_vecMulVec_self_star (a i)
  have h0 : (∑ i, A i * A i).PosSemidef := by
    rw [hAA]; exact posSemidef_sum _ fun i _ => (hpsd i).smul (by
      exact_mod_cast (Finset.sum_nonneg fun j _ => by positivity : (0:ℝ) ≤ ∑ j, ‖a i j‖ ^ 2))
  have h1 : (((α' : ℝ) : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ) - ∑ i, A i * A i).PosSemidef := by
    rw [hAA, ← hsum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine posSemidef_sum _ fun i _ => ?_
    rw [← sub_smul, ← Complex.ofReal_sub]
    exact (hpsd i).smul (by exact_mod_cast sub_nonneg.mpr (hc i))
  have hnorm : ‖∑ i, A i * A i‖ ≤ α' := by
    have := (CStarAlgebra.norm_le_iff_le_algebraMap (∑ i, A i * A i) hα' h0.nonneg).mpr
      (by rw [algebraMap_eq]; exact Matrix.le_iff.mpr h1)
    exact this
  have hsq : Real.sqrt ‖∑ i, A i * A i‖ ≤ Real.sqrt α := by
    calc Real.sqrt ‖∑ i, A i * A i‖ ≤ Real.sqrt α' := Real.sqrt_le_sqrt hnorm
      _ = Real.sqrt α := by
        rcases le_total α 0 with h | h
        · simp [α', max_eq_right h, Real.sqrt_eq_zero'.mpr h]
        · simp [α', max_eq_left h]
  calc 1 / 2 * ‖∑ i, ((σ i : ℝ) : ℂ) • A i‖ ≤ 1 / 2 * (3.4814 * Real.sqrt ‖∑ i, A i * A i‖) := by
        gcongr
    _ ≤ 1 / 2 * (3.4814 * Real.sqrt α) := by gcongr
    _ = 1.7407 * Real.sqrt α := by ring

end L2
end KSPolySign.Main

open KSPolySign

theorem solution :
    (∀ (m n : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℂ), (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1) →
      ∃ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) ∧
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • A i) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) ∧
    (∃ P : MatMulTimeLP.Program, VecBalPoly.Admissible P ∧ ∃ C k : ℕ,
      ∀ (m n : ℕ), 1 ≤ n → ∀ A : Fin m → Matrix (Fin n) (Fin n) ℂ,
        (∀ i, (A i).IsHermitian ∧ (A i).rank ≤ 1 ∧ ∀ j l, IsRatC (A i j l)) →
        ∀ ω : MatMulTimeLP.Tape, ∃ t : ℕ, MatMulTimeLP.HaltsAt P (layout m n A) ω t ∧
          (VecBalPoly.realOps P (layout m n A) ω t : ℝ) ≤
            C * ((m : ℝ) * n ^ 2 + (n : ℝ) ^ 56) * Real.log (m + n + 2) ^ k ∧
          ((t + 1 : ℕ) : ℝ) ≤ C * ((m : ℝ) + n + 2) ^ k ∧
          (∀ i, MatMulTimeLP.outputAt P (layout m n A) ω t m i = 1 ∨ MatMulTimeLP.outputAt P (layout m n A) ω t m i = -1) ∧
          AgnosticTNS.opNorm (∑ i, ((MatMulTimeLP.outputAt P (layout m n A) ω t m i : ℝ) : ℂ) • A i) ≤
            3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, A i * A i))) ∧
    ∀ (m n : ℕ) (a : Fin m → Fin n → ℂ) (α : ℝ),
      ∑ i, Matrix.vecMulVec (a i) (star (a i)) = 1 → (∀ i, ∑ j, ‖a i j‖ ^ 2 ≤ α) →
      ∀ σ : Fin m → ℝ, (∀ i, σ i = 1 ∨ σ i = -1) →
        AgnosticTNS.opNorm (∑ i, ((σ i : ℝ) : ℂ) • Matrix.vecMulVec (a i) (star (a i))) ≤
          3.4814 * Real.sqrt (AgnosticTNS.opNorm (∑ i, Matrix.vecMulVec (a i) (star (a i)) * Matrix.vecMulVec (a i) (star (a i)))) →
        ∀ s : ℝ, (s = 1 ∨ s = -1) →
          AgnosticTNS.opNorm ((∑ i ∈ Finset.univ.filter (fun i => σ i = s), Matrix.vecMulVec (a i) (star (a i))) -
            (1 / 2 : ℂ) • (1 : Matrix (Fin n) (Fin n) ℂ)) ≤ 1.7407 * Real.sqrt α := by
  exact ⟨KSPolySign.theorem_6_8_a, KSPolySign.theorem_6_8_b, KSPolySign.Main.part_c⟩
