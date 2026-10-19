-- Prove2me | solution 1 for OAI.Erdos3.exists_retained_affine_epoch_transition_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:37:09.52346+00:00
-- url     : https://prove2.me/submissions/d6b3b48c-0809-4555-aeaf-6977419a3989

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B213
import Definitions.Def_OAIE3v2B238

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem refined_residue_constraints_iff {M d J : ℕ} (hcop : (M * d).Coprime J)
    {u v w c : ℤ} (hM : c ≡ u [ZMOD (M : ℤ)]) (hd : c ≡ v [ZMOD (d : ℤ)])
    (hJ : c ≡ w [ZMOD (J : ℤ)]) (x : ℤ) :
    (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ v [ZMOD (d : ℤ)] ∧ x ≡ w [ZMOD (J : ℤ)]) ↔
      x ≡ c [ZMOD (Nat.lcm M d * J : ℤ)] := by
  have hL : (Nat.lcm M d).Coprime J := hcop.of_dvd_left (Nat.lcm_dvd_mul M d)
  rw [← and_assoc, residue_constraints_iff_lcm hM hd x,
    residue_constraints_iff_lcm (Int.ModEq.refl c) hJ x, hL.lcm_eq_mul]
  simp only [Nat.cast_mul]

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

theorem residueIndexLength_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |(residueIndexLength a b r v : ℝ) - ((b - a : ℤ) : ℝ) / (r : ℝ)| ≤ 1 := by
  rw [residueIndexLength_eq_card a b r v hr]
  exact scalarResidue_card_absolute_error a b r v hab hr

end Erdos3

end

section

namespace Erdos3

theorem CompatibleAuxResidue.refinedValue_spec {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J) (w : ℤ) :
    v.refinedValue hcop w ≡ u [ZMOD (M : ℤ)] ∧
      v.refinedValue hcop w ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)] ∧
      v.refinedValue hcop w ≡ w [ZMOD (J : ℤ)] :=
  Classical.choose_spec ((coprime_refinement_preserves_compatibility hcop u v.val.val w).mp v.property)

theorem refinement_modEq_iff {M J : ℕ} (hcop : M.Coprime J) {u w : ℤ}
    (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) :
    x ≡ w [ZMOD (M * J : ℕ)] ↔
      (x ≡ u [ZMOD (M : ℤ)] ∧ x ≡ w [ZMOD (J : ℤ)]) := by
  simpa only [hcop.lcm_eq_mul] using
    (residue_constraints_iff_lcm hw (show w ≡ w [ZMOD (J : ℤ)] from Int.ModEq.refl w) x).symm

theorem CompatibleAuxResidue.refinedConstraint_iff {M d J : ℕ} {u : ℤ}
    (v : CompatibleAuxResidue M d u) (hcop : (M * d).Coprime J)
    (w : ℤ) (hw : w ≡ u [ZMOD (M : ℤ)]) (x : ℤ) :
    (x ≡ w [ZMOD (M * J : ℕ)] ∧ x ≡ (v.val.val : ℤ) [ZMOD (d : ℤ)]) ↔
      x ≡ v.refinedValue hcop w [ZMOD (Nat.lcm M d * J : ℕ)] := by
  have hMJ : M.Coprime J := hcop.of_dvd_left (dvd_mul_right M d)
  rw [refinement_modEq_iff hMJ hw x]
  have hc := v.refinedValue_spec hcop w
  exact (and_assoc.trans (and_congr_right fun _ => and_comm)).trans
    (refined_residue_constraints_iff hcop hc.1 hc.2.1 hc.2.2 x)

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_ge_of_width (a b r v : ℤ) (hr : 0 < r)
    (B : ℝ) (hB : 0 ≤ B) (hwidth : (r : ℝ) * (B + 1) ≤ ((b - a : ℤ) : ℝ)) :
    B ≤ (residueIndexLength a b r v : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hwidthpos : (0 : ℝ) < ((b - a : ℤ) : ℝ) :=
    (mul_pos hr' (by linarith : 0 < B + 1)).trans_le hwidth
  have hab : a ≤ b := by
    have h : (0 : ℤ) ≤ b - a := by exact_mod_cast hwidthpos.le
    omega
  have hlower := (abs_le.mp (residueIndexLength_absolute_error a b r v hab hr)).1
  have hratio : B + 1 ≤ ((b - a : ℤ) : ℝ) / (r : ℝ) :=
    (le_div_iff₀ hr').mpr (by simpa only [mul_comm] using hwidth)
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem integerResidueBox_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i) (f : (I → ℤ) → ℂ) :
    (𝔼 x : IntegerResidueBox a b r v, f (fun i => (x i).val)) =
      𝔼 x ∈ translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
        (fun i => residueIndexLength (a i) (b i) (r i) (v i)), f (fun i => v i + r i * x i) := by
  let B := translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
    (fun i => residueIndexLength (a i) (b i) (r i) (v i))
  have h := Fintype.expect_equiv (integerResidueBoxEquiv a b r v hr)
    (fun x => f (fun i => v i + r i * x.val i))
    (fun x => f (fun i => (x i).val)) (fun _ => rfl)
  let g : (I → ℤ) → ℂ := fun x => f (fun i => v i + r i * x i)
  have hcoe : (𝔼 x : ↥B, g x.val) = 𝔼 x ∈ B, g x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card, Fintype.card_coe,
      Finset.sum_coe_sort]
  exact h.symm.trans hcoe

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ExternalFamilyCircleProjection
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

namespace CircleFourier

theorem iteratedCircleAverage_weighted_error
    {X α G J : Type*} [PseudoMetricSpace X] [Fintype G] [Fintype J]
    (A : α → IsometricCircleAction X) (is : List α) (f : X → ℂ)
    (v : J → X → ℂ) (n : J → α → ℤ) (path : G → X) (weight : G → ℂ)
    (Lf : ℝ≥0) (Lv : J → ℝ≥0) (hf : LipschitzWith Lf f)
    (hv : ∀ j, LipschitzWith (Lv j) (v j))
    {B rho tau : ℝ} (hmass : (∑ x, ‖weight x‖) ≤ B)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (happrox : ∀ x, ‖f x - ∑ j, v j x‖ ≤ rho)
    (heigen : ∀ j i, i ∈ is → ∀ t x, v j ((A i).act t x) = character (n j i • t) * v j x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖∑ x, weight x * v j (path x)‖ ≤ tau) :
    ‖(∑ x, weight x * f (path x)) -
      (∑ x, weight x * iteratedCircleAverage A is f (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  classical
  let keep : J → Prop := fun j => ∀ i ∈ is, n j i = 0
  let full : X → ℂ := fun x => ∑ j, v j x
  let retained : X → ℂ := fun x => ∑ j, if keep j then v j x else 0
  have hsum (x : X) : iteratedCircleAverage A is full x = retained x := by
    rw [iteratedCircleAverage_sum A is Finset.univ v Lv (fun j _ => hv j)]
    apply Finset.sum_congr rfl
    intro j _
    rw [iteratedCircleAverage_eigenfunction A is (n j) (v j) (heigen j)]
    dsimp only [keep]
    split_ifs <;> rfl
  have htested (a b : X → ℂ) (hab : ∀ x, ‖a x - b x‖ ≤ rho) :
      ‖(∑ x, weight x * a (path x)) - (∑ x, weight x * b (path x))‖ ≤ B * rho := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x, ‖weight x * a (path x) - weight x * b (path x)‖ := norm_sum_le _ _
      _ ≤ ∑ x, ‖weight x‖ * rho := by
        apply Finset.sum_le_sum
        intro x _
        rw [← mul_sub, norm_mul]
        exact mul_le_mul_of_nonneg_left (hab (path x)) (norm_nonneg _)
      _ = (∑ x, ‖weight x‖) * rho := (Finset.sum_mul ..).symm
      _ ≤ B * rho := mul_le_mul_of_nonneg_right hmass hrho
  have hfirst := htested f full happrox
  have hlast := htested retained (iteratedCircleAverage A is f) (fun x => by
    rw [← hsum, norm_sub_rev]
    exact iteratedCircleAverage_sub_norm_le A is hf (lipschitz_finite_complex_sum v Lv hv)
      happrox x)
  have hid : (∑ x, weight x * full (path x)) - (∑ x, weight x * retained (path x)) =
      ∑ j, if keep j then 0 else ∑ x, weight x * v j (path x) := by
    simp only [full, retained, Finset.mul_sum]
    rw [Finset.sum_comm, Finset.sum_comm (f := fun x j => weight x * if keep j then v j (path x) else 0),
      ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : keep j <;> simp [hj]
  have hmiddle : ‖(∑ x, weight x * full (path x)) - (∑ x, weight x * retained (path x))‖ ≤
      Fintype.card J * tau := by
    rw [hid]
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _j : J, tau := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hj : keep j
        · simpa only [hj, ite_true, norm_zero] using htau
        · simpa only [hj, ite_false] using hdiscard j hj
      _ = _ := by simp
  have htri := norm_sub_le_norm_sub_add_norm_sub
    (∑ x, weight x * f (path x)) (∑ x, weight x * full (path x))
    (∑ x, weight x * iteratedCircleAverage A is f (path x))
  have htri' := norm_sub_le_norm_sub_add_norm_sub
    (∑ x, weight x * full (path x)) (∑ x, weight x * retained (path x))
    (∑ x, weight x * iteratedCircleAverage A is f (path x))
  linarith

end CircleFourier
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalCentralCircle
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem exists_centralRationalCircle_frequency (v : L) (hv : v ∈ D.filtration.layer s)
    (eta : L →ₗ[ℚ] ℚ) (f : D.Space → ℂ)
    (hf : ∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → ∀ x,
      f (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * f x) :
    let := D.metricSpace
    ∃ n : ℤ,
      (∀ t x, f ((D.centralRationalCircle v hv).act t x) = character (n • t) * f x) ∧
      (eta v = 0 → n = 0) := by
  classical
  let := D.metricSpace
  by_cases hz : ∀ x, f x = 0
  · exact ⟨0, fun t x => by simp [hz], fun _ => rfl⟩
  push Not at hz
  obtain ⟨n, hn⟩ := vertical_frequency_integral_on_lattice D.filtration D.realLattice eta f hf hz
    (⟨D.periodicRealDirection v⟩ : D.RealGroup)
    (D.periodicRealDirection_mem_top v hv) (D.periodicRealDirection_mem_lattice v)
  refine ⟨n, ?_, ?_⟩
  · intro t x
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    rw [D.centralRationalCircle_act_coe]
    have hr : realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r ∈ D.filtration.realification.subgroup s := by
      change r • D.periodicRealDirection v ∈ D.filtration.realLayer s
      exact (D.filtration.realLayer s).smul_mem r (D.periodicRealDirection_mem_top v hv)
    rw [hf _ hr]
    apply congrArg (fun z : CircleFourier.Circle => character z * f x)
    change ((realifyFunctional eta (r • D.periodicRealDirection v) : ℝ) : CircleFourier.Circle) =
      n • (r : CircleFourier.Circle)
    rw [map_smul, hn, ← AddCircle.coe_zsmul]
    congr 1
    simp only [smul_eq_mul, zsmul_eq_mul, mul_comm]
  · intro heta
    have hzero : realifyFunctional eta (D.periodicRealDirection v) = 0 := by
      simp [periodicRealDirection, realifyFunctional_tmul, heta]
    have hn0 : (n : ℝ) = 0 := hn.symm.trans hzero
    exact_mod_cast hn0

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestProbabilityProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem averageCircles_orbit (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α) :
    (T.averageCircles A is).orbit = T.orbit := rfl

theorem averageCircles_complexity (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    {p : ℝ} (hT : T.ComplexityLE p) : (T.averageCircles A is).ComplexityLE p := hT

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators NNReal

variable {σ α L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem averageCircles_weighted_error (T : D.Niltest w)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    {J G : Type*} [Fintype J] [Fintype G] (U : J → D.Niltest w) (n : J → α → ℤ)
    (horbit : ∀ j, (U j).orbit = T.orbit) (path : G → σ → ℤ) (weight : G → ℂ)
    {B rho tau : ℝ} (hmass : (∑ x, ‖weight x‖) ≤ B) (hrho : 0 ≤ rho) (htau : 0 ≤ tau)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hdiscard : ∀ j, ¬ (∀ i ∈ is, n j i = 0) →
      ‖∑ x, weight x * (U j).eval (path x)‖ ≤ tau) :
    ‖(∑ x, weight x * T.eval (path x)) -
      (∑ x, weight x * (T.averageCircles A is).eval (path x))‖ ≤
      2 * B * rho + Fintype.card J * tau := by
  let := D.metricSpace
  let orbitPath : G → D.Space := fun x =>
    QuotientGroup.mk (D.filtration.realification.polynomialOrbitEval w (path x) T.orbit)
  have heval (j : J) (x : G) :
      (U j).observable (orbitPath x) = (U j).eval (path x) := by
    change (U j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval w (path x) T.orbit)) =
      (U j).observable (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval w (path x) (U j).orbit))
    rw [horbit j]
  have hdiscard' (j : J) (hj : ¬ (∀ i ∈ is, n j i = 0)) :
      ‖∑ x, weight x * (U j).observable (orbitPath x)‖ ≤ tau := by
    simpa only [heval] using hdiscard j hj
  exact iteratedCircleAverage_weighted_error A is T.observable (fun j => (U j).observable)
    n orbitPath weight T.lipBound (fun j => (U j).lipBound) T.lipschitz
    (fun j => (U j).lipschitz) hmass hrho htau happrox heigen hdiscard'

theorem exists_positive_circle_projection_family (T : D.Niltest w)
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (A : let := D.metricSpace; α → IsometricCircleAction D.Space) (is : List α)
    (hcomm : let := D.metricSpace; ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j))
    {J β : Type*} {G : β → Type*} [Fintype J] [∀ a, Fintype (G a)]
    (U : J → D.Niltest w) (n : J → α → ℤ) (horbit : ∀ j, (U j).orbit = T.orbit)
    (path : ∀ a, G a → σ → ℤ) (weight : ∀ a, G a → ℂ) (B tau : β → ℝ)
    {rho : ℝ} (hmass : ∀ a, (∑ x, ‖weight a x‖) ≤ B a)
    (hrho : 0 ≤ rho) (htau : ∀ a, 0 ≤ tau a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (heigen : let := D.metricSpace; ∀ j i, i ∈ is → ∀ t x,
      (U j).observable ((A i).act t x) = character (n j i • t) * (U j).observable x)
    (hsignificant : ∀ j, (∃ a, tau a < ‖∑ x, weight a x * (U j).eval (path a x)‖) →
      ∀ i ∈ is, n j i = 0) :
    let := D.metricSpace
    ∃ S : D.Niltest w, S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ i ∈ is, ∀ t x, S.observable ((A i).act t x) = S.observable x) ∧
      ∀ a, ‖(∑ x, weight a x * T.eval (path a x)) -
        (∑ x, weight a x * S.eval (path a x))‖ ≤
          2 * B a * rho + Fintype.card J * tau a := by
  let := D.metricSpace
  refine ⟨T.averageCircles A is, T.averageCircles_unit_interval A is hT,
    T.averageCircles_complexity A is hTc, T.averageCircles_orbit A is, ?_, ?_⟩
  · intro i hi t x
    exact T.averageCircles_invariant A is hcomm i hi t x
  · intro a
    apply T.averageCircles_weighted_error A is U n horbit (path a) (weight a)
      (hmass a) hrho (htau a) happrox heigen
    intro j hj
    exact le_of_not_gt (fun h => hj (hsignificant j ⟨a, h⟩))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_positive_kernel_projection_family (T : D.Niltest w)
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {J β : Type*} {G : β → Type*} [Fintype J] [∀ a, Fintype (G a)]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (path : ∀ a, G a → σ → ℤ) (weight : ∀ a, G a → ℂ) (B tau : β → ℝ)
    {rho : ℝ} (hmass : ∀ a, (∑ x, ‖weight a x‖) ≤ B a)
    (hrho : 0 ≤ rho) (htau : ∀ a, 0 ≤ tau a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hkill : ∀ j, (∃ a, tau a < ‖∑ x, weight a x * (U j).eval (path a x)‖) →
      ∀ v ∈ K, eta j v = 0) :
    ∃ S : D.Niltest w, S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ K.baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ∀ a, ‖(∑ x, weight a x * T.eval (path a x)) -
        (∑ x, weight a x * S.eval (path a x))‖ ≤
          2 * B a * rho + Fintype.card J * tau a := by
  classical
  let := D.metricSpace
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let b := Module.finBasis ℚ K
  let v : Fin (finrank ℚ K) → L := fun i => b i
  have hv (i : Fin (finrank ℚ K)) : v i ∈ D.filtration.layer s := hK (b i).property
  let A : Fin (finrank ℚ K) → IsometricCircleAction D.Space :=
    fun i => D.centralRationalCircle (v i) (hv i)
  have hfreq (j : J) (i : Fin (finrank ℚ K)) : ∃ n : ℤ,
      (∀ t x, (U j).observable ((A i).act t x) = character (n • t) * (U j).observable x) ∧
      (eta j (v i) = 0 → n = 0) :=
    D.exists_centralRationalCircle_frequency (v i) (hv i) (eta j) (U j).observable (hvertical j)
  choose n heigen hzero using hfreq
  let is := List.finRange (finrank ℚ K)
  have hcomm : ∀ i ∈ is, ∀ j ∈ is, (A i).Commutes (A j) :=
    fun i _ j _ => D.centralRationalCircle_commutes (v i) (v j) (hv i) (hv j)
  have hsignificant (j : J)
      (hj : ∃ a, tau a < ‖∑ x, weight a x * (U j).eval (path a x)‖) :
      ∀ i ∈ is, n j i = 0 := by
    intro i _
    exact hzero j i (hkill j hj (v i) (b i).property)
  obtain ⟨S, hS, hSc, hSo, hSinv, herror⟩ := T.exists_positive_circle_projection_family hT hTc
    A is hcomm U n horbit path weight B tau hmass hrho htau happrox
    (fun j i _ => heigen j i) hsignificant
  refine ⟨S, hS, hSc, hSo, ?_, herror⟩
  intro z hz x
  exact D.invariant_of_kernel_circles K hK b S.observable
    (fun i t y => hSinv i (by simp [is]) t y) z hz x

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem exists_probability_kernel_projection_family (T : D.Niltest w)
    (hT : T.UnitIntervalValued) {p : ℝ} (hTc : T.ComplexityLE p)
    (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {J β : Type*} {G : β → Type*} [Fintype J] [∀ a, Fintype (G a)]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (law : ∀ a, FiniteProbabilityWeights (G a)) (path : ∀ a, G a → σ → ℤ)
    (tau : β → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (htau : ∀ a, 0 ≤ tau a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hkill : ∀ j, (∃ a, tau a < ‖(law a).complexMean (fun x => (U j).eval (path a x))‖) →
      ∀ v ∈ K, eta j v = 0) :
    ∃ S : D.Niltest w, S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ K.baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ∀ a, ‖(law a).complexMean (fun x => T.eval (path a x)) -
        (law a).complexMean (fun x => S.eval (path a x))‖ ≤
          2 * rho + Fintype.card J * tau a := by
  have hmass (a : β) : (∑ x, ‖((law a).weight x : ℂ)‖) ≤ 1 := by
    have hnorm (x : G a) : ‖((law a).weight x : ℂ)‖ = (law a).weight x := by
      rw [Complex.norm_real, Real.norm_of_nonneg ((law a).nonneg x)]
    simp_rw [hnorm]
    exact (law a).total.le
  simpa only [FiniteProbabilityWeights.complexMean, mul_one] using
    T.exists_positive_kernel_projection_family hT hTc K hK eta U horbit hvertical path
      (fun a x => ((law a).weight x : ℂ)) (fun _ => 1) tau hmass hrho htau happrox hkill

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_log (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).orbit.log =
      weightedDilation (fun _ => 1) r (VectorPolynomial.translate shift T.orbit.log) :=
  substitute_scalarAffinePolynomial r shift T.orbit.log

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_eq_of_orbit_eq (T U : D.Niltest w) (h : T.orbit = U.orbit)
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    T.symbol b ω hF = U.symbol b ω hF := by
  unfold symbol
  apply congrArg (D.filtration.realPolynomialSymbolHom b ω hF w)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : D.filtration.realification.PolynomialOrbit w => o.log) h

theorem affinePullback_orbit_eq_of_orbit_eq [Fintype τ]
    (T U : D.Niltest (fun _ : σ => 1)) (h : T.orbit = U.orbit)
    (A : σ → τ → ℤ) (b : σ → ℤ) :
    (T.affinePullback A b).orbit = (U.affinePullback A b).orbit := by
  change D.filtration.realification.polynomialOrbitSubstitute _ _ T.orbit =
    D.filtration.realification.polynomialOrbitSubstitute _ _ U.orbit
  rw [h]

theorem exists_affine_finset_kernel_projection_family [Fintype τ]
    (T : D.Niltest (fun _ : σ => 1)) (hT : T.UnitIntervalValued)
    {p : ℝ} (hTc : T.ComplexityLE p) (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {J β : Type*} [Fintype J]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : σ => 1))
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (A : β → σ → τ → ℤ) (b : β → σ → ℤ)
    (boxes : β → Finset (τ → ℤ)) (hboxes : ∀ a, (boxes a).Nonempty)
    (threshold : β → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hthreshold : ∀ a, 0 ≤ threshold a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hkill : ∀ j, (∃ a, threshold a <
      ‖𝔼 x ∈ boxes a, ((U j).affinePullback (A a) (b a)).eval x‖) →
      ∀ v ∈ K, eta j v = 0) :
    ∃ S : D.Niltest (fun _ : σ => 1),
      S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ K.baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ∀ a, ‖(𝔼 x ∈ boxes a, (T.affinePullback (A a) (b a)).eval x) -
        (𝔼 x ∈ boxes a, (S.affinePullback (A a) (b a)).eval x)‖ ≤
          2 * rho + Fintype.card J * threshold a := by
  let law (a : β) := FiniteProbabilityWeights.uniformFinset (boxes a) (hboxes a)
  let path (a : β) (x : ↥(boxes a)) := integerAffineMap (A a) (b a) x.val
  have hmean (a : β) (F : D.Niltest (fun _ : σ => 1)) :
      (law a).complexMean (fun x => F.eval (path a x)) =
        𝔼 x ∈ boxes a, (F.affinePullback (A a) (b a)).eval x := by
    simpa only [law, path, eval_affinePullback] using
      FiniteProbabilityWeights.uniformFinset_complexMean (boxes a) (hboxes a)
        (fun x => F.eval (integerAffineMap (A a) (b a) x))
  have hkill' : ∀ j, (∃ a, threshold a <
      ‖(law a).complexMean (fun x => (U j).eval (path a x))‖) →
      ∀ v ∈ K, eta j v = 0 := by
    intro j ⟨a, ha⟩ v hv
    apply hkill j ⟨a, ?_⟩ v hv
    simpa only [hmean] using ha
  obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ :=
    T.exists_probability_kernel_projection_family hT hTc K hK eta U horbit hvertical
      law path threshold hrho hthreshold happrox hkill'
  exact ⟨S, hS, hSc, hSo, hinv, fun a => by simpa only [hmean] using herr a⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalBoxPartition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem comparableBoxPartitions_step {I : Type*} (N H : I → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i) (i : I)
    (k : (comparableBoxPartitions N H hH hHN i).Label) :
    (comparableBoxPartitions N H hH hHN i).step k = 1 := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonStrideResidueGeometry
namespace OAI

section

namespace Erdos3

theorem commonStridePoint_index_of_modEq {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) :
    commonStridePoint c m (commonStrideIndex c m y) = y := by
  funext i
  have hd := Int.modEq_iff_dvd.mp (hy i).symm
  change c i + (m : ℤ) * ((y i - c i) / (m : ℤ)) = y i
  rw [mul_comm, Int.ediv_mul_cancel hd]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AuxiliaryStrideGeometry
namespace OAI

section

namespace Erdos3

theorem mem_boxAuxiliaryCell_iff {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (x : IntegerResidueBox a (fun i => a i + N i) r b) :
    x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k ↔
      ∀ i, (intervalCellLower (a i) (P i) (k i).1 ≤ (x i).val ∧
        (x i).val < intervalCellUpper (a i) (P i) (k i).1) ∧
        (x i).val ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)] := by
  simp only [mem_partitionCell, boxAuxiliaryCell, funext_iff]
  apply forall_congr'
  intro i
  exact intervalAuxiliaryCell_eq_iff (a i) (P i) (hstep i) (M i) (d i) (hd i)
    (u i) (r i) (b i) (hbase i) (x i) (k i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

theorem integerAffineMap_residueStepMatrix {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (J : I → ℕ) (x : I → ℤ) :
    integerAffineMap (residueStepMatrix J) a x = fun i => a i + (J i : ℤ) * x i :=
  integerAffineMap_diagonal a (fun i => (J i : ℤ)) x

theorem commonStrideIndex_residue_affine {I : Type*} (u v : I → ℤ) {M : ℕ} (hM : 0 < M)
    (J : I → ℕ) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (x : I → ℤ) :
    commonStrideIndex u M (fun i => v i + ((M * J i : ℕ) : ℤ) * x i) =
      fun i => commonStrideIndex u M v i + (J i : ℤ) * x i := by
  have heq : commonStridePoint u M (fun i => commonStrideIndex u M v i + (J i : ℤ) * x i) =
      (fun i => v i + ((M * J i : ℕ) : ℤ) * x i) := by
    funext i
    have hbase := congrFun (commonStridePoint_index_of_modEq u M v hv) i
    change u i + (M : ℤ) * commonStrideIndex u M v i = v i at hbase
    change u i + (M : ℤ) * (commonStrideIndex u M v i + (J i : ℤ) * x i) = _
    calc
      _ = (u i + (M : ℤ) * commonStrideIndex u M v i) + ((M * J i : ℕ) : ℤ) * x i := by
        push_cast
        ring
      _ = _ := by rw [hbase]
  rw [← heq, commonStrideIndex_point u hM]

theorem residueBoxStride_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a b : I → ℤ) (M : ℕ) (hM : 0 < M) (u v : I → ℤ) (J : I → ℕ)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (f : (I → ℤ) → ℂ) :
    (𝔼 x : IntegerResidueBox a b (fun i => (M * J i : ℕ)) v, residueBoxStrideValue f u M x) =
      𝔼 x ∈ translatedIntegerBox
        (fun i => residueIndexLower (a i) (M * J i : ℕ) (v i))
        (fun i => residueIndexLength (a i) (b i) (M * J i : ℕ) (v i)),
        f (fun i => commonStrideIndex u M v i + (J i : ℤ) * x i) := by
  change (𝔼 x : IntegerResidueBox a b (fun i => (M * J i : ℕ)) v,
    f (commonStrideIndex u M (fun i => (x i).val))) = _
  rw [integerResidueBox_expect a b (fun i => (M * J i : ℕ)) v
    (fun i => by exact_mod_cast Nat.mul_pos hM (hJ i)) (fun y => f (commonStrideIndex u M y))]
  apply Finset.expect_congr rfl
  intro x _
  exact congrArg f (commonStrideIndex_residue_affine u v hM J hv x)

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

theorem residueBoxStride_mean (T : D.Niltest (fun _ : σ => 1))
    (a b : σ → ℤ) (M : ℕ) (hM : 0 < M) (u v : σ → ℤ) (J : σ → ℕ)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) :
    (𝔼 x : IntegerResidueBox a b (fun i => (M * J i : ℕ)) v, residueBoxStrideValue T.eval u M x) =
      𝔼 x ∈ translatedIntegerBox
        (fun i => residueIndexLower (a i) (M * J i : ℕ) (v i))
        (fun i => residueIndexLength (a i) (b i) (M * J i : ℕ) (v i)),
        (T.affinePullback (residueStepMatrix J) (commonStrideIndex u M v)).eval x := by
  rw [residueBoxStride_expect a b M hM u v J hJ hv]
  apply Finset.expect_congr rfl
  intro x _
  rw [eval_affinePullback, integerAffineMap_residueStepMatrix]

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem commonStrideIndex_of_refinement {σ : Type*}
    (u v : σ → ℤ) {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (x : σ → ℤ) :
    commonStrideIndex u M (commonStridePoint v N x) =
      fun i => ((N / M : ℕ) : ℤ) * x i + commonStrideIndex u M v i := by
  change commonStrideIndex u M (fun i => v i + (N : ℤ) * x i) = _
  have h := commonStrideIndex_residue_affine u v hM (fun _ : σ => N / M) hv x
  simpa only [Nat.mul_div_cancel' hMN, add_comm] using h

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem eval_commonStride_rebase (T : D.Niltest (fun _ : σ => 1))
    (u v : σ → ℤ) {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (x : σ → ℤ)
    (hx : ∀ i, x i ≡ v i [ZMOD (N : ℤ)]) :
    T.eval (commonStrideIndex u M x) =
      (T.scalarAffinePullback (N / M : ℕ) (fun i => (commonStrideIndex u M v i : ℚ))).eval
        (commonStrideIndex v N x) := by
  have hindex := commonStrideIndex_of_refinement u v hM hMN hv (commonStrideIndex v N x)
  rw [commonStridePoint_index_of_modEq v N x hx] at hindex
  have heval := T.scalarAffinePullback_eval_integer ((N / M : ℕ) : ℤ)
    (commonStrideIndex u M v) (commonStrideIndex v N x)
  calc
    T.eval (commonStrideIndex u M x) =
        T.eval (fun i => ((N / M : ℕ) : ℤ) * commonStrideIndex v N x i + commonStrideIndex u M v i) :=
      congrArg T.eval hindex
    _ = _ := by simpa only [Int.cast_natCast] using heval.symm

theorem residueBoxStride_rebase [Fintype σ] [DecidableEq σ]
    (T : D.Niltest (fun _ : σ => 1)) (lo hi r z u v : σ → ℤ)
    {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hz : ∀ i (x : ℤ), x ≡ z i [ZMOD r i] → x ≡ v i [ZMOD (N : ℤ)]) :
    (𝔼 x : IntegerResidueBox lo hi r z, residueBoxStrideValue T.eval u M x) =
      𝔼 x : IntegerResidueBox lo hi r z,
        residueBoxStrideValue
          (T.scalarAffinePullback (N / M : ℕ) (fun i => (commonStrideIndex u M v i : ℚ))).eval v N x := by
  apply Finset.expect_congr rfl
  intro x _
  exact T.eval_commonStride_rebase u v hM hMN hv (fun i => (x i).val)
    (fun i => hz i (x i).val (Finset.mem_filter.mp (x i).property).2)

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineResidueDescent
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

theorem scalarAffinePolynomial_integer {σ : Type*} (a : ℤ) (shift : σ → ℤ) (i : σ) :
    scalarAffinePolynomial (a : ℚ) (fun j => (shift j : ℚ)) i ∈ integerCoefficientPolynomials σ := by
  exact (integerCoefficientPolynomials σ).add_mem (integerCoefficientPolynomials_C (shift i))
    ((integerCoefficientPolynomials σ).mul_mem (integerCoefficientPolynomials_C a)
      (integerCoefficientPolynomials_X i))

theorem scalarAffine_monomial_integer_coefficients {σ : Type*}
    (a : ℤ) (shift : σ → ℤ) (α β : σ →₀ ℕ) :
    ∃ z : ℤ, (MvPolynomial.aeval (R := ℚ)
      (scalarAffinePolynomial (a : ℚ) (fun i => (shift i : ℚ))) (monomial β 1)).coeff α =
        (z : ℚ) := by
  apply (mem_integerCoefficientPolynomials_iff _).mp ?_ α
  apply integerPolynomialHom_preserves
    (MvPolynomial.aeval (R := ℚ) (scalarAffinePolynomial (a : ℚ) (fun i => (shift i : ℚ))))
  · intro i
    simpa only [aeval_X] using scalarAffinePolynomial_integer a shift i
  · refine ⟨monomial β (1 : ℤ), ?_⟩
    simp

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

theorem scalarAffineAdaptedHom_coord {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ)
    (g : (F.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) :
    ((F.scalarAffineAdaptedHom r h g).coord : VectorPolynomial σ ℚ L) =
      weightedDilation (fun _ : σ => 1) r (translate h (g.coord : VectorPolynomial σ ℚ L)) := by
  change substitute (scalarAffinePolynomial r h) (g.coord : VectorPolynomial σ ℚ L) = _
  exact substitute_scalarAffinePolynomial r h _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem polynomialRationalGrid_scalarAffine_integer {σ ι L : Type*}
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (q : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (hg : F.PolynomialRationalGrid b (fun _ : σ => 1) q g)
    (a : ℤ) (shift : σ → ℤ) :
    F.PolynomialRationalGrid b (fun _ : σ => 1) q
      (F.realification.scalarAffineAdaptedHom (a : ℚ) (fun i => (shift i : ℚ)) g) := by
  classical
  obtain ⟨u, hu⟩ := hg
  choose c hc using fun α β => scalarAffine_monomial_integer_coefficients a shift α β
  refine ⟨fun z => ∑ β ∈ (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).support,
    c z.1 β * u (β, z.2), ?_⟩
  funext z
  change ((∑ β ∈ (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))).support,
    c z.1 β * u (β, z.2) : ℤ) : ℝ) = (q : ℝ) * (b.baseChange ℝ).repr
      (coefficients ((F.realification.scalarAffineAdaptedHom (a : ℚ)
        (fun i => (shift i : ℚ)) g).coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2
  rw [scalarAffineAdaptedHom_coord, ← substitute_scalarAffinePolynomial, coefficients_substitute]
  simp only [Int.cast_sum, Int.cast_mul, map_sum, Finsupp.finsetSum_apply,
    map_rat_smul, Finsupp.smul_apply, Rat.smul_def, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  rw [hc z.1 β]
  have hβ := congrFun hu (β, z.2)
  change (u (β, z.2) : ℝ) = (q : ℝ) * (b.baseChange ℝ).repr
    (coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) β) z.2 at hβ
  rw [hβ]
  push_cast
  ring

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem scalarAffineAdaptedHom_constant {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (r : ℚ) (h : σ → ℚ) (κ : F.Group) :
    F.scalarAffineAdaptedHom r h (F.adaptedConstantGroupHom (fun _ : σ => 1) κ) =
      F.adaptedConstantGroupHom (fun _ : σ => 1) κ := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change substitute (scalarAffinePolynomial r h) (monomial 0 κ.coord) = monomial 0 κ.coord
  simp [monomial]

end NilpotentLieFiltration

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_normalized_factorization (S : D.Niltest (fun _ : σ => 1))
    (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
    (κ : D.RealGroup)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
      ⟨⟨S.orbit.log, S.orbit.property⟩⟩)
    (r : ℚ) (h : σ → ℚ) :
    D.filtration.realification.scalarAffineAdaptedHom r h E *
      D.filtration.realification.scalarAffineAdaptedHom r h b *
      D.filtration.realification.scalarAffineAdaptedHom r h R *
      D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨(S.scalarAffinePullback r h).orbit.log, (S.scalarAffinePullback r h).orbit.property⟩⟩ := by
  have heq := congrArg (D.filtration.realification.scalarAffineAdaptedHom r h) hprod
  simp only [map_mul, NilpotentLieFiltration.scalarAffineAdaptedHom_constant] at heq
  refine heq.trans ?_
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  rw [NilpotentLieFiltration.scalarAffineAdaptedHom_coord]
  exact (S.scalarAffinePullback_log r h).symm

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AuxiliaryCellMeans
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem boxAuxiliaryCell_expect {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (P : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (P i).step k = 1) (hpos : ∀ i k, 0 < (P i).length k)
    (M d : I → ℕ) (hd : ∀ i, 0 < d i) (u r b : I → ℤ)
    (hbase : ∀ i (x : ℤ), x ≡ b i [ZMOD r i] → x ≡ u i [ZMOD (M i : ℤ)])
    (k : AuxiliaryBoxLabels P M d u) (R c : I → ℤ)
    (hcombine : ∀ i (x : ℤ),
      (x ≡ b i [ZMOD r i] ∧ x ≡ ((k i).2.val.val : ℤ) [ZMOD (d i : ℤ)]) ↔ x ≡ c i [ZMOD R i])
    (f : (I → ℤ) → ℂ) :
    (𝔼 x ∈ partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k,
      f (fun i => (x i).val)) =
      𝔼 x : IntegerResidueBox (fun i => intervalCellLower (a i) (P i) (k i).1)
        (fun i => intervalCellUpper (a i) (P i) (k i).1) R c,
        f (fun i => (x i).val) := by
  let B := partitionCell (boxAuxiliaryCell a N P M d hd u r b hbase) k
  let g : IntegerResidueBox a (fun i => a i + N i) r b → ℂ := fun x => f (fun i => (x i).val)
  have he := Fintype.expect_equiv (boxAuxiliaryCellEquiv a N P hstep hpos M d hd u r b hbase k R c hcombine)
    (fun x => g x.val) (fun x => f (fun i => (x i).val)) (fun _ => rfl)
  have hcoe : (𝔼 x : ↥B, g x.val) = 𝔼 x ∈ B, g x := by
    rw [Fintype.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card,
      Fintype.card_coe, Finset.sum_coe_sort]
  exact hcoe.symm.trans he

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TranslatedStabilityStep
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem gradedFast_finrank_inf_lt (V U : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ)
    (hU : ∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF eta x = 0)
    (hV : ∃ x ∈ V, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x ∧
      F.gradedFrequency b ω hF eta x ≠ 0) :
    finrank ℚ ↥(V ⊓ U) < finrank ℚ V := by
  let : FiniteDimensional ℚ F.AssociatedGraded :=
    (F.associatedGradedBasis b ω hF).finiteDimensional_of_finite
  change finrank ℚ ↥(V.toSubmodule ⊓ U.toSubmodule) < finrank ℚ V.toSubmodule
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne inf_le_left ?_
  intro heq
  obtain ⟨x, hx, hgrade, hnonzero⟩ := hV
  have hxinf : x ∈ V.toSubmodule ⊓ U.toSubmodule := heq.symm ▸ hx
  exact hnonzero (hU x hxinf.2 hgrade)

omit [Fintype ι] in
theorem exists_graded_top_frequency_ne_zero (V : LieSubalgebra ℚ F.AssociatedGraded)
    (eta : L →ₗ[ℚ] ℚ) (hV : ∃ x ∈ F.gradedRefiltrationLayer V s, eta x ≠ 0) :
    ∃ x ∈ V, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x ∧
      F.gradedFrequency b ω hF eta x ≠ 0 := by
  obtain ⟨v, hv, hne⟩ := hV
  obtain ⟨hvs, hvV⟩ := (F.mem_gradedRefiltrationLayer V s v).mp hv
  refine ⟨F.associatedGradedPieceMap s ⟨v, hvs⟩, hvV,
    F.associatedGradedPieceMap_grade_fixed b ω hF s ⟨v, hvs⟩, ?_⟩
  simpa only [F.gradedFrequency_top_piece b ω hF eta] using hne

theorem ControlledSymbolFactorization.exists_dimension_drop
    {eta : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF eta T X p)
    (V : LieSubalgebra ℚ F.AssociatedGraded)
    (hV : ∃ x ∈ F.gradedRefiltrationLayer V s, eta x ≠ 0) :
    ∃ (l : ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded) (u : ι → F.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = U.toSubmodule ∧
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω U.toSubmodule ∧
      (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) ∧
      (∀ x ∈ U, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
        F.gradedFrequency b ω hF eta x = 0) ∧
      finrank ℚ ↥(V ⊓ U) < finrank ℚ V ∧ F.SymbolFactorizationIn b ω hF T X p l U := by
  obtain ⟨l, U, u, hl, hlp, hspan, hgraded, hheight, hkill, hfactor⟩ :=
    ControlledSymbolFactorization.exists_in F b ω hF h
  exact ⟨l, U, u, hl, hlp, hspan, hgraded, hheight, hkill,
    F.gradedFast_finrank_inf_lt b ω hF V U eta hkill
      (F.exists_graded_top_frequency_ne_zero b ω hF V eta hV), hfactor⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DescentPartitionLengths
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem roundedPartitionLength_bounds (N : ℕ) (ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (hlarge : 2 ≤ ρ * (N : ℝ)) :
    0 < ⌊ρ * (N : ℝ)⌋₊ ∧ ⌊ρ * (N : ℝ)⌋₊ ≤ N ∧
      ρ * (N : ℝ) / 2 ≤ (⌊ρ * (N : ℝ)⌋₊ : ℝ) ∧
      (⌊ρ * (N : ℝ)⌋₊ : ℝ) ≤ ρ * (N : ℝ) ∧
      ((N / ⌊ρ * (N : ℝ)⌋₊ : ℕ) : ℝ) ≤ 2 / ρ := by
  let H := ⌊ρ * (N : ℝ)⌋₊
  have hH : 0 < H := Nat.floor_pos.mpr (by linarith)
  have hHN : H ≤ N := Nat.floor_le_of_le (by
    nlinarith [Nat.cast_nonneg (α := ℝ) N])
  have hupper : (H : ℝ) ≤ ρ * (N : ℝ) := Nat.floor_le (by linarith)
  have hnext : ρ * (N : ℝ) < (H : ℝ) + 1 := Nat.lt_floor_add_one _
  have hlower : ρ * (N : ℝ) / 2 ≤ (H : ℝ) := by linarith
  have hHreal : 0 < (H : ℝ) := by exact_mod_cast hH
  have hquot : ((N / H : ℕ) : ℝ) * (H : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N H
  have hcount : ((N / H : ℕ) : ℝ) ≤ 2 / ρ := by
    calc
      ((N / H : ℕ) : ℝ) ≤ (N : ℝ) / (H : ℝ) :=
        (le_div_iff₀ hHreal).mpr hquot
      _ ≤ 2 / ρ := (div_le_div_iff₀ hHreal hρ).mpr (by nlinarith)
  exact ⟨hH, hHN, hlower, hupper, hcount⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_descent_partition_lengths {I : Type*} [Fintype I]
    (N : I → ℕ) (M : ℕ) (A : I → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (hsize : ∀ i, (N i : ℝ) ≤ 2 * (M : ℝ) * A i)
    (hlarge : ∀ i, 8 ≤ δ * (N i : ℝ))
    (R : I → ℝ) (hR : ∀ i, 0 ≤ R i) (ε : ℝ)
    (hcount : (∑ i, R i / (N i : ℝ)) ≤ δ * ε / 8) :
    ∃ H : I → ℕ, (∀ i, 0 < H i) ∧ (∀ i, H i ≤ N i) ∧
      (∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ)) ∧
      (∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4) ∧
      (∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ) ∧
      (∑ i, R i / (H i : ℝ)) ≤ ε := by
  let H : I → ℕ := fun i => ⌊(δ / 4) * (N i : ℝ)⌋₊
  have hround (i : I) := roundedPartitionLength_bounds (N i) (δ / 4)
    (by positivity) (by linarith) (by nlinarith [hlarge i])
  have hH : ∀ i, 0 < H i := fun i => (hround i).1
  have hHN : ∀ i, H i ≤ N i := fun i => (hround i).2.1
  have hlo : ∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ) := by
    intro i
    have h := (hround i).2.2.1
    change (δ / 4) * (N i : ℝ) / 2 ≤ (H i : ℝ) at h
    nlinarith
  have hhi : ∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4 := by
    intro i
    have h := (hround i).2.2.2.1
    change (H i : ℝ) ≤ (δ / 4) * (N i : ℝ) at h
    nlinarith
  have hfreeze : ∀ i, 2 * (H i : ℝ) ≤ (M : ℝ) * A i * δ := by
    intro i
    calc
      2 * (H i : ℝ) ≤ δ * (N i : ℝ) / 2 := by nlinarith [hhi i]
      _ ≤ δ * (2 * (M : ℝ) * A i) / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hsize i) hδ.le) (by norm_num)
      _ = _ := by ring
  have hratio (i : I) : R i / (H i : ℝ) ≤ (8 / δ) * (R i / (N i : ℝ)) := by
    have hN : 0 < (N i : ℝ) := by nlinarith [hlarge i, Nat.cast_nonneg (α := ℝ) (N i)]
    calc
      R i / (H i : ℝ) ≤ R i / (δ * (N i : ℝ) / 8) :=
        div_le_div_of_nonneg_left (hR i) (by positivity) (hlo i)
      _ = _ := by field_simp
  refine ⟨H, hH, hHN, hlo, hhi, hfreeze, ?_⟩
  calc
    (∑ i, R i / (H i : ℝ)) ≤ ∑ i, (8 / δ) * (R i / (N i : ℝ)) :=
      Finset.sum_le_sum (fun i _ => hratio i)
    _ = (8 / δ) * ∑ i, R i / (N i : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ (8 / δ) * (δ * ε / 8) := mul_le_mul_of_nonneg_left hcount (by positivity)
    _ = ε := by field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.HalfResidueDescent
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

theorem FixedResidueDescent.half_discrepancy
    {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    {D : RationalFilteredNilmanifold L s d}
    {W : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    {V : RationalFilteredNilmanifold K t e} {w : σ → ℕ}
    {b : (D.filtration.realification.adaptedPolynomialFiltration w).Group}
    {child : V.filtration.realification.PolynomialOrbit w}
    {p cost : ℝ} {q P C a : ℕ} {hP : 0 < P}
    (hdesc : FixedResidueDescent D W V w b child p q P hP C a cost)
    (S : D.Niltest w) (hS : S.ComplexityLE p) (hunit : S.UnitIntervalValued)
    (hinvariant : ∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W s →
      ∀ x, S.observable (z • x) = S.observable x)
    (E R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
    (κ : D.RealGroup) (hκ : κ ∈ D.realLattice)
    (hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom w κ =
      ⟨⟨S.orbit.log, S.orbit.property⟩⟩)
    (hgrid : D.filtration.PolynomialRationalGrid D.basis w q R)
    (A : σ → ℝ) (hA : ∀ i, 0 < A i)
    (hE : D.filtration.PolynomialSlowBound D.basis w A (Real.exp ((p + 2) ^ a)) E)
    (M : ℕ) (hM : 0 < M) (lo : σ → ℤ) (N : σ → ℕ) (u v : σ → ℤ) (J : σ → ℕ)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hcop : ∀ i, (M * (M * P)).Coprime (J i)) (Δ ε δ : ℝ)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : ε < 1 / 2)
    (hprecision : 8 * ε + 2 * (Real.exp ((p + 2) ^ C) * δ) ≤ Δ / 2)
    (hlarge : ∀ i, 8 ≤ δ * (N i : ℝ))
    (hphysical : ∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
      (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i)
    (hcount : (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8)
    (hgap : Δ ≤
      ‖(𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u,
          residueBoxStrideValue S.eval u M x) -
        (𝔼 x : IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v,
          residueBoxStrideValue S.eval u M x)‖) :
    ∃ (H : σ → ℕ) (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i),
      (∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ)) ∧
      (∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4) ∧
      let Q := comparableBoxPartitions N H hH hHN
      let c₀ := baseAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u
      let c₁ := refinedAuxiliaryBoxCell lo N Q (fun _ => M) (fun _ => M * P) J
        (fun _ => Nat.mul_pos hM hP) u v hv
      ∃ k : AuxiliaryBoxLabels Q (fun _ => M) (fun _ => M * P) u,
        0 < (partitionCell c₀ k).card ∧ 0 < (partitionCell c₁ k).card ∧
        ∃ U : V.Niltest w, U.orbit = child ∧ U.UnitIntervalValued ∧ U.ComplexityLE cost ∧
          Δ / 2 ≤
            ‖(𝔼 x ∈ partitionCell c₀ k, residueBoxStrideValue U.eval u M x) -
              (𝔼 x ∈ partitionCell c₁ k, residueBoxStrideValue U.eval u M x)‖ := by
  have hsize : ∀ i, (N i : ℝ) ≤ 2 * (M : ℝ) * A i := by
    intro i
    linarith [(hphysical i).1, (hphysical i).2]
  obtain ⟨H, hH, hHN, hlo, hhi, hfreeze, hcounts⟩ := exists_descent_partition_lengths N M A δ hδ hδone
    hsize hlarge (fun i => ((Nat.lcm M (M * P) * J i : ℕ) : ℝ))
    (fun _ => Nat.cast_nonneg _) ε hcount
  refine ⟨H, hH, hHN, hlo, hhi, ?_⟩
  intro Q c₀ c₁
  obtain ⟨k, hk₀, hk₁, U, hU, hunitU, hcostU, hchild⟩ := hdesc S hS hunit hinvariant
    E R κ hκ hprod hgrid A hA hE M hM lo N H hH hHN u v J hJ hv hcop
    δ ε hδ.le hε hfreeze hphysical hcounts
  refine ⟨k, hk₀, hk₁, U, hU, hunitU, hcostU, ?_⟩
  linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueEventOrDescent
namespace OAI

section

namespace Erdos3

open Module CircleFourier NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_affine_stability_step (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ τ L : Type*} [Fintype τ] [DecidableEq τ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card τ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ (T : D.Niltest (fun _ : σ => 1)), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (V : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        {β : Type*} (A : β → σ → τ → ℤ) (b : β → σ → ℤ)
        (origin : β → τ → ℤ) (lengths : β → τ → ℕ),
      (∀ a i, 0 < lengths a i) →
      (∀ a i, Real.exp ((q + C) ^ C) ≤ (lengths a i : ℝ)) →
      (∃ (a : β) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
          (u : Fin d → D.filtration.AssociatedGraded),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        Submodule.span ℚ (Set.range u) = U.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
        (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (u i) j) ≤
          (q + C) ^ C) ∧
        finrank ℚ ↥(V ⊓ U) < finrank ℚ V ∧
        D.filtration.SymbolFactorizationIn D.basis ω hF (fun i => (lengths a i : ℝ))
          ((T.affinePullback (A a) (b a)).symbol D.basis ω hF) ((q + C) ^ C) l U) ∨
      (∃ S : D.Niltest (fun _ : σ => 1),
        S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ (D.filtration.gradedRefiltrationLayer V s).baseChange ℝ →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        ∀ a, ‖(𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
            (T.affinePullback (A a) (b a)).eval x) -
          (𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
            (S.affinePullback (A a) (b a)).eval x)‖ ≤
              2 * rho + Real.exp (verticalDecompositionBudget p - q)) := by
  classical
  obtain ⟨C, hC, hstep⟩ := exists_translated_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ τ L _ _ _ _ d _ _ _ _ D ω hF p q rho hp hpq hτ hfreq hrho hrhop
    T hunit hTc V β A b origin lengths hlength hlarge
  obtain ⟨J, inst, eta, U, hcard, hheight, hU, hvertical, _, _, happrox, _⟩ :=
    T.exists_controlled_vertical_decomposition hp hTc rho hrho hrhop
  let := inst
  let K := D.filtration.gradedRefiltrationLayer V s
  by_cases hevent : ∃ (j : J) (a : β),
      Real.exp (-q) < ‖𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
        ((U j).affinePullback (A a) (b a)).eval x‖ ∧ ∃ v ∈ K, eta j v ≠ 0
  · left
    obtain ⟨j, a, hbias, hnonzero⟩ := hevent
    have hfactor := hstep D ω hF q (hp.trans hpq) hτ ((U j).affinePullback (A a) (b a))
      ((hU j).1.mono hpq) (eta j) (fun i => (hheight j i).trans hfreq) (hvertical j)
      (origin a) (lengths a) (hlength a) (hlarge a) hbias.le
    have horbit := (U j).affinePullback_orbit_eq_of_orbit_eq T (hU j).2 (A a) (b a)
    have hsymbol := ((U j).affinePullback (A a) (b a)).symbol_eq_of_orbit_eq
      (T.affinePullback (A a) (b a)) horbit D.basis ω hF
    rw [hsymbol] at hfactor
    obtain ⟨l, W, u, hl, hlp, hspan, hgraded, hheightW, _hkill, hdim, hfixed⟩ :=
      ControlledSymbolFactorization.exists_dimension_drop D.filtration D.basis ω hF hfactor V hnonzero
    exact ⟨a, l, W, u, hl, hlp, hspan, hgraded, hheightW, hdim, hfixed⟩
  · right
    have hkill : ∀ j, (∃ a, Real.exp (-q) <
        ‖𝔼 x ∈ translatedIntegerBox (origin a) (lengths a),
          ((U j).affinePullback (A a) (b a)).eval x‖) →
        ∀ v ∈ K, eta j v = 0 := by
      intro j ⟨a, ha⟩ v hv
      by_contra hne
      exact hevent ⟨j, a, ha, v, hv, hne⟩
    have hboxes (a : β) : (translatedIntegerBox (origin a) (lengths a)).Nonempty := by
      refine ⟨origin a, (mem_translatedIntegerBox (origin a) (lengths a) (origin a)).mpr ?_⟩
      intro i
      have hi := hlength a i
      exact ⟨le_rfl, by omega⟩
    obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ := T.exists_affine_finset_kernel_projection_family
      hunit hTc K (D.filtration.gradedRefiltrationLayer_le V s) eta U (fun j => (hU j).2)
      hvertical A b (fun a => translatedIntegerBox (origin a) (lengths a)) hboxes
      (fun _ => Real.exp (-q)) hrho.le (fun _ => (Real.exp_pos _).le)
      (fun x => by simpa only [norm_sub_rev] using happrox x) hkill
    refine ⟨S, hS, hSc, hSo, hinv, ?_⟩
    intro a
    apply (herr a).trans
    apply add_le_add le_rfl
    calc
      (Fintype.card J : ℝ) * Real.exp (-q) ≤
          Real.exp (verticalDecompositionBudget p) * Real.exp (-q) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_pos _).le
      _ = Real.exp (verticalDecompositionBudget p - q) := by rw [← Real.exp_add, sub_eq_add_neg]

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_residue_law_stability_step (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (V : LieSubalgebra ℚ D.filtration.AssociatedGraded) {β : Type*}
        (lo hi : β → σ → ℤ) (M : β → ℕ) (u v : β → σ → ℤ) (J : β → σ → ℕ),
      (∀ a, 0 < M a) → (∀ a i, 0 < J a i) →
      (∀ a i, v a i ≡ u a i [ZMOD (M a : ℤ)]) →
      (∀ a i, ((M a * J a i : ℕ) : ℝ) * (Real.exp ((q + C) ^ C) + 1) ≤
        ((hi a i - lo a i : ℤ) : ℝ)) →
      let lawMean : D.Niltest (fun _ : σ => 1) → β → ℂ := fun F a =>
        𝔼 x : IntegerResidueBox (lo a) (hi a) (fun i => (M a * J a i : ℕ)) (v a),
          residueBoxStrideValue F.eval (u a) (M a) x
      (∃ (a : β) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
          (z : Fin d → D.filtration.AssociatedGraded),
        0 < l ∧ (l : ℝ) ≤ Real.exp ((q + C) ^ C) ∧
        Submodule.span ℚ (Set.range z) = U.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
        (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (z i) j) ≤
          (q + C) ^ C) ∧
        finrank ℚ ↥(V ⊓ U) < finrank ℚ V ∧
        D.filtration.SymbolFactorizationIn D.basis ω hF
          (fun i => (residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i) : ℝ))
          ((T.affinePullback (residueStepMatrix (J a)) (commonStrideIndex (u a) (M a) (v a))).symbol
            D.basis ω hF) ((q + C) ^ C) l U) ∨
      (∃ S : D.Niltest (fun _ : σ => 1),
        S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer V s →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        (∀ a, ‖lawMean T a - lawMean S a‖ ≤
          2 * rho + Real.exp (verticalDecompositionBudget p - q)) ∧
        ∀ a b, ‖lawMean T a - lawMean T b‖ -
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤
            ‖lawMean S a - lawMean S b‖) := by
  obtain ⟨C, hC, hstep⟩ := exists_affine_stability_step s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p q rho hp hpq hσ hfreq hrho hrhop
    T hunit hT V β lo hi M u v J hM hJ hv hlarge lawMean
  have hcounts : ∀ a i, Real.exp ((q + C) ^ C) ≤
      (residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i) : ℝ) := by
    intro a i
    exact residueIndexLength_ge_of_width (lo a i) (hi a i) (M a * J a i : ℕ) (v a i)
      (by exact_mod_cast Nat.mul_pos (hM a) (hJ a i)) _ (Real.exp_nonneg _) (by
        simpa only [Int.cast_natCast] using hlarge a i)
  have hpositive : ∀ a i, 0 < residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i) := by
    intro a i
    have h := (Real.exp_pos _).trans_le (hcounts a i)
    exact_mod_cast h
  let origin : β → σ → ℤ := fun a i => residueIndexLower (lo a i) (M a * J a i : ℕ) (v a i)
  let lengths : β → σ → ℕ := fun a i => residueIndexLength (lo a i) (hi a i) (M a * J a i : ℕ) (v a i)
  rcases hstep D ω hF p q rho hp hpq hσ hfreq hrho hrhop T hunit hT V
    (fun a => residueStepMatrix (J a)) (fun a => commonStrideIndex (u a) (M a) (v a))
    origin lengths hpositive hcounts with hevent | hprojection
  · exact Or.inl hevent
  · obtain ⟨S, hS, hSc, hSo, hinvariant, hmeans⟩ := hprojection
    have hm : ∀ a, ‖lawMean T a - lawMean S a‖ ≤
        2 * rho + Real.exp (verticalDecompositionBudget p - q) := by
      intro a
      dsimp only [lawMean]
      rw [T.residueBoxStride_mean (lo a) (hi a) (M a) (hM a) (u a) (v a) (J a) (hJ a) (hv a),
        S.residueBoxStride_mean (lo a) (hi a) (M a) (hM a) (u a) (v a) (J a) (hJ a) (hv a)]
      exact hmeans a
    refine Or.inr ⟨S, hS, hSc, hSo, hinvariant, hm, ?_⟩
    intro a b
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (lawMean T a) (lawMean S a) (lawMean T b)
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (lawMean S a) (lawMean S b) (lawMean T b)
    rw [norm_sub_rev (lawMean S b) (lawMean T b)] at h₂
    linarith [hm a, hm b]

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

theorem exists_residue_pair_stability_step (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p q rho : ℝ), 0 ≤ p → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (lo : σ → ℤ) (N : σ → ℕ)
        (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ),
      0 < M → (∀ i, 0 < J i) → (∀ i, v i ≡ u i [ZMOD (M : ℤ)]) →
      (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + C) ^ C) + 1) ≤ (N i : ℝ)) →
      let eta := 2 * rho + Real.exp (verticalDecompositionBudget p - q)
      ResiduePairDimensionDrop D ω hF T W lo N M u v J ((q + C) ^ C) ∨
      ∃ S : D.Niltest (fun _ : σ => 1),
        S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ D.filtration.realGradedRefiltrationLayer W s →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        (∀ flag, ‖residuePairMean T.eval lo N M u v J flag -
          residuePairMean S.eval lo N M u v J flag‖ ≤ eta) ∧
        ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ -
          2 * eta ≤
          ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ := by
  obtain ⟨C, hC, hstep⟩ := exists_residue_law_stability_step s hs
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF p q rho hp hpq hσ hfreq hrho hrhop
    T hunit hT W lo N M u v J hM hJ hv hlarge eta
  have hpositive : ∀ flag i, 0 < residuePairStep J flag i := by
    intro flag i
    cases flag
    · exact Nat.zero_lt_one
    · exact hJ i
  have hcompat : ∀ flag i, residuePairValue u v flag i ≡ u i [ZMOD (M : ℤ)] := by
    intro flag i
    cases flag
    · exact Int.ModEq.refl (u i)
    · exact hv i
  have hwidth : ∀ flag i, ((M * residuePairStep J flag i : ℕ) : ℝ) *
      (Real.exp ((q + C) ^ C) + 1) ≤ ((lo i + N i - lo i : ℤ) : ℝ) := by
    intro flag i
    simp only [add_sub_cancel_left, Int.cast_natCast]
    cases flag
    · change ((M * 1 : ℕ) : ℝ) * (Real.exp ((q + C) ^ C) + 1) ≤ (N i : ℝ)
      rw [Nat.mul_one]
      have hm : (M : ℝ) ≤ (M * J i : ℕ) := by exact_mod_cast Nat.le_mul_of_pos_right M (hJ i)
      exact (mul_le_mul_of_nonneg_right hm (by positivity)).trans (hlarge i)
    · exact hlarge i
  rcases hstep D ω hF p q rho hp hpq hσ hfreq hrho hrhop T hunit hT W
    (fun _ : Bool => lo) (fun _ i => lo i + N i) (fun _ => M) (fun _ => u)
    (residuePairValue u v) (residuePairStep J) (fun _ => hM) hpositive hcompat hwidth with hevent | hprojection
  · exact Or.inl hevent
  · obtain ⟨S, hS, hSc, hSo, hinvariant, hmeans, hgap⟩ := hprojection
    exact Or.inr ⟨S, hS, hSc, hSo, hinvariant, hmeans, hgap false true⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedAnchoredComparison
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem anchored_auxiliary_piece_residue_pair {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} (T : D.Niltest (fun _ : σ => 1))
    (lo : σ → ℤ) (N : σ → ℕ) (cells : ∀ i, FiniteProgressionPartition (N i))
    (hstep : ∀ i k, (cells i).step k = 1) (hpos : ∀ i k, 0 < (cells i).length k)
    (M P : ℕ) (hM : 0 < M) (hP : 0 < P) (u v : σ → ℤ) (J : σ → ℕ)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (hcop : ∀ i, (M * (M * P)).Coprime (J i))
    (k : AuxiliaryBoxLabels cells (fun _ => M) (fun _ => M * P) u)
    (hk₀ : 0 < (partitionCell (baseAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P)
      (fun _ => Nat.mul_pos hM hP) u) k).card)
    (hk₁ : 0 < (partitionCell (refinedAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P) J
      (fun _ => Nat.mul_pos hM hP) u v hv) k).card) :
    let Q := Nat.lcm M (M * P)
    let lo' : σ → ℤ := fun i => intervalCellLower (lo i) (cells i) (k i).1
    let N' : σ → ℕ := fun i => (cells i).length (k i).1
    ∃ w z : σ → ℤ,
      (∀ i, lo' i ≤ w i ∧ w i < lo' i + N' i) ∧
      (∀ i, lo' i ≤ z i ∧ z i < lo' i + N' i) ∧
      (∀ i, w i ≡ u i [ZMOD (M : ℤ)]) ∧
      (∀ i, z i ≡ v i [ZMOD (M * J i : ℕ)]) ∧
      (∀ i, z i ≡ w i [ZMOD (Q : ℤ)]) ∧
      Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w) ∧
      Nonempty (IntegerResidueBox lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z) ∧
      let S := T.scalarAffinePullback (Q / M : ℕ) (fun i => (commonStrideIndex u M w i : ℚ))
      (𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u) k, residueBoxStrideValue T.eval u M x) =
        residuePairMean S.eval lo' N' Q w z J false ∧
      (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell lo N cells (fun _ => M) (fun _ => M * P) J
        (fun _ => Nat.mul_pos hM hP) u v hv) k, residueBoxStrideValue T.eval u M x) =
        residuePairMean S.eval lo' N' Q w z J true := by
  intro Q lo' N'
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hk₀
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hk₁
  let w : σ → ℤ := fun i => (x i).val
  let z : σ → ℤ := fun i => (y i).val
  have hx' := (mem_boxAuxiliaryCell_iff lo N cells hstep (fun _ => M) (fun _ => M * P)
    (fun _ => Nat.mul_pos hM hP) u (fun _ => (M : ℤ)) u (fun _ _ ht => ht) k x).mp hx
  have hy' := (mem_boxAuxiliaryCell_iff lo N cells hstep (fun _ => M) (fun _ => M * P)
    (fun _ => Nat.mul_pos hM hP) u (fun i => (M * J i : ℕ)) v
    (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) k y).mp hy
  have hw : ∀ i, w i ≡ u i [ZMOD (M : ℤ)] := fun i => (Finset.mem_filter.mp (x i).property).2
  have hz : ∀ i, z i ≡ v i [ZMOD (M * J i : ℕ)] := fun i => (Finset.mem_filter.mp (y i).property).2
  have hcombine₀ : ∀ i (t : ℤ),
      (t ≡ u i [ZMOD (M : ℤ)] ∧ t ≡ ((k i).2.val.val : ℤ) [ZMOD (M * P : ℕ)]) ↔
        t ≡ w i [ZMOD (Q : ℤ)] := by
    intro i t
    exact residue_constraints_iff_lcm (hw i) (hx' i).2 t
  have hcombine₁ : ∀ i (t : ℤ),
      (t ≡ v i [ZMOD (M * J i : ℕ)] ∧ t ≡ ((k i).2.val.val : ℤ) [ZMOD (M * P : ℕ)]) ↔
        t ≡ z i [ZMOD (Q * J i : ℕ)] := by
    intro i t
    have hc := ((k i).2.refinedConstraint_iff (hcop i) (v i) (hv i) (z i)).mp ⟨hz i, (hy' i).2⟩
    exact ((k i).2.refinedConstraint_iff (hcop i) (v i) (hv i) t).trans
      ⟨fun ht => ht.trans hc.symm, fun ht => ht.trans hc⟩
  have hzw : ∀ i, z i ≡ w i [ZMOD (Q : ℤ)] := fun i => (hcombine₀ i (z i)).mp
    ⟨refinedResidue_implies_base M (J i) (u i) (v i) (hv i) (z i) (hz i), (hy' i).2⟩
  have hMQ : M ∣ Q := Nat.dvd_lcm_left M (M * P)
  refine ⟨w, z, fun i => (hx' i).1, fun i => (hy' i).1, hw, hz, hzw, ?_, ?_, ?_⟩
  · exact ⟨fun i => ⟨w i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hx' i).1, Int.ModEq.refl _⟩⟩⟩
  · exact ⟨fun i => ⟨z i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (hy' i).1, Int.ModEq.refl _⟩⟩⟩
  · intro S
    constructor
    · rw [residuePairMean_false]
      exact (boxAuxiliaryCell_expect lo N cells hstep hpos (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u (fun _ => (M : ℤ)) u (fun _ _ ht => ht) k
        (fun _ => (Q : ℤ)) w hcombine₀ (fun t => T.eval (commonStrideIndex u M t))).trans
        (T.residueBoxStride_rebase lo' (fun i => lo' i + N' i) (fun _ => (Q : ℤ)) w u w
          hM hMQ hw (fun _ _ ht => ht))
    · rw [residuePairMean_true]
      exact (boxAuxiliaryCell_expect lo N cells hstep hpos (fun _ => M) (fun _ => M * P)
        (fun _ => Nat.mul_pos hM hP) u (fun i => (M * J i : ℕ)) v
        (fun i => refinedResidue_implies_base M (J i) (u i) (v i) (hv i)) k
        (fun i => (Q * J i : ℕ)) z hcombine₁ (fun t => T.eval (commonStrideIndex u M t))).trans
        (T.residueBoxStride_rebase lo' (fun i => lo' i + N' i) (fun i => (Q * J i : ℕ)) z u w
          hM hMQ hw (fun i => refinedResidue_implies_base Q (J i) (w i) (z i) (hzw i)))

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem anchored_child_comparison_of_piece {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {t e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (cost η δ : ℝ) (lo : σ → ℤ) (N H : σ → ℕ)
    (hH : ∀ i, 0 < H i) (hHN : ∀ i, H i ≤ N i)
    (hlower : ∀ i, δ * (N i : ℝ) / 8 ≤ (H i : ℝ))
    (hupper : ∀ i, (H i : ℝ) ≤ δ * (N i : ℝ) / 4)
    (M P : ℕ) (hM : 0 < M) (hP : 0 < P) (u v : σ → ℤ) (J : σ → ℕ)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (hcop : ∀ i, (M * (M * P)).Coprime (J i))
    (k : AuxiliaryBoxLabels (comparableBoxPartitions N H hH hHN) (fun _ => M) (fun _ => M * P) u)
    (hk₀ : 0 < (partitionCell (baseAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
      (fun _ => M) (fun _ => M * P) (fun _ => Nat.mul_pos hM hP) u) k).card)
    (hk₁ : 0 < (partitionCell (refinedAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
      (fun _ => M) (fun _ => M * P) J (fun _ => Nat.mul_pos hM hP) u v hv) k).card)
    (U : V.Niltest (fun _ : σ => 1)) (hU : U.orbit = child) (hunit : U.UnitIntervalValued)
    (hcost : U.ComplexityLE cost)
    (hgap : η ≤ ‖(𝔼 x ∈ partitionCell (baseAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
        (fun _ => M) (fun _ => M * P) (fun _ => Nat.mul_pos hM hP) u) k, residueBoxStrideValue U.eval u M x) -
      (𝔼 x ∈ partitionCell (refinedAuxiliaryBoxCell lo N (comparableBoxPartitions N H hH hHN)
        (fun _ => M) (fun _ => M * P) J (fun _ => Nat.mul_pos hM hP) u v hv) k, residueBoxStrideValue U.eval u M x)‖) :
    AnchoredChildResidueComparison V child cost η δ lo N M P u v J := by
  let cells := comparableBoxPartitions N H hH hHN
  have hstep : ∀ i j, (cells i).step j = 1 := comparableBoxPartitions_step N H hH hHN
  have hpos : ∀ i j, 0 < (cells i).length j := fun i j =>
    (hH i).trans_le (comparableBoxPartitions_length N H hH hHN i j).1
  obtain ⟨w, z, hwpos, hzpos, hw, hz, hzw, hbase, hfine, hmean₀, hmean₁⟩ :=
    anchored_auxiliary_piece_residue_pair U lo N cells hstep hpos M P hM hP u v J hv hcop k hk₀ hk₁
  let Q := Nat.lcm M (M * P)
  let lo' : σ → ℤ := fun i => intervalCellLower (lo i) (cells i) (k i).1
  let N' : σ → ℕ := fun i => (cells i).length (k i).1
  let S := U.scalarAffinePullback (Q / M : ℕ) (fun i => (commonStrideIndex u M w i : ℚ))
  refine ⟨lo', N', w, z, S, ?_, fun i => hpos i (k i).1, ?_, hwpos, hzpos, hw, hz, hzw,
    hbase, hfine, ?_, hunit, hcost, ?_⟩
  · intro i
    have hend := (cells i).end_le_of_step_one (hstep i) (k i).1 (hpos i (k i).1)
    have hend' : ((cells i).start (k i).1 : ℤ) + (cells i).length (k i).1 ≤ N i := by exact_mod_cast hend
    have hstart : (0 : ℤ) ≤ (cells i).start (k i).1 := Int.natCast_nonneg _
    dsimp only [lo', N', intervalCellLower]
    constructor <;> omega
  · intro i
    have hlen := comparableBoxPartitions_length N H hH hHN i (k i).1
    have hlo : (H i : ℝ) ≤ (N' i : ℝ) := by exact_mod_cast hlen.1
    have hhi : (N' i : ℝ) < 2 * (H i : ℝ) := by exact_mod_cast hlen.2
    exact ⟨(hlower i).trans hlo, by linarith [hupper i]⟩
  · change V.filtration.realification.scalarAffineOrbitHom (Q / M : ℕ)
      (fun i => (commonStrideIndex u M w i : ℚ)) U.orbit = _
    rw [hU]
  · exact hgap.trans_eq (congrArg norm (congrArg₂ (fun a b : ℂ => a - b) hmean₀ hmean₁))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FixedAffineEpochTransition
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_separated_residue_event_or_child (s : ℕ) (hs : 1 ≤ s) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (V : RationalFilteredNilmanifold K t e)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (p work q rho : ℝ), 0 ≤ p → p ≤ work → p ≤ q → (Fintype.card σ : ℝ) ≤ q →
      verticalDecompositionBudget p ≤ q → 0 < rho → rho⁻¹ ≤ Real.exp p →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (b : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
        (q₀ P C a : ℕ) (hP : 0 < P) (cost : ℝ),
      FixedResidueDescent D W V (fun _ : σ => 1) b child work q₀ P hP C a cost →
      ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (E R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup), κ ∈ D.realLattice →
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
          ⟨⟨T.orbit.log, T.orbit.property⟩⟩ →
        D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q₀ R →
        ∀ A : σ → ℝ, (∀ i, 0 < A i) →
          D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A (Real.exp ((work + 2) ^ a)) E →
          ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (_hM : 0 < M) (u v : σ → ℤ) (J : σ → ℕ),
          (∀ i, 0 < J i) → ∀ _hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)],
          (∀ i, (M * (M * P)).Coprime (J i)) →
          (∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ)) →
          ∀ Δ ε δ : ℝ, 0 < δ → δ ≤ 1 → ε < 1 / 2 →
          2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2 →
          8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ Δ / 4 →
          (∀ i, 8 ≤ δ * (N i : ℝ)) →
          (∀ i, (u i : ℝ) - (M : ℝ) * A i ≤ (lo i : ℝ) ∧
            (lo i : ℝ) + (N i : ℝ) ≤ (u i : ℝ) + (M : ℝ) * A i) →
          (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8 →
          Δ ≤ ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ →
          ResiduePairDimensionDrop D ω hF T W lo N M u v J ((q + B) ^ B) ∨
          AnchoredChildResidueComparison V child cost (Δ / 4) δ lo N M P u v J := by
  obtain ⟨B, hB, hstep⟩ := exists_residue_pair_stability_step s hs
  refine ⟨B, hB, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ d t e D V ω hF p work q rho hp hpwork hpq hσ hfreq hrho hrhop
    W b child q₀ P C a hP cost hdesc T hunit hT E R κ hκ hprod hgrid A hA hE
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  rcases hstep D ω hF p q rho hp hpq hσ hfreq hrho hrhop T hunit hT W lo N M u v J
    hM hJ hv hsteplarge with hevent | hprojected
  · exact Or.inl hevent
  · obtain ⟨S, hunitS, hS, hSo, hinvariant, _, hSgap⟩ := hprojected
    have hprodS : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ := by
      simpa only [hSo] using hprod
    have hgapS : Δ / 2 ≤
        ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖ := by
      linarith
    simp only [residuePairMean_false, residuePairMean_true] at hgapS
    have hresult := hdesc.half_discrepancy S (hS.mono hpwork) hunitS hinvariant E R κ hκ hprodS hgrid A hA hE
      M hM lo N u v J hJ hv hcop (Δ / 2) ε δ hδ hδone hε
      (by nlinarith : 8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ (Δ / 2) / 2)
      hlarge hphysical hcount hgapS
    obtain ⟨H, hH, hHN, hlower, hupper, k, hk₀, hk₁, U, hU, hunitU, hcostU, hgapU⟩ := hresult
    exact Or.inr (anchored_child_comparison_of_piece V child cost (Δ / 4) δ lo N H hH hHN
      hlower hupper M P hM hP u v J hv hcop k hk₀ hk₁ U hU hunitU hcostU
      (by simpa only [show (Δ / 2) / 2 = Δ / 4 by ring] using hgapU))

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_fixed_affine_epoch_transition (s : ℕ) (hs : 1 ≤ s) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L K : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {d t e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (V : RationalFilteredNilmanifold K t e)
      (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ)
      (work cost : ℝ) (q₀ P C : ℕ) (hP : 0 < P), 0 ≤ work →
      ∀ (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group)
        (κ : D.RealGroup),
      κ ∈ D.realLattice →
      E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨T.orbit.log, T.orbit.property⟩⟩ →
      D.filtration.PolynomialRationalGrid D.basis (fun _ : σ => 1) q₀ R →
      (∀ A' : σ → ℝ, (∀ i, 0 < A' i) → ∀ (r : ℚ) (h : σ → ℚ),
        (∀ i, |(h i : ℝ)| ≤ A i) → (∀ i, |(r : ℝ)| * A' i ≤ A i) →
        D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A' (Real.exp (work + 2))
          (D.filtration.realification.scalarAffineAdaptedHom r h E)) →
      ∀ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
      FixedAffineResidueDescent D W V b child work q₀ P hP C 1 cost →
      FixedAffineEpochTransition D ω hF W T A V child work cost P C B := by
  obtain ⟨B, hB, hstep⟩ := exists_separated_residue_event_or_child s hs
  refine ⟨B, hB, ?_⟩
  intro σ L K _ _ _ _ _ _ _ _ _ _ _ _ _ _ d t e D V ω hF W T A work cost q₀ P C hP _hwork
    E b R κ hκ hprod hgrid hslow child hchild p hp hpwork r h A' hA' hh hr S hS hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  let E' := D.filtration.realification.scalarAffineAdaptedHom (r : ℚ) (fun i => (h i : ℚ)) E
  let b' := D.filtration.realification.scalarAffineAdaptedHom (r : ℚ) (fun i => (h i : ℚ)) b
  let R' := D.filtration.realification.scalarAffineAdaptedHom (r : ℚ) (fun i => (h i : ℚ)) R
  have horbit : (T.scalarAffinePullback (r : ℚ) (fun i => (h i : ℚ))).orbit = S.orbit := hS.symm
  have hprod' : E' * b' * R' *
      D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) κ =
        ⟨⟨S.orbit.log, S.orbit.property⟩⟩ := by
    simpa only [horbit] using T.scalarAffinePullback_normalized_factorization E b R κ hprod
      (r : ℚ) (fun i => (h i : ℚ))
  have hgrid' := D.filtration.polynomialRationalGrid_scalarAffine_integer D.basis q₀ R hgrid r h
  have hslow' := hslow A' hA' (r : ℚ) (fun i => (h i : ℚ))
    (fun i => by simpa only [Rat.cast_intCast] using hh i)
    (fun i => by simpa only [Rat.cast_intCast] using hr i)
  exact hstep D V ω hF p work q rho hp hpwork hpq hσ hfreq hrho hrhop W b'
    (V.filtration.realification.scalarAffineOrbitHom (r : ℚ) (fun i => (h i : ℚ)) child)
    q₀ P C 1 hP cost (hchild r h) S hunit hcost E' R' κ hκ hprod' hgrid' A' hA'
    (by simpa only [pow_one] using hslow') lo N M hM u v J hJ hv hcop hsteplarge
    Δ ε δ hδ hδone hε hprojection hfreezing hlarge hphysical hcount hgap

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RetainedEpochTransition
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct

theorem exists_retained_affine_epoch_transition_s2_oai (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ {σ L : Type*} [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d) (ω : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (T : D.Niltest (fun _ : σ => 1)) (A : σ → ℝ) (p cost : ℝ) (C : ℕ),
      0 ≤ p → RetainedAffineResidueEpoch D ω hF W T A p cost C →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        ∃ (n : ℕ) (_hn : n ≤ d)
          (Q : RationalFilteredNilmanifold
            ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n),
          Q.filtration = E.filtration.quotientTop ∧
          let H := D.filtration.gradedRefiltrationSubalgebra W
          let N := H ⧸ E.filtration.layerIdeal (s + 1)
          let := moduleTopology ℝ (ℝ ⊗[ℚ] N)
          let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] N)
          let := realification_moduleTopology_t2 Q.basis
          ∃ V : RationalFilteredNilmanifold N s n,
            V.filtration = Q.filtration ∧ V.lattice ≤ Q.lattice ∧ V.GeometryComplexityLE cost ∧
            ∃ child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1),
              DegreeLE (fun _ => 1) s child.log ∧
              FixedAffineEpochTransition D ω hF W T A V child p cost P C B := by
  obtain ⟨B, hB, htransition⟩ := exists_fixed_affine_epoch_transition (s + 1) (by omega)
  refine ⟨B, hB, ?_⟩
  intro σ L _ _ _ _ d _ _ _ _ D ω hF W T A p cost C hp hepoch
  obtain ⟨v, q, P, hP, κ, E, b, R, _, _, _, _, _, hPb, hκ, hprod,
    _, hslow, hgrid, _, _, _, hchild⟩ := hepoch
  obtain ⟨E₀, hE₀, n, hn, Q, hQ, hfixed⟩ := hchild
  refine ⟨P, hP, hPb, E₀, hE₀, n, hn, Q, hQ, ?_⟩
  intro H N _ _ _
  obtain ⟨V, hVF, hVL, hV, child, hdegree, hdescent⟩ := hfixed
  exact ⟨V, hVF, hVL, hV, child, hdegree,
    htransition D V ω hF W T A p cost q P C hP hp E b R κ hκ hprod hgrid hslow child hdescent⟩

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.exists_retained_affine_epoch_transition_s2_oai.{u_1, u_2} := @OAI.Erdos3.exists_retained_affine_epoch_transition_s2_oai.{u_1, u_2}
