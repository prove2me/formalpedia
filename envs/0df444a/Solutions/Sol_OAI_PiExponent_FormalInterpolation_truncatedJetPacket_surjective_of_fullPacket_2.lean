-- Prove2me | solution 2 for OAI.PiExponent.FormalInterpolation.truncatedJetPacket_surjective_of_fullPacket
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-16T05:06:03.887694+00:00
-- url     : https://prove2.me/submissions/4727de96-521f-4cfc-a604-095c47ab342d

-- Bridge repair directed by Alexander Richard Towell (queelius), formalized by Codex.
-- Uses Yuxuan Xu's accepted rational truncation equivalence and the upstream
-- rational-index method from OpenAI/math FormalJetIndices.lean at adc7f1241b42e322a6451854ab7e4b4c146bf78a.
import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Theorems.Thm_OAI_PiExponent_FormalLogTruncation_formalLog_packets_surjective_iff_truncated

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

namespace Queelius.PacketRepair

noncomputable def rationalRowWeights {nu : ℝ} (d : FixedData nu) : Fin (d.m + 1) → ℚ :=
  Fin.cases d.v0 (fun i => (Nat.ceil (Real.log (d.q i.val)) : ℚ) / d.base.theta)

theorem cast_rationalRowWeights {nu : ℝ} (d : FixedData nu) (i : Fin (d.m + 1)) :
    (rationalRowWeights d i : ℝ) = InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
  cases i using Fin.cases with
  | zero => rfl
  | succ i => simp [rationalRowWeights, InterpolationMatrix.rowWeights,
      MatrixArithmetic.logWeights, finiteDenominators]

theorem rationalRowWeights_nonneg {nu : ℝ} (d : FixedData nu) :
    ∀ i, 0 ≤ rationalRowWeights d i := by
  intro i
  cases i using Fin.cases with
  | zero =>
    change 0 ≤ d.v0
    exact_mod_cast d.v0_pos.le
  | succ i =>
    change 0 ≤ (Nat.ceil (Real.log (d.q i.val)) : ℚ) / d.base.theta
    apply div_nonneg (Nat.cast_nonneg _)
    exact_mod_cast d.base.theta_pos.le

theorem rational_cutoff {nu : ℝ} (d : FixedData nu)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ)) :
    ∀ i : Fin d.m, rationalRowWeights d i.succ ≤
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℚ) *
        rationalRowWeights d 0 := by
  intro i
  have hi := hT i
  change (Nat.ceil (Real.log (d.q i.val)) : ℝ) / (d.base.theta : ℝ) ≤ _ at hi
  change (Nat.ceil (Real.log (d.q i.val)) : ℚ) / d.base.theta ≤
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℚ) * d.v0
  exact_mod_cast hi

#print axioms cast_rationalRowWeights
#print axioms rationalRowWeights_nonneg
#print axioms rational_cutoff

end Queelius.PacketRepair

open scoped BigOperators

namespace Queelius.PacketRepair

theorem rationalRowWeights_pos {nu : ℝ} (d : FixedData nu) :
    ∀ i, 0 < rationalRowWeights d i := by
  intro i
  cases i using Fin.cases with
  | zero => change 0 < d.v0; exact_mod_cast d.v0_pos
  | succ i =>
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℚ) / d.base.theta
    apply div_pos
    · have h := d.x_one_le (i.val + 1)
      rw [d.x_log] at h
      have hh : (0 : ℝ) < (Nat.ceil (Real.log (d.q i.val)) : ℝ) := by linarith
      exact_mod_cast hh
    · exact_mod_cast d.base.theta_pos

theorem mem_strict_simplex {n : ℕ} (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (H : ℝ) (a : Fin n → ℕ) :
    a ∈ strictWeightedSimplex w H ↔ ∑ i, w i * (a i : ℝ) < H := by
  classical
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, h.le⟩, h⟩
    simp only [Fintype.mem_piFinset, Finset.mem_range]
    intro i
    apply Nat.lt_succ_of_le
    apply Nat.le_floor
    apply (le_div_iff₀ (hw i)).mpr
    calc
      _ = w i * (a i : ℝ) := mul_comm _ _
      _ ≤ ∑ j, w j * (a j : ℝ) := Finset.single_le_sum
        (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
      _ ≤ H := h.le

theorem cast_finsupp_weight {n : ℕ} (V : Fin n → ℚ) (a : Fin n →₀ ℕ) :
    (Finsupp.weight V a : ℝ) = ∑ i, (V i : ℝ) * (a i : ℝ) := by
  simp only [Finsupp.weight_eq_sum, nsmul_eq_mul, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_natCast, mul_comm]

@[simp] theorem exponentVector_apply {n : ℕ} (a : Fin n → ℕ) (i : Fin n) :
    InterpolationMatrix.exponentVector a i = a i := by
  simp [InterpolationMatrix.exponentVector]

@[simp] theorem exponentVector_coe {n : ℕ} (a : Fin n →₀ ℕ) :
    InterpolationMatrix.exponentVector (fun i => a i) = a := by
  ext i
  simp

noncomputable def indexEquiv {nu : ℝ} (d : FixedData nu) (H : ℚ) :
    {a : Fin (d.m + 1) →₀ ℕ // Finsupp.weight (rationalRowWeights d) a < H} ≃
      ↥(strictWeightedSimplex
        (InterpolationMatrix.rowWeights d.v0 d.base.theta
          (MatrixArithmetic.logWeights (finiteDenominators d))) (H : ℝ)) := by
  have hw : ∀ i, 0 < InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
    intro i
    rw [← cast_rationalRowWeights]
    exact_mod_cast rationalRowWeights_pos d i
  refine {
    toFun := fun a => ⟨fun i => a.val i, ?_⟩
    invFun := fun a => ⟨InterpolationMatrix.exponentVector a.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · apply (mem_strict_simplex _ hw _ _).mpr
    have h : (Finsupp.weight (rationalRowWeights d) a.val : ℝ) < (H : ℝ) := by
      exact_mod_cast a.property
    simpa only [cast_finsupp_weight, cast_rationalRowWeights] using h
  · have h := (mem_strict_simplex _ hw _ _).mp a.property
    have hc : (Finsupp.weight (rationalRowWeights d)
        (InterpolationMatrix.exponentVector a.val) : ℝ) < (H : ℝ) := by
      simpa only [cast_finsupp_weight, cast_rationalRowWeights, exponentVector_apply] using h
    exact_mod_cast hc
  · intro a
    apply Subtype.ext
    exact exponentVector_coe a.val
  · intro a
    apply Subtype.ext
    funext i
    exact exponentVector_apply a.val i

@[simp] theorem indexEquiv_apply_val {nu : ℝ} (d : FixedData nu) (H : ℚ)
    (a : {a : Fin (d.m + 1) →₀ ℕ // Finsupp.weight (rationalRowWeights d) a < H}) :
    (indexEquiv d H a).val = fun i => a.val i := rfl

@[simp] theorem indexEquiv_symm_val {nu : ℝ} (d : FixedData nu) (H : ℚ)
    (a : ↥(strictWeightedSimplex
      (InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))) (H : ℝ))) :
    ((indexEquiv d H).symm a).val = InterpolationMatrix.exponentVector a.val := rfl

end Queelius.PacketRepair

open Queelius.PacketRepair

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℚ)
    (hT : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i / (d.base.theta : ℝ) ≤
        (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i : ℝ) *
          (d.v0 : ℝ))
    (hpacket : Function.Surjective (FormalInterpolation.packetMap d (H : ℝ))) :
    Function.Surjective
      (fun P : FormalInterpolation.WeightedPolynomial d.w0
          (MatrixArithmetic.logWeights (finiteDenominators d)) (H : ℝ) =>
        fun rho : Row d H =>
          MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
            (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
              (fun i => MvPowerSeries.C ((rho.1.val : ℂ) *
                  MatrixArithmetic.rationalCenters (finiteNumerators d)
                    (finiteDenominators d) i) + MvPowerSeries.X i.succ +
                FormalInterpolation.liftSeries d.m
                  ((PowerSeries.trunc
                    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
                    (PowerSeries.log ℂ) : Polynomial ℂ) : PowerSeries ℂ))) P.val)) := by
  let V := rationalRowWeights d
  let T := MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0
  let c : Fin d.K → Fin d.m → ℂ := fun j i => (j.val : ℂ) *
    MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i
  let P := fun p : FormalInterpolation.WeightedPolynomial d.w0
    (MatrixArithmetic.logWeights (finiteDenominators d)) (H : ℝ) => p.val
  have hfull : Function.Surjective (fun p j =>
      JetGeometry.rationalCoefficientPacket V H (FormalLogJet.formalJet (c j) (P p))) := by
    intro y
    obtain ⟨p, hp⟩ := hpacket (fun rho => y rho.1 ((indexEquiv d H).symm rho.2))
    refine ⟨p, ?_⟩
    funext j a
    have h := congrFun hp (j, indexEquiv d H a)
    simp only [FormalInterpolation.packetMap, indexEquiv_apply_val, exponentVector_coe,
      Equiv.symm_apply_apply] at h
    exact h
  have htrunc := (FormalLogTruncation.formalLog_packets_surjective_iff_truncated
    V (rationalRowWeights_nonneg d) H T (rational_cutoff d hT) c P).mp hfull
  intro y
  obtain ⟨p, hp⟩ := htrunc (fun j a => y (j, indexEquiv d H a))
  refine ⟨p, ?_⟩
  funext rho
  have h := congrFun (congrFun hp rho.1) ((indexEquiv d H).symm rho.2)
  simp only [JetGeometry.rationalCoefficientPacket, indexEquiv_symm_val,
    Equiv.apply_symm_apply] at h
  exact h

#print axioms solution
