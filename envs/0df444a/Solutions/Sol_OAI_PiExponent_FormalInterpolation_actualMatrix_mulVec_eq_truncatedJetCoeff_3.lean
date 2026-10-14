-- Prove2me | solution 3 for OAI.PiExponent.FormalInterpolation.actualMatrix_mulVec_eq_truncatedJetCoeff
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-11T19:14:52.518856+00:00
-- url     : https://prove2.me/submissions/da6f4f79-35b4-4ffe-904c-22abebe85e1f

import Definitions.Def_OAI_PiExponent_FormalInterpolationPackets
import Mathlib

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

noncomputable section
namespace MatrixLeaf

@[simp] private theorem exponentVector_apply {m : ℕ} (a : Fin m → ℕ) (i : Fin m) :
    InterpolationMatrix.exponentVector a i = a i := rfl

private def nestedPolynomialSwap (R : Type*) [CommRing R] (m : ℕ) :
    MvPolynomial (Fin m) (Polynomial R) ≃ₐ[R] Polynomial (MvPolynomial (Fin m) R) :=
  (MvPolynomial.mapAlgEquiv (Fin m) (MvPolynomial.uniqueAlgEquiv R Unit).symm).trans
    ((MvPolynomial.commAlgEquiv R (Fin m) Unit).trans
      ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin m) R) Unit).restrictScalars R))

private theorem coeff_commAlgEquiv {R σ τ : Type*} [CommRing R]
    (p : MvPolynomial σ (MvPolynomial τ R)) (b : σ →₀ ℕ) (c : τ →₀ ℕ) :
    ((MvPolynomial.commAlgEquiv R σ τ p).coeff c).coeff b = (p.coeff b).coeff c := by
  classical
  induction p using MvPolynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, MvPolynomial.coeff_add, hp, hq]
  | monomial d a =>
    induction a using MvPolynomial.induction_on' with
    | add a e ha he =>
      simpa only [map_add, MvPolynomial.coeff_add]
        using congrArg₂ (· + ·) ha he
    | monomial e r =>
      have hs : MvPolynomial.commAlgEquiv R σ τ
          (MvPolynomial.monomial d (MvPolynomial.monomial e r)) =
          MvPolynomial.monomial e (MvPolynomial.monomial d r) :=
        AddMonoidAlgebra.commAlgEquiv_single_single (R := R) d e r
      rw [hs]
      simp only [MvPolynomial.coeff_monomial]
      split_ifs <;> simp_all

private theorem coeff_nestedPolynomialSwap {R : Type*} [CommRing R] {m : ℕ}
    (p : MvPolynomial (Fin m) (Polynomial R)) (s : ℕ) (b : Fin m →₀ ℕ) :
    ((nestedPolynomialSwap R m p).coeff s).coeff b = (p.coeff b).coeff s := by
  change ((MvPolynomial.uniqueAlgEquiv (MvPolynomial (Fin m) R) Unit
    (MvPolynomial.commAlgEquiv R (Fin m) Unit
      (MvPolynomial.mapAlgEquiv (Fin m) (MvPolynomial.uniqueAlgEquiv R Unit).symm p))).coeff s).coeff b = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv, coeff_commAlgEquiv]
  rw [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.coeff_map]
  change (((MvPolynomial.uniqueAlgEquiv R Unit).symm (p.coeff b)).coeff
    (Finsupp.single () s)) = _
  rw [MvPolynomial.coeff_uniqueAlgEquiv_symm]
  simp

private def flatten (m : ℕ) :
    MvPolynomial (Fin m) (Polynomial ℂ) →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  (MvPolynomial.coeToMvPowerSeries.algHom ℂ).comp
    ((MvPolynomial.finSuccEquiv ℂ m).symm.toAlgHom.comp
      (nestedPolynomialSwap ℂ m).toAlgHom)

@[simp] private theorem coeff_flatten {m : ℕ}
    (p : MvPolynomial (Fin m) (Polynomial ℂ)) (d : Fin (m+1) →₀ ℕ) :
    MvPowerSeries.coeff d (flatten m p) = (p.coeff d.tail).coeff (d 0) := by
  change ((MvPolynomial.finSuccEquiv ℂ m).symm (nestedPolynomialSwap ℂ m p)).coeff d = _
  rw [← Finsupp.cons_tail d, ← MvPolynomial.finSuccEquiv_coeff_coeff,
    AlgEquiv.apply_symm_apply]
  exact coeff_nestedPolynomialSwap p (d 0) d.tail

@[simp] private theorem coeff_liftSeries (m : ℕ) (f : PowerSeries ℂ)
    (d : Fin (m + 1) →₀ ℕ) :
    MvPowerSeries.coeff d (FormalInterpolation.liftSeries m f) =
      if d.tail = 0 then PowerSeries.coeff (d 0) f else 0 := by
  have h := MvPowerSeries.coeff_coeff_finSuccEquiv
    (FormalInterpolation.liftSeries m f) (k := d 0) (x := d.tail)
  rw [Finsupp.cons_tail] at h
  rw [← h]
  simp [FormalInterpolation.liftSeries, PowerSeries.coeff_map, MvPowerSeries.coeff_C]

@[simp] private theorem liftSeries_X (m : ℕ) :
    FormalInterpolation.liftSeries m PowerSeries.X = MvPowerSeries.X 0 := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [FormalInterpolation.liftSeries]

@[simp] private theorem liftSeries_C (m : ℕ) (r : ℂ) :
    FormalInterpolation.liftSeries m (PowerSeries.C r) = MvPowerSeries.C r := by
  apply (MvPowerSeries.finSuccEquiv ℂ m).injective
  simp [FormalInterpolation.liftSeries]

@[simp] private theorem flatten_C {m : ℕ} (p : Polynomial ℂ) :
    flatten m (MvPolynomial.C p) =
      FormalInterpolation.liftSeries m (p : PowerSeries ℂ) := by
  classical
  ext d
  rw [coeff_flatten, coeff_liftSeries]
  simp only [MvPolynomial.coeff_C, Polynomial.coeff_coe]
  split_ifs <;> simp_all

@[simp] private theorem flatten_X {m : ℕ} (i : Fin m) :
    flatten m (MvPolynomial.X i) = MvPowerSeries.X i.succ := by
  classical
  ext d
  rw [coeff_flatten, MvPolynomial.coeff_X, MvPowerSeries.coeff_X]
  have hd : d = Finsupp.single i.succ 1 ↔
      d.tail = Finsupp.single i 1 ∧ d 0 = 0 := by
    conv_lhs => rw [← Finsupp.cons_tail d]
    exact Finsupp.cons_eq_single_succ_iff i
  simp only [hd]
  by_cases ht : Finsupp.single i 1 = d.tail
  · rw [if_pos ht]
    have ht' : d.tail = Finsupp.single i 1 := ht.symm
    simp only [ht', true_and, Polynomial.coeff_one]
  · rw [if_neg ht, Polynomial.coeff_zero]
    have ht' : ¬ d.tail = Finsupp.single i 1 := Ne.symm ht
    simp only [ht', false_and, ite_false]

private def literalJet {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) :
    MvPolynomial (Fin (m+1)) ℂ →ₐ[ℂ] MvPolynomial (Fin m) (Polynomial ℂ) :=
  MvPolynomial.aeval (Fin.cases (MvPolynomial.C (1 + Polynomial.X))
    (fun i => MvPolynomial.C (Polynomial.C ((j : ℂ) * r i) + G i) + MvPolynomial.X i))

private def truncatedJet {m : ℕ} (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ) :
    MvPolynomial (Fin (m+1)) ℂ →ₐ[ℂ] MvPowerSeries (Fin (m+1)) ℂ :=
  MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
    (fun i => MvPowerSeries.C ((j : ℂ) * r i) + MvPowerSeries.X i.succ +
      FormalInterpolation.liftSeries m
        ((PowerSeries.trunc (T i) (PowerSeries.log ℂ) : Polynomial ℂ) : PowerSeries ℂ)))

private theorem flatten_literalJet {m : ℕ}
    (r : Fin m → ℂ) (T : Fin m → ℕ) (j : ℕ)
    (p : MvPolynomial (Fin (m+1)) ℂ) :
    flatten m (literalJet r (fun i => InterpolationMatrix.truncatedLog (T i)) j p) =
      truncatedJet r T j p := by
  have hh : (flatten m).comp
      (literalJet r (fun i => InterpolationMatrix.truncatedLog (T i)) j) =
        truncatedJet r T j := by
    ext i
    cases i using Fin.cases with
    | zero => simp [literalJet, truncatedJet]
    | succ i =>
      simp [literalJet, truncatedJet, InterpolationMatrix.truncatedLog,
        add_assoc, add_left_comm, add_comm]
  exact DFunLike.congr_fun hh p

private theorem literalJet_monomial {m : ℕ} (r : Fin m → ℂ)
    (G : Fin m → Polynomial ℂ) (j : ℕ) (e : Fin (m+1) → ℕ) (z : ℂ) :
    literalJet r G j (MvPolynomial.monomial (InterpolationMatrix.exponentVector e) z) =
      MvPolynomial.C (Polynomial.C z) *
        InterpolationMatrix.monomialImage r G j (e 0) (fun i => e i.succ) := by
  classical
  rw [literalJet, MvPolynomial.aeval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_succ]
  simp only [exponentVector_apply, Fin.cases_zero, Fin.cases_succ,
    InterpolationMatrix.monomialImage, ← map_pow]
  rfl

private theorem simplex_mem {m : ℕ} (w : Fin m → ℝ) (hw : ∀ i, 0 < w i)
    (H : ℝ) (a : Fin m → ℕ) (ha : ∑ i, w i * (a i : ℝ) ≤ H) :
    a ∈ realWeightedSimplex w H := by
  classical
  refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr ?_, ha⟩
  intro i
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  apply Nat.le_floor
  apply (le_div_iff₀ (hw i)).mpr
  rw [mul_comm]
  exact (Finset.single_le_sum (f := fun j => w j * (a j : ℝ))
    (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)).trans ha

private theorem reconstruct {m : ℕ} (w0 H : ℝ) (w : Fin m → ℝ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : FormalInterpolation.WeightedPolynomial w0 w H) :
    (∑ c : InterpolationMatrix.Column w0 w H,
      MvPolynomial.monomial (InterpolationMatrix.exponentVector c.val)
        (P.val.coeff (InterpolationMatrix.exponentVector c.val))) = P.val := by
  classical
  ext e
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  let a : Fin (m+1) → ℕ := fun i => e i
  have hea : InterpolationMatrix.exponentVector a = e := by ext i; rfl
  by_cases ha : a ∈ realWeightedSimplex (InterpolationMatrix.columnWeights w0 w) H
  · let c : InterpolationMatrix.Column w0 w H := ⟨a, ha⟩
    rw [Finset.sum_eq_single c]
    · simp [c, hea]
    · intro b _ hbc
      have hne : InterpolationMatrix.exponentVector b.val ≠ e := by
        intro he
        apply hbc
        apply Subtype.ext
        funext i
        exact congrArg (fun f : Fin (m+1) →₀ ℕ => f i) he
      simp [hne]
    · simp
  · have hp : P.val.coeff e = 0 := by
      by_contra hne
      apply ha
      apply simplex_mem _ (fun i => Fin.cases hw0 hw i)
      simpa [a] using P.property e (MvPolynomial.mem_support_iff.mpr hne)
    rw [hp]
    apply Finset.sum_eq_zero
    intro c _
    have hne : InterpolationMatrix.exponentVector c.val ≠ e := by
      intro he
      apply ha
      have hc : c.val = a := by
        funext i
        exact congrArg (fun f : Fin (m+1) →₀ ℕ => f i) he
      exact hc ▸ c.property
    simp [hne]

private theorem matrix_coefficient {m : ℕ} (K : ℕ) (w0 v0 theta H : ℝ)
    (w : Fin m → ℝ) (T : Fin m → ℕ) (r : Fin m → ℂ)
    (hw0 : 0 < w0) (hw : ∀ i, 0 < w i)
    (P : FormalInterpolation.WeightedPolynomial w0 w H)
    (rho : InterpolationMatrix.Row K v0 theta w H) :
    (InterpolationMatrix.truncatedLogMatrix K w0 v0 theta w H r T).mulVecLin
      (fun c => P.val.coeff (InterpolationMatrix.exponentVector c.val)) rho =
    MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
      (truncatedJet r T rho.1.val P.val) := by
  classical
  conv_rhs => rw [← reconstruct w0 H w hw0 hw P]
  rw [← flatten_literalJet, coeff_flatten]
  simp only [map_sum, literalJet_monomial, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_C_mul, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  rw [Matrix.mulVecLin_apply, Matrix.mulVec]
  apply Finset.sum_congr rfl
  intro c _
  have ht : (InterpolationMatrix.exponentVector rho.2.val).tail =
      InterpolationMatrix.exponentVector (fun i => rho.2.val i.succ) := by
    ext i
    rfl
  simp only [ht, exponentVector_apply, InterpolationMatrix.truncatedLogMatrix,
    InterpolationMatrix.matrix, InterpolationMatrix.entry]
  ring

end MatrixLeaf

theorem solution
    {nu : Real} (d : FixedData nu) (H : Rat)
    (P : FormalInterpolation.WeightedPolynomial d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) (H : Real)) :
    forall rho : Row d H,
      (actualMatrix d (H : Real)).mulVecLin
          (fun c : Column d (H : Real) =>
            P.val.coeff (InterpolationMatrix.exponentVector c.1)) rho =
        MvPowerSeries.coeff (InterpolationMatrix.exponentVector rho.2.val)
          (MvPolynomial.aeval (Fin.cases (1 + MvPowerSeries.X 0)
            (fun i => MvPowerSeries.C ((rho.1.val : Complex) *
                MatrixArithmetic.rationalCenters (finiteNumerators d)
                  (finiteDenominators d) i) + MvPowerSeries.X i.succ +
              FormalInterpolation.liftSeries d.m
                ((PowerSeries.trunc
                  (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0 i)
                  (PowerSeries.log Complex) : Polynomial Complex) : PowerSeries Complex))) P.val) := by
  intro rho
  have hw : ∀ i : Fin d.m, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    change 0 < (Nat.ceil (Real.log (d.q i.val)) : ℝ)
    rw [← d.x_log i.val]
    exact lt_of_lt_of_le zero_lt_one (d.x_one_le _)
  exact MatrixLeaf.matrix_coefficient d.K d.w0 d.v0 d.base.theta (H : ℝ)
    (MatrixArithmetic.logWeights (finiteDenominators d))
    (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)
    (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
    d.w0_pos hw P rho
