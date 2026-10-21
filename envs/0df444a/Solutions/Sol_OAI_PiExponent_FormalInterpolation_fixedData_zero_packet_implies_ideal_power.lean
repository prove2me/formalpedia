-- Prove2me | solution 1 for OAI.PiExponent.FormalInterpolation.fixedData_zero_packet_implies_ideal_power
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:34:10.699548+00:00
-- url     : https://prove2.me/submissions/d25d62d0-7520-4f3f-b7cf-d5efb0eb3852
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_fixedData_packet_conditions_eq_colength
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finite_colength_and_truncated_packet_lifting
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmic_ideal_power_truncated_packet_vanishing
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_finiteDimensional_quotient_power_of_finiteDimensional
import Theorems.Thm_OAI_PiExponent_FormalInterpolation_logarithmicCentersIdeal_finiteColength

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation

set_option maxHeartbeats 1000000 in
/-- A polynomial whose truncated packet vanishes at height `n * R` lies in the `n`-th power of
the logarithmic center ideal.  The proof uses exactness of the packet map on the finite
dimensional quotient modulo that ideal power: ideal-power membership implies packet vanishing
(easy direction), the packet is surjective modulo the ideal power (finite colength plus
lifting), and the Hilbert-function count identifies the two finite dimensions, forcing the
induced map to be injective. -/
theorem solution
    (nu : Real) (d : FixedData nu)
    (R : Rat) (T : Fin d.m → Nat) (e : Fin (d.m + 1) → Nat)
    (hR : 0 < R) (he : ∀ i, 0 < e i)
    (hT : ∀ i, InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i.succ ≤
      (T i : Real) * InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) 0)
    (hscale : ∀ i, (R : Real) = (e i : Real) *
      InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i)
    (n : Nat) (P : MvPolynomial (Fin (d.m + 1)) Complex)
    (hzero : truncatedPolynomialPacket d.K d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) ((n : Real) * (R : Real))
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)) T P = 0) :
    P ∈ (logarithmicCentersIdeal
      (fun j : Fin d.K => fun i => (j.val : Complex) *
        MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d) i)
      T e) ^ n := by
  classical
  -- abridged notations
  let w : Fin d.m → Real := MatrixArithmetic.logWeights (finiteDenominators d)
  let r : Fin d.m → Complex :=
    MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d)
  let c : Fin d.K → Fin d.m → Complex := fun j i => (j.val : Complex) * r i
  let I : Ideal (MvPolynomial (Fin (d.m + 1)) Complex) := logarithmicCentersIdeal c T e
  -- positivity and nondegeneracy facts coming from admissibility
  have hv0 : 0 < (d.v0 : Real) := d.v0_pos
  have htheta : 0 < (d.base.theta : Real) := d.base.theta_pos
  have hq : ∀ i, 2 ≤ d.q i := fun i => (d.approximations i).1
  have hw : ∀ i, 0 < w i := by
    intro i
    have h2 : (2 : Real) ≤ (d.q i : Real) := by exact_mod_cast hq i
    have hlog : 0 < Real.log (d.q i : Real) := Real.log_pos (by linarith)
    exact lt_of_lt_of_le hlog (Nat.le_ceil _)
  have hRr : (0 : Real) < (R : Real) := by exact_mod_cast hR
  let hi0 : Fin d.m := ⟨0, d.m_pos⟩
  have hrne : r hi0 ≠ 0 := by
    intro h
    have hp0 : d.p 0 ≠ 0 := (d.approximations 0).2.1
    have hq0 : (d.q 0 : Complex) ≠ 0 := by
      have h1 : (d.q 0 : Nat) ≠ 0 := by have := hq 0; omega
      exact Nat.cast_ne_zero.mpr h1
    have h' : (2 * Complex.I * (d.p 0 : Complex)) / (d.q 0 : Complex) = 0 := by
      dsimp only [r, hi0, MatrixArithmetic.rationalCenters, finiteNumerators,
        finiteDenominators] at h
      exact h
    rcases div_eq_zero_iff.mp h' with h2 | h2
    · have h3 : (d.p 0 : Complex) = 0 := by
        rcases mul_eq_zero.mp h2 with h4 | h4
        · norm_num at h4
        · exact h4
      exact hp0 (Int.cast_eq_zero.mp h3)
    · exact hq0 h2
  have hdist : ∀ j₁ j₂ : Fin d.K, j₁ ≠ j₂ → c j₁ ≠ c j₂ := by
    intro j₁ j₂ hne heq
    apply hne
    have hval : (j₁.val : Complex) * r hi0 = (j₂.val : Complex) * r hi0 :=
      congrFun heq hi0
    have hcast : (j₁.val : Complex) = (j₂.val : Complex) := by
      have h' : (j₁.val : Complex) * r hi0 / r hi0 =
          (j₂.val : Complex) * r hi0 / r hi0 := by rw [hval]
      rwa [mul_div_cancel_right₀ _ hrne, mul_div_cancel_right₀ _ hrne] at h'
    exact Fin.ext (by exact_mod_cast hcast)
  -- finite-dimensionality of the quotient modulo the ideal power
  have hfiniteI : FiniteDimensional Complex
      (MvPolynomial (Fin (d.m + 1)) Complex ⧸ I) :=
    logarithmicCentersIdeal_finiteColength (m := d.m) (K := d.K) c T e he hdist
  have hfiniteIn : FiniteDimensional Complex
      (MvPolynomial (Fin (d.m + 1)) Complex ⧸ I ^ n) :=
    finiteDimensional_quotient_power_of_finiteDimensional I hfiniteI n
  -- surjectivity of the truncated packet map modulo the ideal power (finite colength lifting)
  obtain ⟨-, hlift⟩ := finite_colength_and_truncated_packet_lifting (m := d.m) d.K
    ((d.v0 : Rat) : Real) ((d.base.theta : Rat) : Real) w (R : Real) e T r hRr he
    (fun i => hscale i) ⟨hi0, hrne⟩
  -- the packet is linear in the polynomial
  let φ : MvPolynomial (Fin (d.m + 1)) Complex →ₗ[Complex]
      (InterpolationMatrix.Row d.K d.v0 d.base.theta w ((n : Real) * (R : Real)) → Complex) :=
    { toFun := fun Q => truncatedPolynomialPacket d.K d.v0 d.base.theta w
        ((n : Real) * (R : Real)) r T Q
      map_add' := by
        intro Q₁ Q₂
        funext ρ
        simp only [truncatedPolynomialPacket, Pi.add_apply]
        rw [map_add (truncatedPolynomialJet (fun i => (ρ.1.val : Complex) * r i) T),
          MvPolynomial.coeff_add]
      map_smul' := by
        intro a Q
        funext ρ
        simp only [truncatedPolynomialPacket, Pi.smul_apply]
        rw [map_smul (truncatedPolynomialJet (fun i => (ρ.1.val : Complex) * r i) T),
          MvPolynomial.coeff_smul, RingHom.id_apply] }
  -- the ideal power is a complex subspace of the kernel of the packet
  let p : Submodule (MvPolynomial (Fin (d.m + 1)) Complex)
      (MvPolynomial (Fin (d.m + 1)) Complex) := I ^ n
  let pr : Submodule Complex (MvPolynomial (Fin (d.m + 1)) Complex) :=
    p.restrictScalars Complex
  have hIker : pr ≤ LinearMap.ker φ := by
    intro Q hQ
    rw [LinearMap.mem_ker]
    funext ρ
    exact congrFun (logarithmic_ideal_power_truncated_packet_vanishing d.K
      ((d.v0 : Rat) : Real) ((d.base.theta : Rat) : Real) w r (R : Real) T e hv0 htheta hw
      hRr (fun i => le_of_eq (hscale i)) n Q hQ) ρ
  -- the induced map on the quotient
  let ψ : ((MvPolynomial (Fin (d.m + 1)) Complex) ⧸ pr) →ₗ[Complex]
      (InterpolationMatrix.Row d.K d.v0 d.base.theta w ((n : Real) * (R : Real)) → Complex) :=
    Submodule.liftQ pr φ hIker
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨Q, hQ⟩ := hlift n y
    refine ⟨Submodule.mkQ pr Q, ?_⟩
    have hmem : Q - Q ∈ (I ^ n : Ideal (MvPolynomial (Fin (d.m + 1)) Complex)) := by
      rw [sub_self]
      exact (I ^ n).zero_mem
    have hval : ψ (Submodule.mkQ pr Q) = φ Q := by
      show (Submodule.liftQ pr φ hIker) (Submodule.Quotient.mk Q) = φ Q
      rw [Submodule.liftQ_apply]
    rw [hval]
    exact hQ Q hmem
  -- Hilbert-function count: the two finite dimensions agree
  have hVdim : Module.finrank Complex
      (MvPolynomial (Fin (d.m + 1)) Complex ⧸ I ^ n) =
      Fintype.card (InterpolationMatrix.Row d.K d.v0 d.base.theta w
        ((n : Real) * (R : Real))) :=
    fixedData_packet_conditions_eq_colength nu d R T e hR he hT hscale n
  have hVdim' : Module.finrank Complex
      ((MvPolynomial (Fin (d.m + 1)) Complex) ⧸ pr) =
      Fintype.card (InterpolationMatrix.Row d.K d.v0 d.base.theta w
        ((n : Real) * (R : Real))) := by
    rw [LinearEquiv.finrank_eq (Submodule.Quotient.restrictScalarsEquiv Complex p), hVdim]
  have hWdim : Module.finrank Complex
      (InterpolationMatrix.Row d.K d.v0 d.base.theta w
        ((n : Real) * (R : Real)) → Complex) =
      Fintype.card (InterpolationMatrix.Row d.K d.v0 d.base.theta w
        ((n : Real) * (R : Real))) :=
    Module.finrank_fintype_fun_eq_card Complex
  haveI : FiniteDimensional Complex ((MvPolynomial (Fin (d.m + 1)) Complex) ⧸ p) := hfiniteIn
  haveI : FiniteDimensional Complex ((MvPolynomial (Fin (d.m + 1)) Complex) ⧸ pr) :=
    LinearEquiv.finiteDimensional (Submodule.Quotient.restrictScalarsEquiv Complex p).symm
  have hψ_inj : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot]
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    have hrange : ψ.range = ⊤ := LinearMap.range_eq_top.mpr hψ_surj
    have h1 : Module.finrank Complex ψ.range =
        Fintype.card (InterpolationMatrix.Row d.K d.v0 d.base.theta w
          ((n : Real) * (R : Real))) := by
      rw [hrange, finrank_top, hWdim]
    have h2 : Module.finrank Complex ψ.ker = 0 := by
      rw [h1, hVdim'] at hrn
      omega
    exact Submodule.finrank_eq_zero.mp h2
  -- conclude
  have hφP : φ P = 0 := hzero
  have hker0 : Submodule.mkQ pr P = 0 := by
    apply hψ_inj
    rw [show ψ (Submodule.mkQ pr P) = φ P from by
      show (Submodule.liftQ pr φ hIker) (Submodule.Quotient.mk P) = φ P
      rw [Submodule.liftQ_apply]]
    rw [hφP, map_zero]
  rw [Submodule.mkQ_apply] at hker0
  exact (Submodule.Quotient.mk_eq_zero pr).mp hker0
