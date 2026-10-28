-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.free_hankel_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:55:31.715314+00:00
-- url     : https://prove2.me/submissions/279bed4b-4189-4aca-b2cc-2e12b13fd787

import Mathlib
import Definitions.Def_OAIQ039C066
import Theorems.Thm_OAI_Kadison_FreeBlocks_free_fejer_norm
import Theorems.Thm_OAI_Kadison_FreeBlocks_normalized_errors
import Theorems.Thm_OAI_Kadison_FreeBlocks_normalized_fejer_entry

section
-- module Solutions.OAIQ039_CM.Commutator_FejerTest
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.FejerTest

lemma sum_fin_val (n : ℕ) :
    (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * ((n : ℝ)-1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, ih, Nat.cast_add, Nat.cast_one]
    ring

lemma hankel_average (N : ℕ) (hN : 0 < N) :
    (N : ℝ)⁻¹ * ∑ j : Fin N, ∑ k : Fin N,
      (((2*N : ℝ) - j.val - k.val - 1) / (2*N : ℝ)^2) = 1/4 := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, sum_fin_val]
  simp only [← Finset.mul_sum, sum_fin_val]
  field_simp [hn]
  ring

end Kadison.FejerTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FiniteHankel
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace

open ContinuousLinearMap

namespace Kadison.FreeCorner

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

lemma norm_compress_le (V : K →ₗᵢ[ℂ] H) (T : H →L[ℂ] H) :
    ‖compress V T‖ ≤ ‖T‖ := by
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hv' : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact hv
  calc
    ‖compress V T‖ ≤ ‖V.toContinuousLinearMap.adjoint‖ * ‖T‖ *
        ‖V.toContinuousLinearMap‖ := (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := mul_le_mul
      (mul_le_mul_of_nonneg_right hv' (norm_nonneg _)) hv (norm_nonneg _)
      (by positivity)
    _ = ‖T‖ := by ring

lemma compression_commutator_identity (V : K →ₗᵢ[ℂ] H)
    (G L : H →L[ℂ] H) (J : K →L[ℂ] K) :
    compress V (G * L - L * G) =
      J * compress V L - compress V L * J +
      (G.adjoint.comp V.toContinuousLinearMap -
        V.toContinuousLinearMap.comp J.adjoint).adjoint.comp
        (L.comp V.toContinuousLinearMap) -
      V.toContinuousLinearMap.adjoint.comp
        (L.comp (G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J)) := by
  simp only [compress, mul_def, comp_sub, sub_comp, map_sub,
    adjoint_comp, adjoint_adjoint, comp_assoc]
  abel

lemma norm_compression_commutator_le (V : K →ₗᵢ[ℂ] H)
    (G L : H →L[ℂ] H) (J : K →L[ℂ] K) {d d' : ℝ}
    (hd : ‖G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J‖ ≤ d)
    (hd' : ‖G.adjoint.comp V.toContinuousLinearMap -
      V.toContinuousLinearMap.comp J.adjoint‖ ≤ d') :
    ‖J * compress V L - compress V L * J‖ ≤
      ‖G * L - L * G‖ + (d + d') * ‖L‖ := by
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hd
  have hd0' : 0 ≤ d' := (norm_nonneg _).trans hd'
  let R := G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J
  let R' := G.adjoint.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J.adjoint
  have hv : ‖V.toContinuousLinearMap‖ ≤ 1 := V.norm_toContinuousLinearMap_le
  have hv' : ‖V.toContinuousLinearMap.adjoint‖ ≤ 1 := by rw [adjoint.norm_map]; exact hv
  have h1 : ‖R'.adjoint.comp (L.comp V.toContinuousLinearMap)‖ ≤ d' * ‖L‖ := by
    calc
      _ ≤ ‖R'.adjoint‖ * (‖L‖ * ‖V.toContinuousLinearMap‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ d' * (‖L‖ * 1) := mul_le_mul
        (by simpa only [adjoint.norm_map, R'] using hd')
        (mul_le_mul_of_nonneg_left hv (norm_nonneg _)) (by positivity) hd0'
      _ = d' * ‖L‖ := by ring
  have h2 : ‖V.toContinuousLinearMap.adjoint.comp (L.comp R)‖ ≤ d * ‖L‖ := by
    calc
      _ ≤ ‖V.toContinuousLinearMap.adjoint‖ * (‖L‖ * ‖R‖) :=
        (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left (opNorm_comp_le _ _) (norm_nonneg _))
      _ ≤ 1 * (‖L‖ * d) := mul_le_mul hv'
        (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) (by positivity) (by positivity)
      _ = d * ‖L‖ := by ring
  have heq : J * compress V L - compress V L * J =
      compress V (G * L - L * G) - R'.adjoint.comp (L.comp V.toContinuousLinearMap) +
        V.toContinuousLinearMap.adjoint.comp (L.comp R) := by
    rw [compression_commutator_identity]
    dsimp [R, R']
    abel
  rw [heq]
  calc
    _ ≤ ‖compress V (G * L - L * G)‖ +
        ‖R'.adjoint.comp (L.comp V.toContinuousLinearMap)‖ +
        ‖V.toContinuousLinearMap.adjoint.comp (L.comp R)‖ := (norm_add_le _ _).trans
      (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ ‖G * L - L * G‖ + d' * ‖L‖ + d * ‖L‖ :=
      add_le_add (add_le_add (norm_compress_le V _) h1) h2
    _ = _ := by ring

lemma compressed_commutator_bound (V : K →ₗᵢ[ℂ] H)
    (G L : H →L[ℂ] H) (J : K →L[ℂ] K) {c ε : ℝ}
    (hG : ‖G * L - L * G‖ ≤ ε * ‖L‖)
    (hR : ‖G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp J‖ ≤ 2*c*ε)
    (hR' : ‖G.adjoint.comp V.toContinuousLinearMap -
      V.toContinuousLinearMap.comp J.adjoint‖ ≤ 2*c*ε) :
    ‖J * compress V L - compress V L * J‖ ≤ (1+4*c)*ε*‖L‖ := by
  calc
    _ ≤ ‖G * L - L * G‖ + (2*c*ε + 2*c*ε)*‖L‖ :=
      norm_compression_commutator_le V G L J hR hR'
    _ ≤ ε*‖L‖ + (2*c*ε + 2*c*ε)*‖L‖ := add_le_add hG le_rfl
    _ = _ := by ring

end Kadison.FreeCorner

namespace Kadison.FiniteCompression

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [CompleteSpace H] [DecidableEq I] in
lemma norm_sum_sq (x : I → H) (h : ∀ i j, i ≠ j → inner ℂ (x i) (x j) = 0) :
    ‖∑ i, x i‖^2 = ∑ i, ‖x i‖^2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_sum_diagonal x x h, map_sum]
  exact Finset.sum_congr rfl (fun i _ => (norm_sq_eq_re_inner (𝕜 := ℂ) (x i)).symm)

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma norm_average_le (c : ℝ) (U : I → K →L[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x : K, inner ℂ (U i x) (U j x) = 0)
    (hscale : c^2 * Fintype.card I = 1) {d : ℝ} (hd : 0 ≤ d)
    (hU : ∀ i, ‖U i‖ ≤ d) : ‖average c U‖ ≤ d := by
  apply (average c U).opNorm_le_bound hd
  intro x
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg x))).mp
  rw [average_apply, norm_smul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, norm_sum_sq _ (fun i j hij => horth i j hij x)]
  calc
    c^2 * ∑ i, ‖U i x‖^2 ≤ c^2 * ∑ _i : I, (d*‖x‖)^2 := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hd (norm_nonneg x))).mpr
      exact ((U i).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hU i) (norm_nonneg x))
    _ = (d*‖x‖)^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, hscale, one_mul]

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma comp_sum' (U : I → K →L[ℂ] H) (G : H →L[ℂ] H) :
    G.comp (∑ i, U i) = ∑ i, G.comp (U i) := by
  ext x
  simp

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma sum_comp' (U : I → K →L[ℂ] H) (B : K →L[ℂ] K) :
    (∑ i, U i).comp B = ∑ i, (U i).comp B := by
  ext x
  simp

omit [CompleteSpace H] [CompleteSpace K] [DecidableEq I] in
lemma average_error (c : ℝ) (U : I → K →L[ℂ] H) (G : H →L[ℂ] H) (B : K →L[ℂ] K) :
    G.comp (average c U) - (average c U).comp B =
      average c (fun i => G.comp (U i) - (U i).comp B) := by
  simp only [average, comp_smul, smul_comp, comp_sum', sum_comp',
    Finset.sum_sub_distrib, smul_sub]

omit [DecidableEq I] in
lemma average_compression (c : ℝ) (U : I → K →L[ℂ] H) (T : H →L[ℂ] H) :
    ((average c U).adjoint.comp T).comp (average c U) =
      ((c : ℂ)^2) • ∑ i, ∑ j, ((U i).adjoint.comp T).comp (U j) := by
  unfold average
  rw [map_smulₛₗ, map_sum]
  have hc : starRingEnd ℂ (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
  rw [hc]
  ext x
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    sum_apply, map_smul, map_sum]
  simp only [Finset.smul_sum, smul_smul, pow_two]
  rw [Finset.sum_comm]

omit [DecidableEq I] in
lemma average_compression_entries (c : ℝ) (U : I → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (hscale : c^2 * Fintype.card I = 1)
    (T : H →L[ℂ] H) (S : K →L[ℂ] K) (u : ℂ) (a b : I → I → ℂ)
    (hentry : ∀ i j, ((U i).toContinuousLinearMap.adjoint.comp T).comp
      (U j).toContinuousLinearMap = u • (a i j • 1 + b i j • S)) :
    FreeCorner.compress (averageIsometry c U horth hscale) T =
      u • (((c : ℂ)^2 * ∑ i, ∑ j, a i j) • 1 +
          ((c : ℂ)^2 * ∑ i, ∑ j, b i j) • S) := by
  rw [FreeCorner.compress, averageIsometry_toCLM, average_compression]
  simp only [hentry, smul_add, smul_smul, Finset.sum_add_distrib,
    ← Finset.sum_smul, ← Finset.mul_sum]
  module

end Kadison.FiniteCompression

namespace Kadison.FiniteHankel

open scoped BigOperators InnerProductSpace

open ContinuousLinearMap FiniteCompression

variable {H K : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

theorem norm_commutator_le_of_finite_entries
    (N : ℕ) (hN : 0 < N) (U : Fin N → K →ₗᵢ[ℂ] H)
    (horth : ∀ i j, i ≠ j → ∀ x y : K, inner ℂ (U i x) (U j y) = 0)
    (G L : H →L[ℂ] H) (B S : K →L[ℂ] K) (u c ε : ℝ)
    (hu : 0 < u) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hL : ‖L‖ ≤ 4*u)
    (hG : ‖G*L-L*G‖ ≤ ε*‖L‖)
    (hR : ∀ i, ‖G.comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp B‖ ≤ 2*c*ε)
    (hR' : ∀ i, ‖G.adjoint.comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp B.adjoint‖ ≤ 2*c*ε)
    (hRorth : ∀ i j, i ≠ j → ∀ x : K,
      inner ℂ (G (U i x) - U i (B x)) (G (U j x) - U j (B x)) = 0)
    (hRorth' : ∀ i j, i ≠ j → ∀ x : K,
      inner ℂ (G.adjoint (U i x) - U i (B.adjoint x))
        (G.adjoint (U j x) - U j (B.adjoint x)) = 0)
    (a : Fin N → Fin N → ℂ)
    (hentry : ∀ i j, ((U i).toContinuousLinearMap.adjoint.comp L).comp
      (U j).toContinuousLinearMap = (u : ℂ) • (a i j • 1 +
        (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2)) • S)) :
    ‖B*S-S*B‖ ≤ 16*(1+4*c)*ε := by
  let v : ℝ := (Real.sqrt (N : ℝ))⁻¹
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hv2 : v^2 = (N : ℝ)⁻¹ := by
    dsimp [v]
    rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  have hscale : v^2 * Fintype.card (Fin N) = 1 := by
    rw [hv2, Fintype.card_fin, inv_mul_cancel₀ hn]
  let V := averageIsometry v U horth hscale
  have hRV : ‖G.comp V.toContinuousLinearMap - V.toContinuousLinearMap.comp B‖ ≤ 2*c*ε := by
    rw [averageIsometry_toCLM, average_error]
    exact norm_average_le v _ (fun i j hij x => hRorth i j hij x) hscale (by positivity) hR
  have hRV' : ‖G.adjoint.comp V.toContinuousLinearMap -
      V.toContinuousLinearMap.comp B.adjoint‖ ≤ 2*c*ε := by
    rw [averageIsometry_toCLM, average_error]
    exact norm_average_le v _ (fun i j hij x => hRorth' i j hij x) hscale (by positivity) hR'
  have hb : (v : ℂ)^2 * ∑ i : Fin N, ∑ j : Fin N,
      (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2)) = 1/4 := by
    have h : v^2 * ∑ i : Fin N, ∑ j : Fin N,
        (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2) = 1/4 := by
      rw [hv2]
      exact FejerTest.hankel_average N hN
    simpa only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_sum,
      Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using
      congrArg Complex.ofReal h
  have hcomp : FreeCorner.compress V L = (u : ℂ) •
      (((v : ℂ)^2 * ∑ i, ∑ j, a i j) • 1 + (1/4 : ℂ) • S) := by
    have h := average_compression_entries v U horth hscale L S (u : ℂ) a
      (fun i j => (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2))) hentry
    rw [hb] at h
    exact h
  have heq : B * FreeCorner.compress V L - FreeCorner.compress V L * B =
      ((u/4 : ℝ) : ℂ) • (B*S-S*B) := by
    rw [hcomp]
    simp only [smul_add, mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one,
      one_mul, smul_sub, smul_smul, Complex.ofReal_div, Complex.ofReal_ofNat]
    module
  have hbound := FreeCorner.compressed_commutator_bound V G L B hG hRV hRV'
  rw [heq, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos hu (by norm_num))] at hbound
  have hbound' : (u/4)*‖B*S-S*B‖ ≤ (1+4*c)*ε*(4*u) :=
    hbound.trans (mul_le_mul_of_nonneg_left hL (by positivity))
  apply (mul_le_mul_iff_right₀ (div_pos hu (by norm_num : (0 : ℝ) < 4))).mp
  calc
    _ ≤ (1+4*c)*ε*(4*u) := hbound'
    _ = (u/4)*(16*(1+4*c)*ε) := by ring

end Kadison.FiniteHankel

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma headSpace_le_tailSpace_orthogonal (i : ι) :
    headSpace t S i ≤ (tailSpace t S i)ᗮ := by
  apply (headSpan t S i).topologicalClosure_minimal ?_ (Submodule.isClosed_orthogonal _)
  rw [tailSpace, Submodule.orthogonal_closure]
  apply Submodule.span_le.mpr
  rintro x ⟨z, hz, ⟨a, z, rfl, ha⟩, rfl⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, hiw, rfl⟩ := hy
    rw [inner_wordVector]
    change t.functional.toLinearMap (star (word w) * word (a :: z)) = 0
    rw [gram_word (fun a => map_star t.functional a) t.normalized hfree _ _ hw hz]
    exact gram_zero_of_colors_ne _ _ (colors_ne_prepend t S hiw a ha)
  | zero => simp
  | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
  | smul c y _ hy => simp [inner_smul_left, hy]

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockWords2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i ≠ j)

include hfree hij in
lemma blockVector_cons_nil (x : Letters t S i j)
    (xs : List (Letters t S i j)) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S (x::xs) z) (blockVector t S ([] : List (Letters t S i j)) v) = 0 := by
  rw [blockVector_cons, ← ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ _ ((star (t.functional.gnsStarAlgHom (letterValue t S j x.1))) _) = 0
  rw [← map_star]
  have hm : t.functional.gnsStarAlgHom (star (letterValue t S j x.1))
      (blockVector t S ([] : List (Letters t S i j)) v) =
      (t.functional.toPreGNS (star (letterValue t S j x.1)*v) : t.functional.GNS) := by
    simp [blockVector_nil, PositiveLinearMap.gnsStarAlgHom]
  rw [hm]
  have ht := factor_vector_mem_tailSpace t S hij (mul_mem (star_mem x.1.property.1) hv)
  have hh := headSpace_le_tailSpace_orthogonal t S hfree i
    (creation_mem_headSpace t S i (a := letterValue t S i x.2) x.2.property.1 x.2.property.2
      (blockVector_mem_tail t S hij xs hz))
  exact inner_eq_zero_symm.mp (hh _ ht)

include hfree hij in
lemma blockVector_orthogonal (xs ys : List (Letters t S i j))
    (hlen : xs.length ≠ ys.length) {z v : A} (hz : z ∈ S j) (hv : v ∈ S j) :
    inner ℂ (blockVector t S xs z) (blockVector t S ys v) = 0 := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact (hlen rfl).elim
    | cons y ys => exact inner_eq_zero_symm.mp (blockVector_cons_nil t S hfree hij y ys hv hz)
  | cons x xs ih =>
    cases ys with
    | nil => exact blockVector_cons_nil t S hfree hij x xs hz hv
    | cons y ys =>
      rw [blockVector_cons_gram t S hfree hij x y xs ys hz hv,
        ih ys (by simpa using hlen), mul_zero]

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeBlockTensor2
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor FreeCreation UniformSpace

open scoped InnerProductSpace TensorProduct

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap) {i j : ι} (hij : i≠j)

include hfree hij in
lemma inner_blockReadPre_ne {n m : ℕ} (hnm : n≠m)
    (x : blockTensor t S i j n) (y : blockTensor t S i j m) :
    inner ℂ (blockReadPre t S n x) (blockReadPre t S m y)=0 := by
  have hx : x ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) n)) := by rw [span_blockPure]; trivial
  have hy : y ∈ Submodule.span ℂ (Set.range (blockPure t S (i := i) (j := j) m)) := by rw [span_blockPure]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v,rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨w,rfl⟩ := hy
      rw [←Completion.inner_coe, blockReadPre_pure, blockReadPre_pure]
      exact blockVector_orthogonal t S hfree hij _ _
        (by simpa only [paramLetters_length] using hnm)
        (paramEnd t S n v).property (paramEnd t S m w).property
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add, inner_add_right, hx, hy, add_zero]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy, mul_zero]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, inner_add_left, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx, mul_zero]

include hfree hij in
lemma inner_endpointRead_ne {n m : ℕ} (hnm : n≠m)
    (x : endpointTensor t S i j n) (y : endpointTensor t S i j m) :
    inner ℂ (endpointRead t S n x) (endpointRead t S m y)=0 := by
  induction x using endpointTensor_induction_on t S n with
  | h0 => simp
  | ha x z hx hz => simp only [map_add, inner_add_left, hx, hz, add_zero]
  | ht a x =>
    induction y using endpointTensor_induction_on t S m with
    | h0 => simp
    | ha y z hy hz => simp only [map_add, inner_add_right, hy, hz, add_zero]
    | ht b y =>
      rw [←Completion.inner_coe, endpointRead_tmul, endpointRead_tmul,
        inner_mul_two_tailSpace t S hfree i (a := factorValue t S i a)
          (b := factorValue t S i b) a.property b.property
          (blockReadPre_mem_tail t S hij n x) (blockReadPre_mem_tail t S hij m y),
        Completion.inner_coe, inner_blockReadPre_ne t S hfree hij hnm, mul_zero]

lemma levelEmbedding_orthogonal {n m : ℕ} (hnm : n≠m)
    (x : Completion (endpointTensor t S i j n)) (y : Completion (endpointTensor t S i j m)) :
    inner ℂ (levelEmbedding t S hfree hij n x) (levelEmbedding t S hfree hij m y) = 0 := by
  induction x, y using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
    rw [levelEmbedding_coe, levelEmbedding_coe, Completion.inner_coe]
    exact inner_endpointRead_ne t S hfree hij hnm x y

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCompressionNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

lemma gns_injective : Function.Injective t.functional.gnsStarAlgHom := by
  intro a b hab
  have h := congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS =>
    T (t.functional.toPreGNS 1 : t.functional.GNS)) hab
  have hab' : (t.functional.toPreGNS a : t.functional.GNS) =
      (t.functional.toPreGNS b : t.functional.GNS) := by
    simpa [PositiveLinearMap.gnsStarAlgHom] using h
  exact t.functional.toPreGNS.injective (Completion.coe_injective _ hab')

lemma norm_gns (a : A) : ‖t.functional.gnsStarAlgHom a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (gns_injective t) a

end Kadison.FreeCreation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeDihedralEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

variable (e b : Corner hp) (he : e∈cornerFactor hp (S false) hpD)
  (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
  (hb0 : halfCornerTrace hp t.functional.toLinearMap b=0)

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_projection_coe (heproj : IsStarProjection e) : IsStarProjection (e:A) where
  isSelfAdjoint := by
    show star (e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isSelfAdjoint.star_eq
  isIdempotentElem := by
    show (e:A)*(e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isIdempotentElem.eq

omit [PartialOrder A] [StarOrderedRing A] in
lemma sandwich_supported (heproj : IsStarProjection e) :
    (e:A)*((e:A)*(b:A)*(e:A))*(e:A)=(e:A)*(b:A)*(e:A) := by
  have h := (corner_projection_coe hp (e := e) heproj).isIdempotentElem.eq
  calc
    _ = ((e:A)*(e:A))*(b:A)*((e:A)*(e:A)) := by simp only [mul_assoc]
    _ = _ := by rw [h]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeFejerNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

lemma fejer_numeric_bound (u : ℝ) (m : ℕ) (hm : 0 < m) (hsize : 8≤(m:ℝ)*u) :
    4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹)+2*u≤4*u := by
  have hm' : 0<(m:ℝ) := by exact_mod_cast hm
  have hu : 0<u := (mul_pos_iff_of_pos_left hm').mp (lt_of_lt_of_le (by norm_num) hsize)
  have hi : 0≤(m:ℝ)⁻¹ := inv_nonneg.mpr hm'.le
  have hiu : 8*(m:ℝ)⁻¹ ≤ u := by
    rw [←div_eq_mul_inv]
    exact (div_le_iff₀ hm').2 (by simpa only [mul_comm] using hsize)
  have sq2 := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have squ := Real.sq_sqrt hu.le
  have sqi := Real.sq_sqrt hi
  have hs0 : 0≤4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹) := by positivity
  have hsq : (4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹))^2≤(2*u)^2 := by
    calc
      _ = 32*u*(m:ℝ)⁻¹ := by rw [mul_pow,mul_pow,mul_pow,sq2,squ,sqi]; ring
      _ ≤ (2*u)^2 := by nlinarith [mul_le_mul_of_nonneg_left hiu hu.le]
  have hs : 4*Real.sqrt 2*Real.sqrt u*Real.sqrt ((m:ℝ)⁻¹)≤2*u :=
    (sq_le_sq₀ hs0 (by positivity)).mp hsq
  linarith

include hfree htr hd hs hd0 hs0 hr hd2 hpform hpd hdp in
theorem free_fejer_gns_norm (e : Corner hp) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD) (m : ℕ) (hm : 0 < m)
    (hsize : 8≤(m:ℝ)*(halfCornerTrace hp t.functional.toLinearMap e).re) :
    ‖t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) m:Corner hp):A)*(e:A))‖≤
      4*(halfCornerTrace hp t.functional.toLinearMap e).re := by
  rw [FreeCreation.norm_gns]
  exact (free_fejer_norm t S hfree htr d s hd hs hd0 hs0 hr hd2
    hp hpform hpd hdp hpD e heproj he m hm).trans (fejer_numeric_bound _ m hm hsize)

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeSymmetry14
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology
open scoped TensorProduct
open UniformSpace
open scoped TensorProduct InnerProductSpace

namespace Kadison.FreeBlocks

open FreeWordTensor UniformSpace PreHilbert

open scoped ComplexOrder InnerProductSpace TensorProduct

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i j : ι) (hS : S i=f.range)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap) (hij : i≠j)

lemma sourceLevelEmbedding_orthogonal :
    OrthogonalFamily ℂ (fun n => sourceLevel t f hf S j n)
      (sourceLevelEmbedding t f hf S i j hS hfree hij) := by
  intro n m hnm x y
  exact levelEmbedding_orthogonal t S hfree hij hnm
    ((sourceLevelShuffle t f hf S i j hS n).symm x)
    ((sourceLevelShuffle t f hf S i j hS m).symm y)

end Kadison.FreeBlocks
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeNormalizedColumns
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace TensorProduct ComplexOrder

open UniformSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable {i j : ι} (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)
  (hS : S i=f.range) (hfree : Free S t.functional.toLinearMap) (hij : i≠j)

variable (d : D) (s : letterSpace t S j) (hs : ‖s‖=1)
  (x : letterSpace t S i) (hx : ‖x‖=1)

variable (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) d‖)

lemma normalizedColumn_apply (n : ℕ) (v : multiplicityLevel t S j 0) :
    normalizedColumn t S f hf hS hfree hij d s hs x hx hr n v=
      ((‖TracialGNS.algebraVector (factorTrace t f hf) d‖⁻¹:ℝ):ℂ) •
        repeatedOutput t S f hf hS hfree hij d x n (repeatInsertion t S s hs n v) := rfl

lemma repeatedOutput_orthogonal {n m : ℕ} (hnm : n≠m)
    (v : multiplicityLevel t S j n) (z : multiplicityLevel t S j m) :
    inner ℂ (repeatedOutput t S f hf hS hfree hij d x n v)
      (repeatedOutput t S f hf hS hfree hij d x m z)=0 := by
  exact sourceLevelEmbedding_orthogonal t f hf S i j hS hfree hij hnm _ _

lemma normalizedColumn_orthogonal : OrthogonalFamily ℂ
    (fun _ : ℕ => multiplicityLevel t S j 0)
    (normalizedColumn t S f hf hS hfree hij d s hs x hx hr) := by
  intro n m hnm v z
  simp only [normalizedColumn_apply t S f hf hS hfree hij d s hs x hx hr,inner_smul_left,inner_smul_right,
    repeatedOutput_orthogonal t S f hf hS hfree hij d x hnm,mul_zero]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeHankelEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {p : A} (hp : IsStarProjection p)

lemma projection_factor_trace (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    t.functional (e:A)=((‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2:ℝ):ℂ) := by
  have hn := (factorTrace t f hf).preGNS_norm_sq ((factorTrace t f hf).toPreGNS e0)
  have he := corner_projection_coe hp (e:=e) heproj
  symm
  simpa only [TracialGNS.algebraVector_apply,Completion.norm_coe,
    Complex.ofReal_pow,PositiveLinearMap.ofPreGNS_toPreGNS,pullbackState_apply,
    map_mul,map_star,heq,he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq] using hn

lemma halfCornerTrace_normalization (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    halfCornerTrace hp t.functional.toLinearMap e=
      ((2*‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2:ℝ):ℂ) := by
  rw [halfCornerTrace_apply,PositiveLinearMap.coe_toLinearMap,
    projection_factor_trace t f hf hp e0 e heq heproj]
  push_cast
  rfl

lemma halfCornerTrace_normalization_re (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    (halfCornerTrace hp t.functional.toLinearMap e).re=
      2*‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2 := by
  rw [halfCornerTrace_normalization t f hf hp e0 e heq heproj,Complex.ofReal_re]

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeHankelBound
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

local notation "CE" => Completion (factorSpace t S true)

lemma concrete_hankel_assembly
    (N : ℕ) (hN : 0 < N) (U : Fin N → CE →ₗᵢ[ℂ] t.functional.GNS)
    (horth : ∀ i j, i ≠ j → ∀ x y : CE, inner ℂ (U i x) (U j y) = 0)
    (G L : t.functional.GNS →L[ℂ] t.functional.GNS) (B Q : CE →L[ℂ] CE) (u c ε : ℝ)
    (hu : 0 < u) (hc : 0 ≤ c) (hε : 0 ≤ ε)
    (hL : ‖L‖ ≤ 4*u)
    (hG : ‖G*L-L*G‖ ≤ ε*‖L‖)
    (hR : ∀ i, ‖G.comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp B‖ ≤ 2*c*ε)
    (hR' : ∀ i, ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=t.functional.GNS) (F:=t.functional.GNS) G).comp (U i).toContinuousLinearMap -
      (U i).toContinuousLinearMap.comp (ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=CE) B)‖ ≤ 2*c*ε)
    (hRorth : ∀ i j, i ≠ j → ∀ x : CE,
      inner ℂ (G (U i x) - U i (B x)) (G (U j x) - U j (B x)) = 0)
    (hRorth' : ∀ i j, i ≠ j → ∀ x : CE,
      inner ℂ ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=t.functional.GNS) (F:=t.functional.GNS) G) (U i x) - U i ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=CE) B) x))
        ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=t.functional.GNS) (F:=t.functional.GNS) G) (U j x) - U j ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=CE) B) x)) = 0)
    (a : Fin N → Fin N → ℂ)
    (hentry : ∀ i j, ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=CE) (F:=t.functional.GNS) (U i).toContinuousLinearMap).comp L).comp
      (U j).toContinuousLinearMap = (u : ℂ) • (a i j • 1 +
        (Complex.ofReal (((2*N : ℝ) - i.val - j.val - 1)/(2*N : ℝ)^2)) • Q)) :
    ‖B*Q-Q*B‖ ≤ 16*(1+4*c)*ε := by
  exact @FiniteHankel.norm_commutator_le_of_finite_entries
    t.functional.GNS (Completion (factorSpace t S true))
    (inferInstanceAs (NormedAddCommGroup t.functional.GNS))
    (inferInstanceAs (InnerProductSpace ℂ t.functional.GNS))
    (inferInstanceAs (CompleteSpace t.functional.GNS))
    (inferInstanceAs (NormedAddCommGroup (Completion (factorSpace t S true))))
    (inferInstanceAs (InnerProductSpace ℂ (Completion (factorSpace t S true))))
    (inferInstanceAs (CompleteSpace (Completion (factorSpace t S true))))
    N hN U horth G L B Q u c ε hu hc hε hL hG hR hR' hRorth hRorth' a hentry

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f) (hS : S false=f.range)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)
local notation "sl" => (letterOf t S true (s:A) hs hs0)
local notation "sn" => (norm_letterOf_unitary t S true s hs hs0)
local notation "dl" => (letterOf t S false (d:A) hd hd0)
local notation "dn" => (norm_letterOf_unitary t S false d hd hd0)

variable (G : t.functional.GNS →L[ℂ] t.functional.GNS)

variable (B : ∀ n, multiplicityLevel t S true n →L[ℂ] multiplicityLevel t S true n)

variable (hB : ∀ n a (x : letterSpace t S false) v,
  G (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n (B n v))

variable (hB' : ∀ n a (x : letterSpace t S false) v,
  G.adjoint (repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n v)=
    repeatedOutput t S f hf hS hfree Bool.false_ne_true a x n
      ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) v))

include htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp hpD hB hB' in
theorem free_hankel_bound_oai (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (c ε : ℝ) (hc : 0 ≤ c) (hε : 0≤ε)
    (hsmall : ∀ a : A, (e:A)*a*(e:A)=a →
      ‖G*t.functional.gnsStarAlgHom a-t.functional.gnsStarAlgHom a*G‖≤ε*‖a‖)
    (hprop : ∀ n v, ‖B n (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n (B 0 v)‖≤(2*c*ε)*‖v‖)
    (hprop' : ∀ n v,
      ‖(ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true n)
        (F:=multiplicityLevel t S true n) (B n)) (repeatInsertion t S sl sn n v)-
      repeatInsertion t S sl sn n
        ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=multiplicityLevel t S true 0)
          (F:=multiplicityLevel t S true 0) (B 0)) v)‖≤(2*c*ε)*‖v‖) :
    ‖B 0*baseAction t S hfree (s:A)-baseAction t S hfree (s:A)*B 0‖≤16*(1+4*c)*ε := by
  let E := Completion (factorSpace t S true)
  let u : ℝ := (halfCornerTrace hp t.functional.toLinearMap e).re
  have hu : 0<u := by
    dsimp only [u]
    rw [halfCornerTrace_normalization_re t f hf hp e0 e heq heproj]
    positivity
  obtain ⟨N,hNsize⟩ := exists_nat_gt (4/u)
  have hN : 0 < N := by
    have : (0:ℝ)<N := lt_trans (div_pos (by norm_num) hu) hNsize
    exact_mod_cast this
  have hsize : 8≤((2*N:ℕ):ℝ)*u := by
    have hh := (div_lt_iff₀ hu).mp hNsize
    push_cast
    nlinarith
  let U : Fin N → E →ₗᵢ[ℂ] t.functional.GNS := fun i =>
    normalizedColumn t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr i.val
  let L := t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A))
  have horth : ∀ i j : Fin N, i≠j → ∀ x y : E, inner ℂ (U i x) (U j y)=0 := by
    intro i j hij x y
    exact normalizedColumn_orthogonal t S f hf hS hfree Bool.false_ne_true e0 sl sn dl dn hr
      (mt Fin.ext hij) x y
  have hL : ‖L‖≤4*u := free_fejer_gns_norm t S hfree htr d s hd hs hd0 hs0 hrot hd2
    hp hpform hpd hdp hpD e heproj he (2*N) (by omega) hsize
  have hG : ‖G*L-L*G‖≤ε*‖L‖ := by
    dsimp only [L]
    rw [FreeCreation.norm_gns]
    exact hsmall _ (sandwich_supported hp e (fejerCorner hp (d*s) (2*N)) heproj)
  obtain ⟨hR,hR',hRorth,hRorth'⟩ := normalized_errors t S hfree f hf hS d s hd hs hd0 hs0
    G B hB hB' e0 hr N (2*c*ε) (by positivity) hprop hprop'
  let a : Fin N → Fin N → ℂ := fun i j => 2*t.functional
    (wave (d*s) ((i.val:ℤ)-j.val)*((fejerCorner hp (d*s) (2*N):Corner hp):A))
  have hentry : ∀ i j : Fin N, ((ContinuousLinearMap.adjoint (𝕜:=ℂ) (E:=E) (F:=t.functional.GNS)
      (U i).toContinuousLinearMap).comp L).comp
      (U j).toContinuousLinearMap=(u:ℂ) • (a i j • (1:E→L[ℂ]E)+
        Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2) • baseAction t S hfree (s:A)) := by
    intro i j
    exact normalized_fejer_entry t S hfree f hf hS htr d s hd hs hd0 hs0 hrot hd2 hs2
      hp hpform hpd hdp hpD e0 e heq heproj he hr N hN i j
  have hfinal := concrete_hankel_assembly t S
    N hN U horth G L (B 0) (baseAction t S hfree (s:A)) u c ε hu hc hε
    hL hG hR hR' hRorth hRorth' a hentry
  exact hfinal

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.free_hankel_bound_oai := @OAI.Kadison.FreeBlocks.free_hankel_bound_oai
