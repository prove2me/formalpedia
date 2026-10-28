-- Prove2me | solution 1 for OAI.DimensionTen.main_channel_conditional_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T22:13:22.17307+00:00
-- url     : https://prove2.me/submissions/b8ee2159-7c97-4c4f-aab9-ec1b8807a78f

import Mathlib
import Definitions.Def_DimensionTenChannel
import Definitions.Def_OAIQ057D013
import Theorems.Thm_OAI_DimensionTen_linear_composite_not_separable_s2

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_ChannelModel
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix

namespace ChannelCompletion
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

omit [Fintype m] in
lemma amplify_ad {k : Type} [Fintype k] [DecidableEq k]
    (V : Matrix m n ℂ) (X : Mat (k × n)) :
    amplify (ad V) X = ((1 : Mat k) ⊗ₖ V) * X * ((1 : Mat k) ⊗ₖ V)ᴴ := by
  ext a b
  rcases a with ⟨a,i⟩
  rcases b with ⟨b,j⟩
  change (∑ r : n, (∑ s : n, V i s * X (a,s) (b,r)) * star (V j r)) =
    ∑ r : k × n, (∑ s : k × n, ((1 : Mat k) a s.1 * V i s.2) * X s r) *
      star ((1 : Mat k) b r.1 * V j r.2)
  simp [Fintype.sum_prod_type, Matrix.one_apply, ite_mul, apply_ite,
    Finset.sum_mul]

lemma cp_ad (V : Matrix m n ℂ) : CP (ad V) := by
  intro k _ X hX
  classical
  rw [amplify_ad]
  exact hX.mul_mul_conjTranspose_same _

omit [Fintype n] [Fintype m] [Fintype p] in
lemma cp_comp {F : Map n m} {G : Map m p} (hG : CP G) (hF : CP F) : CP (G.comp F) := by
  intro k _ X hX
  exact hG k (amplify F X) (hF k X hX)

omit [Fintype n] [Fintype m] in
lemma cp_add {F G : Map n m} (hF : CP F) (hG : CP G) : CP (F + G) := by
  intro k _ X hX
  exact (hF k X hX).add (hG k X hX)

omit [Fintype n] [Fintype m] in
lemma cp_smul {F : Map n m} (hF : CP F) {c : ℝ} (hc : 0 ≤ c) :
    CP ((c : ℂ) • F) := by
  intro k _ X hX
  exact (hF k X hX).smul (show (0 : ℂ) ≤ c by exact_mod_cast hc)

omit [Fintype n] [Fintype m] in
lemma amplify_omega [DecidableEq n] (F : Map n m) :
    amplify F (Matrix.vecMulVec (omega (n := n)) (star omega)) = choi F := by
  ext ⟨i,a⟩ ⟨j,b⟩
  change F _ a b = F _ a b
  apply congrArg (fun X : Mat n => F X a b)
  ext x y
  simp only [Matrix.vecMulVec_apply, omega, Pi.star_apply, Matrix.single_apply]
  by_cases hix : i = x <;> by_cases hjy : j = y <;> simp [hix, hjy]

omit [Fintype m] in
lemma cp_choi [DecidableEq n] {F : Map n m} (hF : CP F) : (choi F).PosSemidef := by
  rw [← amplify_omega]
  exact hF n _ (Matrix.posSemidef_vecMulVec_self_star _)

omit [Fintype n] in
lemma effect_eq_sum [DecidableEq n] (F : Map n m) :
    effect F = ∑ a : m, (choi F)ᵀ.submatrix (fun i => (i,a)) (fun i => (i,a)) := by
  ext i j
  simp [effect, choi, Matrix.trace, Matrix.sum_apply]

lemma effect_psd [DecidableEq n] {F : Map n m} (hF : CP F) : (effect F).PosSemidef := by
  rw [effect_eq_sum]
  exact Matrix.posSemidef_sum _ (fun a _ => (cp_choi hF).transpose.submatrix _)

lemma effect_trace [DecidableEq n] (F : Map n m) (X : Mat n) :
    Matrix.trace (effect F * X) = Matrix.trace (F X) := by
  induction X using Matrix.induction_on' with
  | h_zero => simp
  | h_add X Y hX hY => simp [Matrix.mul_add, hX, hY]
  | h_std_basis i j c =>
    rw [Matrix.trace_mul_single]
    have he : Matrix.single i j c = c • Matrix.single i j (1 : ℂ) := by
      simp [Matrix.smul_single]
    rw [he, map_smul, Matrix.trace_smul]
    change Matrix.trace (F (Matrix.single i j 1)) * c =
      c * Matrix.trace (F (Matrix.single i j 1))
    exact mul_comm _ _

lemma coefficient_pos [DecidableEq n] {F : Map n m} (hF : CP F) :
    0 < coefficient F := by
  have h := Complex.nonneg_iff.mp (effect_psd hF).trace_nonneg
  exact one_div_pos.mpr (by linarith [h.1])

end ChannelCompletion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_TraceCompletion
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m]

lemma psd_trace_bound [DecidableEq n] {A : Mat n} (hA : A.PosSemidef) :
    (Matrix.trace A • (1 : Mat n) - A).PosSemidef := by
  let U : Mat n := hA.isHermitian.eigenvectorUnitary
  have hU : U * Uᴴ = 1 := Unitary.coe_mul_star_self _
  have hspec : A = U * Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) * Uᴴ := by
    simpa only [U, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def, RCLike.ofReal_eq_complex_ofReal] using
      hA.isHermitian.spectral_theorem
  have hD : (Matrix.diagonal (fun i => Matrix.trace A -
      (hA.isHermitian.eigenvalues i : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    rw [hA.isHermitian.trace_eq_sum_eigenvalues]
    have he : hA.isHermitian.eigenvalues i ≤ ∑ j, hA.isHermitian.eigenvalues j :=
      Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
    have hc : ((hA.isHermitian.eigenvalues i : ℝ) : ℂ) ≤
        ((∑ j, hA.isHermitian.eigenvalues j : ℝ) : ℂ) := by exact_mod_cast he
    simpa using sub_nonneg.mpr hc
  have hd : Matrix.diagonal (fun i => Matrix.trace A -
        (hA.isHermitian.eigenvalues i : ℂ)) =
      Matrix.trace A • (1 : Mat n) -
        Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have hh := hD.mul_mul_conjTranspose_same U
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, hU, ← hspec] at hh
  exact hh

lemma trace_effect_real [DecidableEq n] {F : Map n m} (hF : CP F) :
    ((Matrix.trace (effect F)).re : ℂ) = Matrix.trace (effect F) := by
  have h := Complex.nonneg_iff.mp (effect_psd hF).trace_nonneg
  apply Complex.ext <;> simp [← h.2]

lemma coefficient_trace [DecidableEq n] {F : Map n m} (hF : CP F) :
    (coefficient F : ℂ) * (1 + Matrix.trace (effect F)) = 1 := by
  rw [← trace_effect_real hF]
  have ht : 0 ≤ (Matrix.trace (effect F)).re :=
    (Complex.nonneg_iff.mp (effect_psd hF).trace_nonneg).1
  simp only [coefficient, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add]
  exact div_mul_cancel₀ _ (by exact_mod_cast (show (1 : ℝ) +
    (Matrix.trace (effect F)).re ≠ 0 by linarith))

lemma defect_psd [DecidableEq n] {F : Map n m} (hF : CP F) : (defect F).PosSemidef := by
  have hc : (0 : ℂ) ≤ coefficient F := by exact_mod_cast (coefficient_pos hF).le
  have he : defect F = (coefficient F : ℂ) •
      (Matrix.trace (effect F) • (1 : Mat n) - effect F) +
      (coefficient F : ℂ) • (1 : Mat n) := by
    have hs : (coefficient F : ℂ) * Matrix.trace (effect F) + (coefficient F : ℂ) = 1 := by
      linear_combination coefficient_trace hF
    rw [smul_sub, smul_smul]
    unfold defect
    have hs' : (coefficient F : ℂ) * Matrix.trace (effect F) = 1 - (coefficient F : ℂ) := by
      linear_combination hs
    rw [hs', sub_smul, one_smul]
    module
  rw [he]
  exact ((psd_trace_bound (effect_psd hF)).smul hc).add (Matrix.PosSemidef.one.smul hc)

end ChannelCompletion

namespace ChannelCompletion
variable {n m : Type} [Fintype n] [Fintype m]

lemma partial_trace_psd {k : Type} [Fintype k] {X : Mat (k × n)} (hX : X.PosSemidef) :
    Matrix.PosSemidef (fun a b : k => Matrix.trace (fun i j : n => X (a,i) (b,j))) := by
  have he : (fun a b : k => Matrix.trace (fun i j : n => X (a,i) (b,j))) =
      ∑ i : n, X.submatrix (fun a => (a,i)) (fun a => (a,i)) := by
    ext a b
    simp [Matrix.trace, Matrix.diag, Matrix.sum_apply]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun i _ => hX.submatrix _)

lemma flag_psd (d : ℕ) : (flagProjection d).PosSemidef := by
  have h := Matrix.posSemidef_vecMulVec_self_star (Pi.single (flag d) (1 : ℂ))
  simpa [flagProjection, Matrix.single_eq_single_vecMulVec_single] using h

lemma cp_prepareTrace (d : ℕ) : CP (prepareTrace (n := n) d) := by
  classical
  intro k _ X hX
  let Y : Mat k := fun a b => Matrix.trace (fun i j : n => X (a,i) (b,j))
  have hY : Y.PosSemidef := partial_trace_psd hX
  change (Y ⊗ₖ flagProjection d).PosSemidef
  exact hY.kronecker (flag_psd d)

lemma cp_measureFlag (d : ℕ) {A : Mat n} (hA : A.PosSemidef) : CP (measureFlag d A) := by
  classical
  let R : Mat n := CFC.sqrt A
  have hR : Rᴴ * R = A := by
    have hh : R.IsHermitian :=
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
    rw [hh.eq]
    exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  have he : measureFlag d A = (prepareTrace d).comp (ad R) := by
    ext X i j
    simp only [measureFlag, prepareTrace, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.comp_apply, ad_apply]
    rw [Matrix.trace_mul_cycle, hR]
  rw [he]
  exact cp_comp (cp_prepareTrace d) (cp_ad R)

end ChannelCompletion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_Compression
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {a b c : Type} [Fintype a] [Fintype b] [Fintype c]

omit [Fintype a] [Fintype c] in
lemma coord_compress [DecidableEq b] (e : a → b) (f : c → b) (X : Mat b) :
    (coord e)ᴴ * X * coord f = X.submatrix e f := by
  ext i j
  simp [coord, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply,
    apply_ite, ite_mul]

omit [Fintype a] [Fintype c] in
lemma coord_inner [DecidableEq b] (e : a → b) (f : c → b) :
    (coord e)ᴴ * coord f = fun i j => if e i = f j then 1 else 0 := by
  ext i j
  simp [coord, Matrix.mul_apply, Matrix.conjTranspose_apply, apply_ite, eq_comm]

omit [Fintype a] in
lemma coord_isometry [DecidableEq a] [DecidableEq b] (e : a → b) (he : Function.Injective e) :
    (coord e)ᴴ * coord e = 1 := by
  rw [coord_inner]
  ext i j
  simp [Matrix.one_apply, he.eq_iff]

omit [Fintype a] [Fintype b] in
lemma coord_transpose [DecidableEq b] (e : a → b) : (coord e)ᵀ = (coord e)ᴴ := by
  ext i j
  simp [coord, Matrix.conjTranspose_apply, Matrix.transpose_apply, apply_ite]

omit [Fintype b] in
lemma coord_single [DecidableEq a] [DecidableEq b] (e : a → b) (i j : a) :
    ad (coord e) (Matrix.single i j 1) = Matrix.single (e i) (e j) 1 := by
  ext x y
  have hmul (r : a) : (coord e * Matrix.single i j (1 : ℂ)) x r =
      if r = j then coord e x i else 0 := by
    by_cases hr : r = j
    · subst r
      simp
    · simp [hr, Matrix.mul_single_apply_of_ne]
  rw [ad_apply, Matrix.mul_apply]
  simp_rw [hmul]
  simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  simp only [coord, Matrix.conjTranspose_apply, Matrix.single_apply, apply_ite, star_one, star_zero]
  by_cases hx : x = e i <;> by_cases hy : y = e j <;> simp [hx, hy, eq_comm]

omit [Fintype a] [Fintype b] [Fintype c] in
lemma coord_kronecker [DecidableEq b] {d : Type} [DecidableEq d]
    (e : a → b) (f : c → d) :
    coord e ⊗ₖ coord f = coord (fun x : a × c => (e x.1, f x.2)) := by
  ext ⟨x,y⟩ ⟨i,j⟩
  simp only [Matrix.kronecker_apply, coord, Prod.mk.injEq]
  by_cases hx : x = e i <;> by_cases hy : y = f j <;> simp [hx, hy]

@[simp] lemma W0_isometry (d : ℕ) : (W0 d)ᴴ * W0 d = 1 := by
  exact coord_isometry _ (by intro i j h; simpa [first] using h)

@[simp] lemma W1_isometry (d : ℕ) : (W1 d)ᴴ * W1 d = 1 := by
  exact coord_isometry _ (by intro i j h; simpa [second] using h)

@[simp] lemma W0_W1 (d : ℕ) : (W0 d)ᴴ * W1 d = 0 := by
  rw [W0, W1, coord_inner]
  ext i j
  simp [first, second]

@[simp] lemma W1_W0 (d : ℕ) : (W1 d)ᴴ * W0 d = 0 := by
  rw [W0, W1, coord_inner]
  ext i j
  simp [first, second]

@[simp] lemma W0_flag (d : ℕ) : (W0 d)ᴴ * flagProjection d * W0 d = 0 := by
  rw [W0, coord_compress]
  ext i j
  simp [flagProjection, first, flag]

@[simp] lemma W1_flag (d : ℕ) : (W1 d)ᴴ * flagProjection d * W1 d = 0 := by
  rw [W1, coord_compress]
  ext i j
  simp [flagProjection, second, flag]

end ChannelCompletion

namespace ChannelCompletion

lemma theta_decomposition (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    theta d F G =
      (coefficient G : ℂ) • ((ad (W0 d)).comp (G.comp (ad (W1 d)ᴴ))) +
      (coefficient F : ℂ) • ((ad (W1 d)).comp (F.comp (ad (W0 d)ᴴ))) +
      (measureFlag d (defect F)).comp (ad (W0 d)ᴴ) +
      (measureFlag d (defect G)).comp (ad (W1 d)ᴴ) +
      measureFlag d (flagProjection d) := by
  apply LinearMap.ext
  intro X
  simp only [theta, measureFlag, LinearMap.coe_mk, AddHom.coe_mk,
    LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smul_apply,
    ad_apply, Matrix.conjTranspose_conjTranspose, add_smul]
  simp only [flagProjection, Matrix.trace_single_mul, one_smul]
  abel

lemma theta_cp (d : ℕ) {F G : Map (Fin d) (Fin d)} (hF : CP F) (hG : CP G) :
    CP (theta d F G) := by
  rw [theta_decomposition]
  apply cp_add
  · apply cp_add
    · apply cp_add
      · exact cp_add
          (cp_smul (cp_comp (cp_ad _) (cp_comp hG (cp_ad _))) (coefficient_pos hG).le)
          (cp_smul (cp_comp (cp_ad _) (cp_comp hF (cp_ad _))) (coefficient_pos hF).le)
      · exact cp_comp (cp_measureFlag _ (defect_psd hF)) (cp_ad _)
    · exact cp_comp (cp_measureFlag _ (defect_psd hG)) (cp_ad _)
  · exact cp_measureFlag _ (flag_psd d)

lemma theta_transpose_decomposition (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    transposeMap.comp (theta d F G) =
      (coefficient G : ℂ) • ((ad (W0 d)).comp ((transposeMap.comp G).comp (ad (W1 d)ᴴ))) +
      (coefficient F : ℂ) • ((ad (W1 d)).comp ((transposeMap.comp F).comp (ad (W0 d)ᴴ))) +
      (measureFlag d (defect F)).comp (ad (W0 d)ᴴ) +
      (measureFlag d (defect G)).comp (ad (W1 d)ᴴ) +
      measureFlag d (flagProjection d) := by
  apply LinearMap.ext
  intro X
  simp only [LinearMap.comp_apply, transposeMap_apply, theta,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.transpose_add, Matrix.transpose_smul,
    W0, W1, flag_transpose, LinearMap.add_apply, LinearMap.smul_apply,
    measureFlag, ad_apply, Matrix.conjTranspose_conjTranspose, add_smul]
  simp only [Matrix.transpose_mul, ← coord_transpose, Matrix.transpose_transpose,
    Matrix.mul_assoc]
  simp only [flagProjection, Matrix.trace_single_mul, one_smul]
  abel

lemma theta_ppt (d : ℕ) {F G : Map (Fin d) (Fin d)} (hF : PPT F) (hG : PPT G) :
    PPT (theta d F G) := by
  refine ⟨theta_cp d hF.1 hG.1, ?_⟩
  rw [theta_transpose_decomposition]
  apply cp_add
  · apply cp_add
    · apply cp_add
      · exact cp_add
          (cp_smul (cp_comp (cp_ad _) (cp_comp hG.2 (cp_ad _))) (coefficient_pos hG.1).le)
          (cp_smul (cp_comp (cp_ad _) (cp_comp hF.2 (cp_ad _))) (coefficient_pos hF.1).le)
      · exact cp_comp (cp_measureFlag _ (defect_psd hF.1)) (cp_ad _)
    · exact cp_comp (cp_measureFlag _ (defect_psd hG.1)) (cp_ad _)
  · exact cp_measureFlag _ (flag_psd d)

variable {n m : Type} [Fintype n] [Fintype m]

lemma defect_trace [DecidableEq n] (F : Map n m) (B : Mat n) :
    Matrix.trace (defect F * B) = Matrix.trace B - (coefficient F : ℂ) * Matrix.trace (F B) := by
  simp [defect, Matrix.sub_mul, effect_trace]

lemma trace_ad_isometry [DecidableEq n] (V : Matrix m n ℂ) (hV : Vᴴ * V = 1) (B : Mat n) :
    Matrix.trace (ad V B) = Matrix.trace B := by
  rw [ad_apply, Matrix.trace_mul_cycle, hV, Matrix.one_mul]

lemma trace_two_blocks (d : ℕ) (X : Mat (Space d)) :
    Matrix.trace X = Matrix.trace ((W0 d)ᴴ * X * W0 d) +
      Matrix.trace ((W1 d)ᴴ * X * W1 d) + X (flag d) (flag d) := by
  rw [W0, W1, coord_compress, coord_compress]
  simp [Matrix.trace, Matrix.diag, Space, first, second, flag, Fintype.sum_sum_type]

lemma theta_tracePreserving (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    TracePreserving (theta d F G) := by
  intro X
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Matrix.trace_add, Matrix.trace_smul]
  rw [trace_ad_isometry _ (W0_isometry d), trace_ad_isometry _ (W1_isometry d),
    defect_trace, defect_trace]
  have hflag : Matrix.trace (flagProjection d) = 1 := by
    simp [flagProjection, Matrix.trace, Matrix.diag, Matrix.single_apply, flag]
  rw [hflag]
  simp only [smul_eq_mul, mul_one]
  rw [trace_two_blocks d X]
  ring

end ChannelCompletion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_ChannelCompletion
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace ChannelCompletion
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

omit [Fintype n] in
lemma compress_ad (V : Matrix p n ℂ) (W : Matrix p m ℂ) (X : Mat m) :
    Vᴴ * ad W X * V = (Vᴴ * W) * X * (Wᴴ * V) := by
  simp only [ad_apply, Matrix.mul_assoc]

lemma theta_first (d : ℕ) (F G : Map (Fin d) (Fin d)) (X : Mat (Space d)) :
    (W0 d)ᴴ * theta d F G X * W0 d =
      (coefficient G : ℂ) • G ((W1 d)ᴴ * X * W1 d) := by
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, compress_ad,
    W0_isometry, W0_W1, W1_W0, W0_flag, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, add_zero]

lemma theta_second (d : ℕ) (F G : Map (Fin d) (Fin d)) (X : Mat (Space d)) :
    (W1 d)ᴴ * theta d F G X * W1 d =
      (coefficient F : ℂ) • F ((W0 d)ᴴ * X * W0 d) := by
  simp only [theta, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, compress_ad,
    W1_isometry, W0_W1, W1_W0, W1_flag, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, smul_zero, zero_add, add_zero]

lemma square_corner (d : ℕ) (F G : Map (Fin d) (Fin d)) (B : Mat (Fin d)) :
    (W0 d)ᴴ * theta d F G (theta d F G (ad (W0 d) B)) * W0 d =
      ((coefficient F * coefficient G : ℝ) : ℂ) • G (F B) := by
  rw [theta_first, theta_second, compress_ad, W0_isometry, Matrix.one_mul,
    Matrix.mul_one, map_smul, smul_smul]
  simp [mul_comm]

omit [Fintype p] in
lemma choi_coord_compress [DecidableEq n] [DecidableEq m] [DecidableEq p]
    {s : Type} [Fintype s] [DecidableEq s]
    (e : n → m) (f : p → s) (F : Map m s) :
    (coord e ⊗ₖ coord f)ᴴ * choi F * (coord e ⊗ₖ coord f) =
      choi ((ad (coord f)ᴴ).comp (F.comp (ad (coord e)))) := by
  rw [coord_kronecker, coord_compress]
  ext ⟨i,a⟩ ⟨j,b⟩
  simp only [choi, Matrix.submatrix_apply, LinearMap.comp_apply]
  rw [ad_apply, Matrix.conjTranspose_conjTranspose, coord_compress, coord_single]
  rfl

omit [Fintype n] [Fintype m] in
lemma choi_smul [DecidableEq n] (F : Map n m) (c : ℂ) : choi (c • F) = c • choi F := rfl

lemma choi_corner (d : ℕ) (F G : Map (Fin d) (Fin d)) :
    (W0 d ⊗ₖ W0 d)ᴴ * choi ((theta d F G).comp (theta d F G)) * (W0 d ⊗ₖ W0 d) =
      ((coefficient F * coefficient G : ℝ) : ℂ) • choi (G.comp F) := by
  rw [W0, choi_coord_compress]
  rw [← choi_smul]
  congr 1
  apply LinearMap.ext
  intro B
  simpa only [LinearMap.comp_apply, ad_apply, Matrix.conjTranspose_conjTranspose,
    LinearMap.smul_apply, W0] using square_corner d F G B

end ChannelCompletion

namespace ChannelCompletion
variable {n m p q : Type} [Fintype n] [Fintype m] [Fintype p] [Fintype q]

omit [Fintype n] [Fintype m] [Fintype p] [Fintype q] in
lemma separable_submatrix {Z : Mat (n × m)} (hZ : Separable Z) (e : p → n) (f : q → m) :
    Separable (Z.submatrix (Prod.map e f) (Prod.map e f)) := by
  obtain ⟨r, A, B, hA, hB, rfl⟩ := hZ
  refine ⟨r, (fun i => (A i).submatrix e e), (fun i => (B i).submatrix f f),
    (fun i => (hA i).submatrix e), (fun i => (hB i).submatrix f), ?_⟩
  ext ⟨a,b⟩ ⟨c,d⟩
  simp [Matrix.submatrix_apply, Matrix.sum_apply]

omit [Fintype p] [Fintype q] in
lemma separable_coord_compress [DecidableEq n] [DecidableEq m]
    {Z : Mat (n × m)} (hZ : Separable Z) (e : p → n) (f : q → m) :
    Separable ((coord e ⊗ₖ coord f)ᴴ * Z * (coord e ⊗ₖ coord f)) := by
  rw [coord_kronecker, coord_compress]
  exact separable_submatrix hZ e f

omit [Fintype n] [Fintype m] in
lemma separable_smul {Z : Mat (n × m)} (hZ : Separable Z) {c : ℝ} (hc : 0 ≤ c) :
    Separable ((c : ℂ) • Z) := by
  obtain ⟨r, A, B, hA, hB, rfl⟩ := hZ
  refine ⟨r, (fun i => (c : ℂ) • A i), B,
    (fun i => (hA i).smul (show (0 : ℂ) ≤ c by exact_mod_cast hc)), hB, ?_⟩
  simp [Finset.smul_sum, Matrix.smul_kronecker]

omit [Fintype n] [Fintype m] in
lemma separable_of_smul {Z : Mat (n × m)} {c : ℝ} (hc : 0 < c)
    (hZ : Separable ((c : ℂ) • Z)) : Separable Z := by
  have h := separable_smul hZ (inv_nonneg.mpr hc.le)
  rw [Complex.ofReal_inv, smul_smul, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'),
    one_smul] at h
  exact h

end ChannelCompletion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_TensorSymmetry
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma firstSix_real : firstSixᴴ = firstSixᵀ := by
  ext i j
  simp [firstSix, Matrix.conjTranspose_apply, apply_ite star]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_ExteriorMaps
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Kronecker ComplexOrder
open Matrix
namespace DimensionTen

lemma phiOne_kraus : phiOne = krausMap phiOneKraus := by
  funext A
  unfold phiOne
  rw [exteriorMap_input_transpose, exteriorMap_kraus, krausMap_postconjugate]
  rfl

lemma phiOne_output_transpose (A : Mat 10) : (phiOne A)ᵀ = phiOne A := by
  unfold phiOne
  rw [real_embedding_transpose _ firstSix_real, exteriorMap_output_transpose]

end DimensionTen

end
end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_PPTSquare_TensorPositivity
attribute [-instance] _root_.OAI.DimensionTen.Mod41.instFactPrimeOfNatNat_solutions _root_.OAI.ZeroKey.matrixMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
open Matrix
namespace TensorCriterion
open ChannelCompletion
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
open Matrix
variable {n m p : Type} [Fintype n] [Fintype m] [Fintype p]

omit [Fintype n] [Fintype m] in
lemma cp_sum {r : Type} [Fintype r] (F : r → Map n m) (hF : ∀ i, CP (F i)) :
    CP (∑ i, F i) := by
  classical
  induction (Finset.univ : Finset r) using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    intro k _ X _
    exact Matrix.PosSemidef.zero
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact cp_add (hF a) ih

end TensorCriterion

end

end OAI
end

section
-- module Solutions.OAIQ057_CH.Quantum_DimensionTen_Channel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A trace-preserving PPT channel with an entangled square, from the dimension-ten pair. -/

noncomputable section

open scoped BigOperators Matrix Kronecker ComplexOrder MatrixOrder
open Matrix

namespace DimensionTen

@[simp] lemma phiOneLinear_apply (A : Mat 10) : phiOneLinear A = phiOne A := by
  rw [phiOne_kraus]
  simp only [phiOneLinear, LinearMap.sum_apply, ChannelCompletion.ad_apply, krausMap]

lemma phiOneLinear_cp : ChannelCompletion.CP phiOneLinear := by
  exact TensorCriterion.cp_sum _ (fun _ => ChannelCompletion.cp_ad _)

lemma phiTwoLinear_cp : ChannelCompletion.CP phiTwoLinear := by
  have h : phiTwoLinear =
      ∑ p : Fin 6 × Fin 6, ChannelCompletion.ad (phiTwoKraus p) := by
    ext A i j
    simp only [phiTwoLinear_apply, LinearMap.sum_apply, ChannelCompletion.ad_apply]
    rw [phiTwo_kraus]
    rfl
  rw [h]
  exact TensorCriterion.cp_sum _ (fun _ => ChannelCompletion.cp_ad _)

lemma phiOneLinear_ppt : ChannelCompletion.PPT phiOneLinear := by
  refine ⟨phiOneLinear_cp, ?_⟩
  have h : ChannelCompletion.transposeMap.comp phiOneLinear = phiOneLinear := by
    ext A i j
    change (phiOneLinear A)ᵀ i j = phiOneLinear A i j
    simp only [phiOneLinear_apply, phiOne_output_transpose]
  rw [h]
  exact phiOneLinear_cp

lemma phiTwoLinear_ppt : ChannelCompletion.PPT phiTwoLinear := by
  refine ⟨phiTwoLinear_cp, ?_⟩
  have h : ChannelCompletion.transposeMap.comp phiTwoLinear = phiTwoLinear := by
    ext A i j
    change (phiTwoLinear A)ᵀ i j = phiTwoLinear A i j
    simp only [phiTwoLinear_apply, phiTwo_output_transpose]
  rw [h]
  exact phiTwoLinear_cp

lemma linear_composite_choi :
    ChannelCompletion.choi (phiTwoLinear.comp phiOneLinear) = compositeChoi := by
  ext i j
  simp only [ChannelCompletion.choi, LinearMap.comp_apply,
    phiOneLinear_apply, phiTwoLinear_apply, compositeChoi, choi, Function.comp_apply]

lemma channel_choi_corner :
    (ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10)ᴴ *
      ChannelCompletion.choi (channel.comp channel) *
        (ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10) =
    ((ChannelCompletion.coefficient phiOneLinear *
      ChannelCompletion.coefficient phiTwoLinear : ℝ) : ℂ) • compositeChoi := by
  rw [channel, ChannelCompletion.choi_corner, linear_composite_choi]

theorem main_channel_conditional_s2_oai (hsr : PublishedChoi21) :
    ChannelCompletion.PPT channel ∧ ChannelCompletion.TracePreserving channel ∧
      ¬ ChannelCompletion.EntanglementBreaking (channel.comp channel) := by
  refine ⟨ChannelCompletion.theta_ppt 10 phiOneLinear_ppt phiTwoLinear_ppt,
    ChannelCompletion.theta_tracePreserving 10 phiOneLinear phiTwoLinear, ?_⟩
  intro hEB
  have hsep := ChannelCompletion.separable_coord_compress (hsr hEB)
    (ChannelCompletion.first 10) (ChannelCompletion.first 10)
  change ChannelCompletion.Separable
    ((ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10)ᴴ *
      ChannelCompletion.choi (channel.comp channel) *
        (ChannelCompletion.W0 10 ⊗ₖ ChannelCompletion.W0 10)) at hsep
  rw [channel_choi_corner] at hsep
  have hpos : 0 < ChannelCompletion.coefficient phiOneLinear *
      ChannelCompletion.coefficient phiTwoLinear :=
    mul_pos (ChannelCompletion.coefficient_pos phiOneLinear_cp)
      (ChannelCompletion.coefficient_pos phiTwoLinear_cp)
  apply linear_composite_not_separable_s2
  rw [linear_composite_choi]
  exact ChannelCompletion.separable_of_smul hpos hsep

end DimensionTen

end

end OAI
end

theorem solution : type_of% @OAI.DimensionTen.main_channel_conditional_s2_oai := @OAI.DimensionTen.main_channel_conditional_s2_oai
