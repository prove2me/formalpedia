-- Prove2me | solution 1 for OAI.CurrentKS.RationalFace.faceCandidates_progress
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:56:34.136962+00:00
-- url     : https://prove2.me/submissions/65d68d17-1726-49bd-bdcf-0b53e7abff07

import Mathlib
import Definitions.Def_OAIQ241TT006
import Theorems.Thm_OAI_CurrentKS_RationalFace_activePotential_regular
import Theorems.Thm_OAI_CurrentKS_RationalSDP_valueQueryPoint_correct
import Theorems.Thm_OAI_CurrentKS_State_LightPoint_computed_candidates_progress
import Theorems.Thm_OAI_CurrentKS_State_etaTheta_minimizer
import Theorems.Thm_OAI_CurrentKS_Variational_kkt

section
-- module Solutions.OAIQ241_TT.Compat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `CStarAlgebra.norm_le_norm_of_le_of_nonneg hab ha`; ours is `norm_le_norm_of_nonneg_of_le ha hab`. -/
theorem _root_.CStarAlgebra.norm_le_norm_of_le_of_nonneg {A : Type*} [NonUnitalCStarAlgebra A]
    [PartialOrder A] [StarOrderedRing A] {a b : A} (hab : a ≤ b) (ha : 0 ≤ a) : ‖a‖ ≤ ‖b‖ :=
  CStarAlgebra.norm_le_norm_of_nonneg_of_le ha hab
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_ScalarPsi
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section
open scoped ContDiff

lemma base_pos {x : ℝ} (hx : |x| < 1) : 0 < 1-x^2 := by
  have h := (abs_lt.mp hx)
  nlinarith [sq_nonneg x]

lemma psi_pos {x : ℝ} (hx : |x| < 1) : 0 < psi x :=
  Real.rpow_pos_of_pos (base_pos hx) _

lemma psi_cube {x : ℝ} (hx : |x| < 1) : psi x ^ 3 = 1-x^2 := by
  rw [psi, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt (base_pos hx))]
  norm_num

lemma psi_le_one {x : ℝ} (hx : |x| < 1) : psi x ≤ 1 := by
  have hp := psi_pos hx
  have hc := psi_cube hx
  nlinarith [sq_nonneg x, sq_nonneg (psi x - 1)]

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_Alpha
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar
noncomputable section

lemma psi_ge_base {x : ℝ} (hx : |x| < 1) : 1-x^2 ≤ psi x := by
  have hp := psi_pos hx
  have hle := psi_le_one hx
  have hc := psi_cube hx
  have hs : psi x ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hs)]

end
end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Arithmetic_CubeInterval
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Scalar

lemma cubeInterval_spec (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) :
    0 ≤ (cubeInterval q k).1 ∧ (cubeInterval q k).2 ≤ 1 ∧
    ((cubeInterval q k).1:ℝ) ≤ r ∧ r ≤ ((cubeInterval q k).2:ℝ) ∧
    (cubeInterval q k).2-(cubeInterval q k).1=(1/2:ℚ)^k := by
  induction k with
  | zero => simpa [cubeInterval] using And.intro hr hr1
  | succ k ih =>
    have horder : (cubeInterval q k).1 ≤ (cubeInterval q k).2 := by
      exact_mod_cast ih.2.2.1.trans ih.2.2.2.1
    let m : ℚ := ((cubeInterval q k).1+(cubeInterval q k).2)/2
    have hml : (cubeInterval q k).1 ≤ m := by dsimp [m] <;> linarith
    have hmu : m ≤ (cubeInterval q k).2 := by dsimp [m] <;> linarith
    have hm : 0 ≤ m := ih.1.trans hml
    have hmr : (0:ℝ) ≤ m := by exact_mod_cast hm
    have he : cubeInterval q (k+1) = if m^3 ≤ q then (m,(cubeInterval q k).2) else ((cubeInterval q k).1,m) := rfl
    rw [he]
    split
    · rename_i h
      have hc : (m:ℝ)^3 ≤ r^3 := by rw [← hq]; exact_mod_cast h
      have hle := (pow_le_pow_iff_left₀ hmr hr (by decide : 3≠0)).mp hc
      refine ⟨hm,ih.2.1,hle,ih.2.2.2.1,?_⟩
      change (cubeInterval q k).2-m=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring
    · rename_i h
      have hc : r^3 ≤ (m:ℝ)^3 := by rw [← hq]; exact_mod_cast (le_of_lt (lt_of_not_ge h))
      have hle := (pow_le_pow_iff_left₀ hr hmr (by decide : 3≠0)).mp hc
      refine ⟨ih.1,hmu.trans ih.2.1,ih.2.2.1,hle,?_⟩
      change m-(cubeInterval q k).1=(1/2:ℚ)^(k+1)
      rw [pow_succ,← ih.2.2.2.2]
      dsimp [m]
      ring

lemma cubeInterval_error (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) :
    |((cubeInterval q k).1:ℝ)-r| ≤ (1/2:ℝ)^k := by
  obtain ⟨_,_,hl,hu,hw⟩ := cubeInterval_spec q r hr hr1 hq k
  have hwr : ((cubeInterval q k).2:ℝ)-(cubeInterval q k).1=(1/2:ℝ)^k := by
    have hc := congrArg (fun z : ℚ => (z : ℝ)) hw
    norm_num only [Rat.cast_sub,Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at hc
    exact hc
  rw [abs_of_nonpos (sub_nonpos.mpr hl)]
  linarith

lemma cubeInterval_lower_mem (q : ℚ) (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hq : (q:ℝ)=r^3) (k : ℕ) : (cubeInterval q k).1 ∈ Set.Icc (0:ℚ) 1 := by
  have h := cubeInterval_spec q r hr hr1 hq k
  exact ⟨h.1,by exact_mod_cast h.2.2.1.trans hr1⟩

lemma psi_closed_cube {x : ℝ} (hx : |x| ≤ 1) : psi x^3=1-x^2 := by
  have hb : 0 ≤ 1-x^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hx
    nlinarith
  rw [psi,← Real.rpow_natCast,← Real.rpow_mul hb]
  norm_num
lemma psi_closed_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hc := psi_closed_cube hx
  have hb : 0 ≤ 1-x^2 := by
    obtain ⟨hl,hu⟩ := abs_le.mp hx
    nlinarith
  have hp : 0 ≤ psi x := Real.rpow_nonneg hb _
  refine ⟨hp,(pow_le_pow_iff_left₀ hp (by norm_num : (0:ℝ) ≤ 1) (by decide : 3≠0)).mp ?_⟩
  rw [hc]
  nlinarith [sq_nonneg x]

lemma inverse_pow_size_le {δ : ℚ} (hδ : 0 < δ) : (1/2:ℚ)^δ.den.size ≤ δ := by
  have hd : (0:ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hp : (0:ℚ) < 2^δ.den.size := by positivity
  have hnum : (1:ℚ) ≤ δ.num := by exact_mod_cast (Int.add_one_le_iff.mpr (Rat.num_pos.mpr hδ))
  have hden : (δ.den:ℚ) ≤ 2^δ.den.size := by exact_mod_cast (Nat.lt_size_self δ.den).le
  rw [_root_.one_div_pow,one_div]
  calc
    (2^δ.den.size:ℚ)⁻¹ ≤ (δ.den:ℚ)⁻¹ := inv_anti₀ hd hden
    _ ≤ (δ.num:ℚ)/(δ.den:ℚ) := by rw [inv_eq_one_div]; exact div_le_div_of_nonneg_right hnum hd.le
    _ = δ := Rat.num_div_den δ

lemma approxPsi_spec (x δ : ℚ) (hx : |(x:ℝ)| ≤ 1) (hδ : 0 < δ) :
    approxPsi x δ ∈ Set.Icc (0:ℚ) 1 ∧ |(approxPsi x δ:ℝ)-psi (x:ℝ)| ≤ (δ:ℝ) := by
  obtain ⟨hp,hp1⟩ := psi_closed_bounds hx
  have hc : ((1-x^2:ℚ):ℝ)=psi (x:ℝ)^3 := by rw [psi_closed_cube hx]; push_cast; rfl
  refine ⟨cubeInterval_lower_mem _ _ hp hp1 hc _,?_⟩
  have he : (((1/2:ℚ)^δ.den.size : ℚ):ℝ) ≤ (δ:ℝ) := Rat.cast_le.mpr (inverse_pow_size_le hδ)
  norm_num only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] at he
  exact (cubeInterval_error _ _ hp hp1 hc _).trans he

end CurrentKS.Scalar

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

variable {d : ℕ}

section OperatorNorm
open scoped Matrix.Norms.L2Operator MatrixOrder

theorem trace_mul_nonneg {A B : Mat d} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (A * B).trace.re := by
  let : CStarAlgebra (Mat d) := {}
  have hs : (CFC.sqrt A).PosSemidef := (CFC.sqrt_nonneg _).posSemidef
  have ht := (hB.mul_mul_conjTranspose_same (CFC.sqrt A)).trace_nonneg
  rw [hs.isHermitian.eq, Matrix.trace_mul_cycle,
    CFC.sqrt_mul_sqrt_self A hA.nonneg] at ht
  exact (Complex.nonneg_iff.mp ht).1

end OperatorNorm

open scoped Matrix.Norms.Frobenius

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

theorem inner_nonneg_of_psd (A B : H d) (hA : A ∈ psdCone d) (hB : B ∈ psdCone d) :
    0 ≤ inner ℝ A B := by
  rw [inner_eq_trace]
  exact trace_mul_nonneg hA hB

theorem rankOne_mem_psdCone (v : Fin d → ℂ) : rankOne v ∈ psdCone d :=
  Matrix.posSemidef_vecMulVec_self_star v

theorem inner_rankOne (A : H d) (v : Fin d → ℂ) :
    inner ℝ A (rankOne v) = (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re := by
  rw [inner_eq_trace]
  change ((A : Mat d) * Matrix.vecMulVec v (star v)).trace.re = _
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

theorem psd_of_inner_nonneg (A : H d)
    (h : ∀ B ∈ psdCone d, 0 ≤ inner ℝ A B) : A ∈ psdCone d := by
  apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
  refine ⟨A.property, fun v => ?_⟩
  apply Complex.nonneg_iff.mpr
  refine ⟨?_, ?_⟩
  · simpa only [inner_rankOne] using h (rankOne v) (rankOne_mem_psdCone v)
  · exact (A.property.im_star_dotProduct_mulVec_self v).symm

theorem isClosed_psdCone : IsClosed (psdCone d : Set (H d)) := by
  have he : (psdCone d : Set (H d)) =
      {A : H d | ∀ v : Fin d → ℂ, 0 ≤ (star v ⬝ᵥ ((A : Mat d) *ᵥ v)).re} := by
    ext A
    constructor
    · intro hA v
      exact hA.re_dotProduct_nonneg v
    · intro hA
      apply psd_of_inner_nonneg A

      have hp : (A : Mat d).PosSemidef :=
        Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨A.property, fun v =>
          Complex.nonneg_iff.mpr ⟨hA v, (A.property.im_star_dotProduct_mulVec_self v).symm⟩⟩
      exact fun B hB => inner_nonneg_of_psd A B hp hB
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro v
  apply isClosed_le continuous_const
  exact Complex.continuous_re.comp (continuous_const.dotProduct
    (continuous_subtype_val.matrix_mulVec continuous_const))

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_InvH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder

variable {d : ℕ}

lemma pd_smul {A : H d} (hA : A ∈ pd d) {a : ℝ} (ha : 0 < a) :
    a • A ∈ pd d := by
  change ((a : ℂ) • (A : Mat d)).PosDef
  exact hA.smul (by exact_mod_cast ha)

lemma isClosed_lowerBound (a : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A} := by
  change IsClosed ((fun A : H d => A - a • one) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_id.sub continuous_const)

lemma isClosed_upperBound (b : ℝ) :
    IsClosed {A : H d | A ≤ (b • one : H d)} := by
  change IsClosed ((fun A : H d => b • one - A) ⁻¹' (psdCone d : Set (H d)))
  exact (isClosed_psdCone (d := d)).preimage (continuous_const.sub continuous_id)

lemma isClosed_orderBox (a b : ℝ) :
    IsClosed {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} :=
  (isClosed_lowerBound a).inter (isClosed_upperBound b)

open scoped Matrix.Norms.L2Operator

theorem inverse_antitone {A B : Mat d} (hA : A.PosDef) (hB : B.PosDef) (hab : A ≤ B) :
    B⁻¹ ≤ A⁻¹ := by
  let : CStarAlgebra (Mat d) := {}
  obtain ⟨u, rfl⟩ := hA.isUnit
  obtain ⟨v, rfl⟩ := hB.isUnit
  simpa only [Matrix.coe_units_inv] using CStarAlgebra.inv_le_inv hA.posSemidef.nonneg hab

lemma scalar_posDef {a : ℝ} (ha : 0 < a) : ((a : ℂ) • (1 : Mat d)).PosDef :=
  Matrix.PosDef.one.smul (by exact_mod_cast ha)

lemma scalar_inv (a : ℝ) : (((a : ℂ) • (1 : Mat d))⁻¹) = (a⁻¹ : ℂ) • (1 : Mat d) := by
  by_cases ha : a = 0
  · simp [ha]
  · let : Invertible (a : ℂ) := invertibleOfNonzero (by exact_mod_cast ha)
    rw [Matrix.inv_smul _ _ (by simp), invOf_eq_inv]
    simp

theorem le_trace_smul_one {A : Mat d} (hA : A.PosSemidef) :
    A ≤ (A.trace.re : ℂ) • (1 : Mat d) := by
  let : CStarAlgebra (Mat d) := {}
  have heig (i : Fin d) : hA.isHermitian.eigenvalues i ≤ A.trace.re := by
    rw [hA.isHermitian.trace_eq_sum_eigenvalues, Complex.re_sum]
    exact Finset.single_le_sum (fun j _ => hA.eigenvalues_nonneg j) (Finset.mem_univ i)
  have hc : 0 ≤ cfc (fun x : ℝ => A.trace.re - x) A := by
    apply (cfc_nonneg_iff _ A).mpr
    intro x hx
    obtain ⟨i, rfl⟩ := hA.isHermitian.spectrum_real_eq_range_eigenvalues ▸ hx
    exact sub_nonneg.mpr (heig i)
  rw [cfc_sub (fun _ : ℝ => A.trace.re) (fun x : ℝ => x),
    cfc_const _ A hA.isHermitian.isSelfAdjoint] at hc
  change 0 ≤ (algebraMap ℝ (Mat d)) A.trace.re - cfc (id : ℝ → ℝ) A at hc
  rw [cfc_id ℝ A hA.isHermitian.isSelfAdjoint] at hc
  have hmap : (algebraMap ℝ (Mat d)) A.trace.re = (A.trace.re : ℂ) • (1 : Mat d) := by
    ext i j
    simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply, Matrix.smul_apply,
      Matrix.one_apply]
  rw [hmap] at hc
  exact sub_nonneg.mp hc

theorem isCompact_orderBox (a b : ℝ) :
    IsCompact {A : H d | (a • one : H d) ≤ A ∧ A ≤ b • one} := by
  let : CStarAlgebra (Mat d) := {}
  let : ProperSpace (H d) := FiniteDimensional.proper ℝ (H d)
  apply (isCompact_closedBall (a • one : H d) ‖(b-a) • (one : H d)‖).of_isClosed_subset
    (isClosed_orderBox a b)
  intro A hA
  rw [Metric.mem_closedBall]
  change dist (A : Mat d) (a • (1 : Mat d)) ≤ ‖(b-a) • (1 : Mat d)‖
  rw [dist_eq_norm]
  have h₁ : a • (1 : Mat d) ≤ (A : Mat d) := hA.1
  have h₂ : (A : Mat d) ≤ b • (1 : Mat d) := hA.2
  apply CStarAlgebra.norm_le_norm_of_le_of_nonneg _ (sub_nonneg.mpr h₁)
  have hh := sub_le_sub_right h₂ (a • (1 : Mat d))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Complex.real_smul,
    Complex.ofReal_sub]
  ring

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTrace
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open scoped BigOperators ComplexOrder

variable {d : ℕ}

theorem nonzero_eigenvalues_card_le (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) :
    Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ A.rank := by
  classical
  have h := hA.conjStarAlgAut_star_eigenvectorUnitary
  have hr : (Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).rank
      ≤ A.rank := by
    rw [← h]
    simp only [Unitary.conjStarAlgAut_apply]
    exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)
  rw [Matrix.rank_diagonal] at hr
  simpa only [Function.comp_apply, ne_eq, RCLike.ofReal_eq_zero] using hr

theorem nonzero_eigenvalue_unique (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i j : Fin d) (hi : hA.eigenvalues i ≠ 0) (hj : hA.eigenvalues j ≠ 0) :
    i = j := by
  have hcard : Fintype.card {i // hA.eigenvalues i ≠ 0} ≤ 1 :=
    (nonzero_eigenvalues_card_le A hA).trans hrank
  have hs := Fintype.card_le_one_iff_subsingleton.mp hcard
  exact congrArg Subtype.val (hs.elim (⟨i, hi⟩ : {i // hA.eigenvalues i ≠ 0}) ⟨j, hj⟩)

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RankFactor
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder

variable {d : ℕ}

lemma rank_one_factor (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef)
    (hrank : A.rank ≤ 1) : ∃ u : Fin d → ℂ, A = vecMulVec u (star u) := by
  classical
  by_cases hzero : A = 0
  · refine ⟨0, ?_⟩
    rw [hzero]
    ext j k
    simp [vecMulVec]
  have he : ∃ i, hA.isHermitian.eigenvalues i ≠ 0 := by
    by_contra! hh
    apply hzero
    exact hA.isHermitian.eigenvalues_eq_zero_iff.mp (funext hh)
  obtain ⟨i,hi⟩ := he
  let U : Matrix (Fin d) (Fin d) ℂ := hA.isHermitian.eigenvectorUnitary
  let e : ℝ := hA.isHermitian.eigenvalues i
  have he0 : 0 ≤ e := hA.eigenvalues_nonneg i
  have hsqrt : (Real.sqrt e : ℂ) * (Real.sqrt e : ℂ) = (e : ℂ) := by
    exact_mod_cast Real.mul_self_sqrt he0
  refine ⟨fun j => (Real.sqrt e : ℂ) * U j i, ?_⟩
  have hspec := hA.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose] at hspec
  rw [hspec]
  ext j k
  change ∑ l, ((U * diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ hA.isHermitian.eigenvalues)) j l) *
      U.conjTranspose l k = ((Real.sqrt e : ℂ)*U j i) * star ((Real.sqrt e : ℂ)*U k i)
  rw [Finset.sum_eq_single i]
  · simp only [Matrix.mul_diagonal,Function.comp_apply,Matrix.conjTranspose_apply,
      StarMul.star_mul,Complex.star_def,Complex.conj_ofReal]
    change U j i * (e : ℂ) * star (U k i) =
      ((Real.sqrt e : ℂ) * U j i) * (star (U k i) * (Real.sqrt e : ℂ))
    rw [← hsqrt]
    ring
  · intro l _ hli
    have hl : hA.isHermitian.eigenvalues l = 0 := by
      by_contra hl
      exact hli (nonzero_eigenvalue_unique A hA.isHermitian hrank l i hl hi)
    simp only [Matrix.mul_diagonal,Function.comp_apply,hl,RCLike.ofReal_zero,mul_zero,zero_mul]
  · simp

lemma outer_sandwich (u : Fin d → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    vecMulVec u (star u) * B * vecMulVec u (star u) =
      (star u ⬝ᵥ (B *ᵥ u)) • vecMulVec u (star u) := by
  ext i j
  simp only [Matrix.mul_apply,vecMulVec_apply,Matrix.smul_apply,smul_eq_mul,
    Matrix.mulVec,dotProduct]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

lemma trace_outer_mul (u : Fin d → ℂ) (B : Matrix (Fin d) (Fin d) ℂ) :
    (vecMulVec u (star u) * B).trace = star u ⬝ᵥ (B *ᵥ u) := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,vecMulVec_apply,Matrix.mulVec,dotProduct,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma rank_one_sandwich (A : Matrix (Fin d) (Fin d) ℂ) (hA : A.PosSemidef)
    (hrank : A.rank ≤ 1) (B : Matrix (Fin d) (Fin d) ℂ) :
    A*B*A = (A*B).trace • A := by
  obtain ⟨u,rfl⟩ := rank_one_factor A hA hrank
  rw [outer_sandwich,trace_outer_mul]

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ realTrace A :=
  (Complex.nonneg_iff.mp hA.trace_nonneg).1

lemma realTrace_mono {A B : H d} (hab : A ≤ B) : realTrace A ≤ realTrace B := by
  have hh := realTrace_nonneg (show B-A ∈ psdCone d from hab)
  simpa using hh

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

lemma continuous_realTrace : Continuous (realTrace : H d → ℝ) := by
  have he : (fun A : H d => traceCLM A) = realTrace := funext traceCLM_apply
  rw [← he]
  exact (traceCLM (d := d)).continuous

lemma continuousAt_invH {A : H d} (hA : A ∈ pd d) : ContinuousAt invH A := by
  have hm : ContinuousAt (Inv.inv : Mat d → Mat d) (A : Mat d) := by
    apply continuousAt_matrix_inv
    have he : (Ring.inverse : ℂ → ℂ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [he]
    exact continuousAt_inv₀ hA.det_pos.ne'
  apply tendsto_subtype_rng.mpr
  exact hm.comp continuousAt_subtype_val

lemma pd_of_lower {a : ℝ} (ha : 0 < a) {A : H d} (hA : a • one ≤ A) : A ∈ pd d := by
  have hp : ((A : Mat d) - (a : ℂ) • 1).PosSemidef := hA
  have hs := (scalar_posDef ha).add_posSemidef hp
  simp only [add_sub_cancel] at hs
  exact hs

lemma inverse_bound_below {a : ℝ} (ha : 0 < a) {A : H d}
    (hA : A ∈ pd d) (he : invH A ≤ a • one) : a⁻¹ • one ≤ A := by
  let : Invertible (A : Mat d) := hA.isUnit.invertible
  have hi := inverse_antitone hA.inv (scalar_posDef ha) he
  rw [scalar_inv, Matrix.inv_inv_of_invertible] at hi
  change ((a⁻¹ : ℝ) : ℂ) • (1 : Mat d) ≤ (A : Mat d)
  simpa only [Complex.ofReal_inv] using hi

lemma psd_nonneg {A : H d} (hA : A ∈ psdCone d) : 0 ≤ A := hA.nonneg

lemma mem_psd_iff_nonneg (A : H d) : A ∈ psdCone d ↔ 0 ≤ A := by
  constructor
  · exact psd_nonneg
  · intro hA
    have hh : (0 : Mat d) ≤ (A : Mat d) := hA
    exact hh.posSemidef

lemma scalar_one_mono {r s : ℝ} (hrs : r ≤ s) :
    r • (one : H d) ≤ s • one := by
  apply sub_nonneg.mp
  erw [← sub_smul]
  exact psd_nonneg (psd_smul one_mem_psdCone (sub_nonneg.mpr hrs))

lemma trace_bound_above {A : H d} (hA : A ∈ psdCone d) : A ≤ realTrace A • one :=
  le_trace_smul_one hA

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RealTraceSum
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma realTrace_sum {ι : Type*} (s : Finset ι) (A : ι → H d) :
    realTrace (∑ i ∈ s, A i) = ∑ i ∈ s, realTrace (A i) := by
  simp only [← inner_one, inner_sum]

lemma psd_sum {ι : Type*} (s : Finset ι) (A : ι → H d) (hA : ∀ i ∈ s, A i ∈ psdCone d) :
    (∑ i ∈ s, A i) ∈ psdCone d := by
  exact (mem_psd_iff_nonneg _).mpr (Finset.sum_nonneg fun i hi => (mem_psd_iff_nonneg _).mp (hA i hi))

lemma smul_order {A B : H d} (h : A ≤ B) {r : ℝ} (hr : 0 ≤ r) : r • A ≤ r • B := by
  apply sub_nonneg.mp
  rw [← smul_sub r B A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)) hr)

lemma scalar_mono_psd {A : H d} (hA : A ∈ psdCone d) {r s : ℝ} (hrs : r ≤ s) : r • A ≤ s • A := by
  apply sub_nonneg.mp
  rw [← sub_smul s r A]
  exact (mem_psd_iff_nonneg _).mp (psd_smul hA (sub_nonneg.mpr hrs))

lemma invH_scalar (a : ℝ) : invH (a • (Hermitian.one : H d)) = a⁻¹ • (Hermitian.one : H d) := by
  apply Subtype.ext
  change (a • (1 : Mat d))⁻¹ = a⁻¹ • (1 : Mat d)
  have h (r : ℝ) : r • (1 : Mat d) = (r : ℂ) • (1 : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [h a, h a⁻¹, Complex.ofReal_inv]
  exact scalar_inv a

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Sandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian

section L2Operator

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {d : ℕ}

lemma sandwich_psd (A U : H d) (hU : U ∈ psdCone d) : sandwich A U ∈ psdCone d := by
  have hh := hU.mul_mul_conjTranspose_same (A : Mat d)
  rw [A.property.eq] at hh
  exact hh

end L2Operator

section Frobenius

open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma inner_sandwich (A U P : H d) :
    inner ℝ P (sandwich A U) = inner ℝ (sandwich A P) U := by
  rw [inner_eq_trace, inner_eq_trace]
  change ((P : Mat d) * ((A : Mat d) * (U : Mat d) * (A : Mat d))).trace.re =
    ((A : Mat d) * (P : Mat d) * (A : Mat d) * (U : Mat d)).trace.re
  rw [← mul_assoc, ← mul_assoc, Matrix.trace_mul_comm ((P : Mat d) * (A : Mat d) * (U : Mat d))]
  simp only [mul_assoc]

end Frobenius

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p7
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_re0a799_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p7
lemma sandwich_sub (A U V : H d) : sandwich A (U-V) = sandwich A U - sandwich A V := by
  apply Subtype.ext
  change (A : Mat d) * ((U : Mat d)-(V : Mat d)) * (A : Mat d) = _
  simp only [mul_sub, sub_mul]
  rfl

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_SandwichShiftInverse
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma trace_mul_real (A B : H d) : (((A : Mat d)*(B : Mat d)).trace.re : ℂ) = ((A : Mat d)*(B : Mat d)).trace := by
  have hs : star (((A : Mat d)*(B : Mat d)).trace) = ((A : Mat d)*(B : Mat d)).trace := by
    rw [← Matrix.trace_conjTranspose,Matrix.conjTranspose_mul,A.property.eq,B.property.eq,Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_re.mp hs

lemma sandwich_rank_one (A B : H d) (hA : A ∈ psdCone d) (hrank : (A : Mat d).rank ≤ 1) :
    sandwich A B = (inner ℝ A B) • A := by
  apply Subtype.ext
  change (A : Mat d)*(B : Mat d)*(A : Mat d) = (inner ℝ A B) • (A : Mat d)
  rw [CurrentKS.rank_one_sandwich _ hA hrank,inner_eq_trace]
  have hs (r : ℝ) : r • (A : Mat d) = (r : ℂ) • (A : Mat d) := by
    ext i j
    exact Complex.real_smul
  rw [hs,trace_mul_real]

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Point
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma feasible_iff (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z.2.1 ∈ pd d ∧ z.2.2 ∈ pd d ∧
      invH z.2.1 + S + η z.2.2 ≤ z.1 • (Hermitian.one : H d) ∧
      invH z.2.2 - S + η z.2.1 ≤ z.1 • (Hermitian.one : H d) := by
  simp only [feasible, domain, residual, mem_ofPred_eq, sub_nonpos]
  tauto

lemma continuous_objective (ε : ℝ) : Continuous (objective (d := d) ε) := by
  exact continuous_fst.add (continuous_const.mul
    (continuous_realTrace.comp ((continuous_fst.comp continuous_snd).add
      (continuous_snd.comp continuous_snd))))

lemma trace_bounds_of_feasible [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {z : Point d} (hz : z ∈ feasible S η) :
    0 ≤ z.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ∧ 0 ≤ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have htr₁ := realTrace_mono h₁
  have htr₂ := realTrace_mono h₂
  have hiX := realTrace_nonneg (A := invH z.2.1) hX.inv.posSemidef
  have hiY := realTrace_nonneg (A := invH z.2.2) hY.inv.posSemidef
  have heX := realTrace_nonneg (hη _ hX.posSemidef)
  have heY := realTrace_nonneg (hη _ hY.posSemidef)
  simp only [realTrace_add, realTrace_sub, realTrace_smul, realTrace_one] at htr₁ htr₂
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  refine ⟨?_, realTrace_nonneg hX.posSemidef, realTrace_nonneg hY.posSemidef⟩
  nlinarith

lemma objective_bounds [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) {z : Point d} (hz : z ∈ feasible S η)
    (hf : objective ε z ≤ K) :
    0 ≤ z.1 ∧ z.1 ≤ K ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.1 ≤ K / ε ∧ _root_.OAI.CurrentKS.Hermitian.realTrace z.2.2 ≤ K / ε := by
  obtain ⟨ht, hX, hY⟩ := trace_bounds_of_feasible S η hη hz
  simp only [objective, realTrace_add] at hf
  refine ⟨ht, ?_, (le_div_iff₀ hε).mpr ?_, (le_div_iff₀ hε).mpr ?_⟩ <;>
    nlinarith [mul_nonneg hε.le hX, mul_nonneg hε.le hY]

lemma inverse_bounds (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {K : ℝ} (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (ht : z.1 ≤ K) :
    invH z.2.1 ≤ (2*K) • (Hermitian.one : H d) ∧ invH z.2.2 ≤ (2*K) • (Hermitian.one : H d) := by
  obtain ⟨hX, hY, h₁, h₂⟩ := (feasible_iff S η z).mp hz
  have heX : 0 ≤ η z.2.1 := psd_nonneg (hη _ hX.posSemidef)
  have heY : 0 ≤ η z.2.2 := psd_nonneg (hη _ hY.posSemidef)
  have htk : z.1 • (Hermitian.one : H d) ≤ K • (Hermitian.one : H d) := scalar_one_mono ht
  constructor
  · have hh : invH z.2.1 + S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heY).trans (h₁.trans htk)
    have hx := add_le_add hh (neg_le_neg hS₁)
    convert hx using 1 <;> first | rfl | module
  · have hh : invH z.2.2 - S ≤ K • (Hermitian.one : H d) :=
      (le_add_of_nonneg_right heX).trans (h₂.trans htk)
    have hx := add_le_add hh hS₂
    convert hx using 1 <;> first | rfl | module

lemma sublevel_box [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    {z : Point d} (hz : z ∈ feasible S η) (hf : objective ε z ≤ K) :
    z.1 ∈ Icc 0 K ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.1 ∧ z.2.1 ≤ (K/ε) • (Hermitian.one : H d)) ∧
    ((2*K)⁻¹ • (Hermitian.one : H d) ≤ z.2.2 ∧ z.2.2 ≤ (K/ε) • (Hermitian.one : H d)) := by
  obtain ⟨ht, htK, htrX, htrY⟩ := objective_bounds S η hη hε hz hf
  obtain ⟨hXi, hYi⟩ := inverse_bounds S η hη hS₁ hS₂ hz htK
  obtain ⟨hX,hY,-,-⟩ := (feasible_iff S η z).mp hz
  have hmul : ∀ r s : ℝ, r ≤ s → r • (Hermitian.one : H d) ≤ s • (Hermitian.one : H d) :=
    fun _ _ h => scalar_one_mono h
  exact ⟨⟨ht,htK⟩,
    ⟨inverse_bound_below (by positivity) hX hXi,
      (trace_bound_above hX.posSemidef).trans (hmul _ _ htrX)⟩,
    ⟨inverse_bound_below (by positivity) hY hYi,
      (trace_bound_above hY.posSemidef).trans (hmul _ _ htrY)⟩⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_PairCone
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma isClosed_pairCone : IsClosed (pairCone d : Set (H d × H d)) :=
  (isClosed_psdCone (d := d)).prod (isClosed_psdCone (d := d))

lemma feasible_iff_cone (S : H d) (η : H d →L[ℝ] H d) (z : Point d) :
    z ∈ feasible S η ↔ z ∈ domain d ∧ -residual S η z ∈ pairCone d := by
  simp only [feasible, mem_ofPred_eq, mem_pairCone, Prod.fst_neg, Prod.snd_neg]
  simp only [mem_psd_iff_nonneg, neg_nonneg]

lemma continuousOn_residual (S : H d) (η : H d →L[ℝ] H d) :
    ContinuousOn (residual S η) (domain d) := by
  intro z hz
  have hiX : ContinuousAt (fun z : Point d => invH z.2.1) z :=
    (continuousAt_invH hz.1).comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have hiY : ContinuousAt (fun z : Point d => invH z.2.2) z :=
    (continuousAt_invH hz.2).comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  have heX : ContinuousAt (fun z : Point d => η z.2.1) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.1) (x := z) (by fun_prop)
  have heY : ContinuousAt (fun z : Point d => η z.2.2) z :=
    η.continuous.continuousAt.comp (f := fun w : Point d => w.2.2) (x := z) (by fun_prop)
  exact (((hiX.add continuousAt_const).add heY).sub
    (continuousAt_fst.smul continuousAt_const)).prodMk
      (((hiY.sub continuousAt_const).add heX).sub
        (continuousAt_fst.smul continuousAt_const)) |>.continuousWithinAt

theorem exists_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d)
    {ε K : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hS₁ : -K • (Hermitian.one : H d) ≤ S) (hS₂ : S ≤ K • (Hermitian.one : H d))
    (z₀ : Point d) (hz₀ : z₀ ∈ feasible S η) (hf₀ : objective ε z₀ ≤ K) :
    ∃ z ∈ feasible S η, objective ε z ≤ K ∧
      ∀ w ∈ feasible S η, objective ε z ≤ objective ε w := by
  let B : Set (Point d) := Icc 0 K ×ˢ
    ({A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)} ×ˢ
      {A : H d | (2*K)⁻¹ • (Hermitian.one : H d) ≤ A ∧ A ≤ (K/ε) • (Hermitian.one : H d)})
  have hBc : IsCompact B := isCompact_Icc.prod
    ((isCompact_orderBox _ _).prod (isCompact_orderBox _ _))
  have hBD : B ⊆ domain d := by
    intro z hz
    exact ⟨pd_of_lower (by positivity) hz.2.1.1, pd_of_lower (by positivity) hz.2.2.1⟩
  let F : Point d → (H d × H d) × ℝ := fun z => (-residual S η z, objective ε z)
  have hFc : ContinuousOn F B := ((continuousOn_residual S η).mono hBD).neg.prodMk
    (continuous_objective ε).continuousOn
  let C : Set (Point d) := B ∩ F ⁻¹' ((pairCone d : Set (H d × H d)) ×ˢ Iic K)
  have hCc : IsClosed C := hFc.preimage_isClosed_of_isClosed hBc.isClosed
    (isClosed_pairCone.prod isClosed_Iic)
  have hCcompact : IsCompact C := hBc.of_isClosed_subset hCc inter_subset_left
  have hCm (z : Point d) : z ∈ C ↔ z ∈ B ∧ z ∈ feasible S η ∧ objective ε z ≤ K := by
    simp only [C, mem_inter_iff, mem_preimage, mem_prod, mem_Iic, F]
    constructor
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, (feasible_iff_cone S η z).mpr ⟨hBD hz, hc⟩, hf⟩
    · rintro ⟨hz, hc, hf⟩
      exact ⟨hz, ((feasible_iff_cone S η z).mp hc).2, hf⟩
  have hnonempty : C.Nonempty := by
    refine ⟨z₀, (hCm z₀).mpr ⟨?_, hz₀, hf₀⟩⟩
    exact sublevel_box S η hη hε hK hS₁ hS₂ hz₀ hf₀
  obtain ⟨z, hz, hmin⟩ := hCcompact.exists_isMinOn hnonempty (continuous_objective ε).continuousOn
  have hzm := (hCm z).mp hz
  refine ⟨z, hzm.2.1, hzm.2.2, fun w hw => ?_⟩
  by_cases hfw : objective ε w ≤ K
  · apply hmin
    exact (hCm w).mpr ⟨sublevel_box S η hη hε hK hS₁ hS₂ hw hfw, hw, hfw⟩
  · exact hzm.2.2.trans (le_of_lt (lt_of_not_ge hfw))

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_re0a799_2 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma eta_apply (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (Z : H d) :
    eta c A x Z = ∑ i, (c * psi (x i)) • sandwich (A i) Z := by
  simp [eta]

lemma psi_bounds {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ psi x ∧ psi x ≤ 1 := by
  have hr : 0 ≤ 1-x^2 := by have hh := abs_le.mp hx; nlinarith
  exact ⟨Real.rpow_nonneg hr _, Real.rpow_le_one hr (by nlinarith [sq_nonneg x]) (by norm_num)⟩

lemma eta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {x : Coordinates N} (hx : Cube x) :
    ∀ Z ∈ psdCone d, eta c A x Z ∈ psdCone d := by
  intro Z hZ
  rw [eta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (psi_bounds (hx i)).1)

lemma eta_symmetric (c : ℝ) (A : Fin N → H d) (x : Coordinates N) : SymmetricMap (eta c A x) := by
  intro U V
  change inner ℝ U (eta c A x V) = inner ℝ (eta c A x U) V
  simp only [eta_apply, sum_inner, inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = (c*psi (x i)) * inner ℝ U (sandwich (A i) V) :=
      real_inner_smul_right U (sandwich (A i) V) (c*psi (x i))
    _ = (c*psi (x i)) * inner ℝ (sandwich (A i) U) V := by rw [inner_sandwich]
    _ = _ := (real_inner_smul_left (sandwich (A i) U) V (c*psi (x i))).symm

lemma sum_le_one (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) : (∑ i, A i) ≤ (Hermitian.one : H d) := by
  have hp := trace_bound_above (psd_sum Finset.univ A fun i _ => hA i)
  simpa only [realTrace_sum,htr,one_smul] using hp

lemma S_bounds (A : Fin N → H d) (hA : ∀ i, A i ∈ psdCone d)
    (htr : ∑ i, _root_.OAI.CurrentKS.Hermitian.realTrace (A i) = 1) {x : Coordinates N} (hx : Cube x) :
    -(Hermitian.one : H d) ≤ S A x ∧ S A x ≤ (Hermitian.one : H d) := by
  have hsum := sum_le_one A hA htr
  have hupper : S A x ≤ ∑ i, A i := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [one_smul] using scalar_mono_psd (hA i) (abs_le.mp (hx i)).2
  have hlower : -(∑ i, A i) ≤ S A x := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    have hh := scalar_mono_psd (hA i) (abs_le.mp (hx i)).1
    have he : (-1 : ℝ) • A i = -A i := neg_one_smul ℝ (A i)
    rw [he] at hh
    exact hh
  exact ⟨(neg_le_neg hsum).trans hlower,hupper.trans hsum⟩

lemma eta_one_bound {c ν : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hν : (∑ i, sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    {x : Coordinates N} (hx : Cube x) : eta c A x (Hermitian.one : H d) ≤ (c*ν) • (Hermitian.one : H d) := by
  rw [eta_apply,SemigroupAction.mul_smul]
  apply le_trans _ (smul_order hν hc)
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mono_psd (sandwich_psd _ _ one_mem_psdCone)
    (mul_le_of_le_one_right hc (psi_bounds (hx i)).2)

end CurrentKS.State

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma scalar_feasible (S : H d) (η : H d →L[ℝ] H d) {s b a : ℝ}
    (hs₁ : -s • (Hermitian.one : H d) ≤ S) (hs₂ : S ≤ s • (Hermitian.one : H d))
    (hb : η (Hermitian.one : H d) ≤ b • (Hermitian.one : H d)) (ha : 0 < a) :
    (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) ∈ feasible S η := by
  have hpd := pd_smul (show (Hermitian.one : H d) ∈ pd d from Matrix.PosDef.one) ha
  apply (feasible_iff _ _ _).mpr
  refine ⟨hpd,hpd,?_,?_⟩
  · change invH (a • (Hermitian.one : H d)) + S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        show a⁻¹ • (Hermitian.one : H d) + S + a • η (Hermitian.one : H d) ≤ _ from
          add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hs₂) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring
  · change invH (a • (Hermitian.one : H d)) - S + η (a • (Hermitian.one : H d)) ≤
      (s+a⁻¹+b*a) • (Hermitian.one : H d)
    rw [invH_scalar,map_smul]
    have hns : -S ≤ s • (Hermitian.one : H d) := by
      have hh := neg_le_neg hs₁
      rw [neg_smul s (Hermitian.one : H d), neg_neg] at hh
      exact hh
    change a⁻¹ • (Hermitian.one : H d) + -S + a • η (Hermitian.one : H d) ≤ _
    calc
      _ ≤ a⁻¹ • (Hermitian.one : H d) + s • (Hermitian.one : H d) + a • (b • (Hermitian.one : H d)) :=
        add_le_add (add_le_add (le_refl (a⁻¹ • (Hermitian.one : H d))) hns) (smul_order hb ha.le)
      _ = (s+a⁻¹+b*a) • (Hermitian.one : H d) := by
        rw [smul_smul,← add_smul,← add_smul]
        congr 1
        ring

lemma scalar_objective (ε s b a : ℝ) :
    objective ε (s+a⁻¹+b*a, a • (Hermitian.one : H d), a • (Hermitian.one : H d)) =
      s+a⁻¹+(b+2*d*ε)*a := by
  simp only [objective,realTrace_add,realTrace_smul,realTrace_one]
  ring

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormalizedMinimizer
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

theorem normalized_minimizer [NeZero d] (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {ε : ℝ} (hε : 0 < ε)
    (hεd : ε*d ≤ 1) (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d))
    (hηI : η (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d)) :
    ∃ z ∈ feasible S η,objective ε z ≤ 100 ∧
      ∀ w ∈ feasible S η,objective ε z ≤ objective ε w := by
  have hlo' : -(100:ℝ) • (Hermitian.one : H d) ≤ S := by
    apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  have hhi' : S ≤ (100:ℝ) • (Hermitian.one : H d) := by
    apply hhi.trans
    simpa only [one_smul] using scalar_mono_psd one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)
  let z₀ : Point d := (1+(1/20:ℝ)⁻¹+384*(1/20),(1/20:ℝ) • (Hermitian.one : H d),(1/20:ℝ) • (Hermitian.one : H d))
  have hz₀ : z₀ ∈ feasible S η :=
    scalar_feasible S η (s:=1) (b:=384) (a:=1/20)
      (by rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul]; exact hlo)
      (by simpa only [one_smul] using hhi) hηI (by norm_num)
  have hf : objective ε z₀ ≤ 100 := by
    dsimp [z₀]
    rw [scalar_objective]
    norm_num
    nlinarith
  exact exists_minimizer S η hη hε (by norm_num) hlo' hhi' z₀ hz₀ hf
end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Value
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma value_eq_of_min (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d)
    (z : Point d) (hz : z ∈ feasible S η)
    (hmin : ∀ w ∈ feasible S η, objective ε z ≤ objective ε w) :
    value ε S η = objective ε z := by
  apply IsLeast.csInf_eq
  refine ⟨⟨z,hz,rfl⟩,?_⟩
  rintro b ⟨w,hw,rfl⟩
  exact hmin w hw

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_CoarseBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

lemma coarseBudget_bounds {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    1 ≤ coarseBudget d N ε σ ∧ (d:ℝ)+1 ≤ coarseBudget d N ε σ ∧
    |ε| ≤ coarseBudget d N ε σ ∧
    200+(200/ε)*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    200*((d:ℝ)+1) ≤ coarseBudget d N ε σ ∧
    ((d:ℝ)+1)+N ≤ coarseBudget d N ε σ ∧
    384*N*(1+800/σ^3) ≤ coarseBudget d N ε σ := by
  have hd : 0 ≤ (d:ℝ)+1 := by positivity
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hp : 0 ≤ (200/ε)*((d:ℝ)+1) := by positivity
  have hr : 0 ≤ 384*(N:ℝ)*(1+800/σ^3) := by positivity
  have he := abs_nonneg ε
  dsimp [coarseBudget]
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor; · linarith
  constructor <;> linarith

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ValueFeasible
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p8
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p8
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.Variational.valueFeasibleOperatorNormedSpace
attribute [local instance] OAI.CurrentKS.Variational.valueFeasiblePairNormedSpace
lemma value_le_feasible [NeZero d] (ε : ℝ) (hε : 0 ≤ ε) (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d, η A ∈ psdCone d) (z : Point d) (hz : z ∈ feasible S η) :
    value ε S η ≤ objective ε z := by
  have hb : BddBelow (objective ε '' feasible S η) := by
    refine ⟨0,?_⟩
    rintro r ⟨w,hw,rfl⟩
    obtain ⟨ht,hX,hY⟩ := trace_bounds_of_feasible S η hη hw
    simp only [objective,realTrace_add]
    exact add_nonneg ht (mul_nonneg hε (add_nonneg hX hY))
  exact csInf_le hb ⟨z,hz,rfl⟩

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_LightPoint
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.State.line_zero _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Interaction
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma lightPoint_of_optimizer [NeZero d] (A : Fin N → H d) (x : Coordinates N) (S₀ : H d)
    {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1)
    (hA : ∀ i, A i ∈ psdCone d) (hA0 : ∀ i, A i ≠ 0)
    (hrank : ∀ i, (A i : Hermitian.Mat d).rank ≤ 1) (hx : ∀ i, |x i| < 1)
    (hlo : -(100 : ℝ) • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ (100 : ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ Variational.feasible (S₀+S A x) (eta 384 A x))
    (hsub : objective ε z ≤ 100)
    (hmin : ∀ w ∈ Variational.feasible (S₀+S A x) (eta 384 A x), objective ε z ≤ objective ε w)
    (hlightA : ∀ i, 384*psi (x i)*inner ℝ (A i) z.2.1 < 1+x i)
    (hlightB : ∀ i, 384*psi (x i)*inner ℝ (A i) z.2.2 < 1-x i) :
    ∃ p : LightPoint d N, p.A = A ∧ p.x = x ∧ p.fixedPart = S₀ ∧ p.ε = ε ∧ p.primal = z := by
  obtain ⟨P,Q,hP,hQ,hPle,hQle,htr,_,_,ht,hX,hY⟩ := kkt (S₀+S A x) (eta 384 A x)
    (eta_positive (by norm_num) A (fun i => (hx i).le)) (eta_symmetric 384 A x) hε hlo hhi z hz hmin
  exact ⟨⟨A,x,S₀,ε,hε,hε₁,hA,hA0,hrank,hx,hlo,hhi,z,hz,hsub,hmin,P,Q,hP,hQ,hPle,hQle,htr,
    ht,hX,hY,hlightA,hlightB⟩,rfl,rfl,rfl,rfl,rfl⟩

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_EndpointCandidates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Difference
open CurrentKS.RationalRoot

variable {N : ℕ}

lemma endpoint_mem (x : Fin N → ℚ) (i : Fin N) (t : ℚ) (ht : |t|=1) :
    Function.update x i t ∈ endpointCandidates x := by
  have hh : t=(-1:ℚ) ∨ t=1 := by
    exact ((abs_eq (by norm_num : (0:ℚ) ≤ 1)).mp ht).symm
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_finRange i,?_⟩
  rcases hh with rfl|rfl <;> simp

end CurrentKS.Difference

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FacePotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State
open CurrentKS.Scalar CurrentKS.Calculus
open scoped BigOperators ContDiff

variable {d N : ℕ}

open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational CurrentKS.Calculus Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff


lemma valueCurve_bounds_nonneg {ε σ : ℝ} (hε : 0 < ε) (hσ : 0 < σ) :
    0 ≤ valueCurve2Bound d N ε σ ∧ 0 ≤ valueCurve3Bound d N ε σ := by
  have hB := (coarseBudget_bounds (d:=d) (N:=N) hε hσ).1
  dsimp [valueCurve2Bound,valueCurve3Bound]
  constructor <;> positivity

lemma scalar_hundred_bounds {S : H d} (hlo : -(Hermitian.one : H d) ≤ S)
    (hhi : S ≤ (Hermitian.one : H d)) :
    -(100:ℝ) • (Hermitian.one : H d) ≤ S ∧ S ≤ (100:ℝ) • (Hermitian.one : H d) := by
  constructor
  · apply le_trans _ hlo
    have hc := scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (-100:ℝ) ≤ -1)
    rw [neg_smul (1:ℝ) (Hermitian.one : H d),one_smul] at hc
    exact hc
  · apply hhi.trans
    simpa only [one_smul] using
      scalar_mono_psd (d:=d) one_mem_psdCone (by norm_num : (1:ℝ) ≤ 100)

end CurrentKS.State

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Potential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma sum_update_composite {α β : Type*} [AddCommGroup β] (f : Fin N → α → β)
    (x : Fin N → α) (i : Fin N) (a : α) :
    (∑ j, f j (Function.update x i a j)) = (∑ j, f j (x j))+f i a-f i (x i) := by
  simp only [Function.apply_update]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  have he := Finset.sum_erase_add Finset.univ (fun j => f j (x j)) (Finset.mem_univ i)
  rw [Finset.sdiff_singleton_eq_erase]
  rw [← he]
  abel

lemma S_update (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) :
    S A (Function.update x i t) = S A x+(t-x i) • A i := by
  rw [S,sum_update_composite (fun (j : Fin N) (r : ℝ) => r • A j) x i t]
  simp only [S]
  module

lemma eta_update (c : ℝ) (A : Fin N → H d) (x : Coordinates N) (i : Fin N) (t : ℝ) (Z : H d) :
    eta c A (Function.update x i t) Z = eta c A x Z+(c*(psi t-psi (x i))) • sandwich (A i) Z := by
  rw [eta_apply,sum_update_composite (fun (j : Fin N) (r : ℝ) => (c*psi r) • sandwich (A j) Z) x i t,eta_apply]
  module

lemma psi_endpoint {t : ℝ} (ht : |t| = 1) : psi t = 0 := by
  have hh : t^2 = 1 := by nlinarith [sq_abs t]
  simp [psi,hh]

lemma Cube_update {x : Coordinates N} (hx : Cube x) (i : Fin N) {t : ℝ} (ht : |t| ≤ 1) :
    Cube (Function.update x i t) := by
  intro j
  by_cases hj : j=i
  · subst j; simpa using ht
  · simpa [Function.update_of_ne hj] using hx j

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceEndpointFeasible
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma face_endpoint_feasible {c : ℝ} (A : Fin N → H d) (S₀ : H d) (x : Coordinates N) (i : Fin N) {t : ℝ}
    (ht : |t| = 1) (hA : A i ∈ psdCone d) (hrank : (A i : Mat d).rank ≤ 1)
    (z : Point d) (hz : z ∈ feasible ((S₀+S A x)) (eta c A x))
    (hplus : t-x i ≤ c*psi (x i)*inner ℝ (A i) z.2.2)
    (hminus : x i-t ≤ c*psi (x i)*inner ℝ (A i) z.2.1) :
    z ∈ feasible ((S₀+S A (Function.update x i t))) (eta c A (Function.update x i t)) := by
  erw [feasible_iff] at hz ⊢
  refine ⟨hz.1,hz.2.1,?_,?_⟩
  · have he : invH z.2.1+(S₀+S A (Function.update x i t))+eta c A (Function.update x i t) z.2.2 =
        invH z.2.1+(S₀+S A x)+eta c A x z.2.2 +
          (t-x i-c*psi (x i)*inner ℝ (A i) z.2.2) • A i := by
      rw [S_update,eta_update,psi_endpoint ht,zero_sub,mul_neg,
        sandwich_rank_one (A i) z.2.2 hA hrank]
      module
    erw [he]
    have hs : (t-x i-c*psi (x i)*inner ℝ (A i) z.2.2) • A i ≤ 0 := by
      simpa only [zero_smul] using scalar_mono_psd hA (sub_nonpos.mpr hplus)
    calc
      _ ≤ invH z.2.1+(S₀+S A x)+eta c A x z.2.2 := by
        simpa only [add_zero] using add_le_add (le_refl (invH z.2.1+(S₀+S A x)+eta c A x z.2.2)) hs
      _ ≤ _ := hz.2.2.1
  · have he : invH z.2.2-(S₀+S A (Function.update x i t))+eta c A (Function.update x i t) z.2.1 =
        invH z.2.2-(S₀+S A x)+eta c A x z.2.1 +
          (x i-t-c*psi (x i)*inner ℝ (A i) z.2.1) • A i := by
      rw [S_update,eta_update,psi_endpoint ht,zero_sub,mul_neg,
        sandwich_rank_one (A i) z.2.1 hA hrank]
      module
    erw [he]
    have hs : (x i-t-c*psi (x i)*inner ℝ (A i) z.2.1) • A i ≤ 0 := by
      simpa only [zero_smul] using scalar_mono_psd hA (sub_nonpos.mpr hminus)
    calc
      _ ≤ invH z.2.2-(S₀+S A x)+eta c A x z.2.1 := by
        simpa only [add_zero] using add_le_add (le_refl (invH z.2.2-(S₀+S A x)+eta c A x z.2.1)) hs
      _ ≤ _ := hz.2.2.2

lemma face_endpoint_potential_le [NeZero d] {ε lam : ℝ} (hε : 0≤ε)
    (A : Fin N → H d) (S₀ : H d) (x : Coordinates N) (hx : Cube x) (i : Fin N) {t : ℝ}
    (ht : |t|=1) (hA : A i∈psdCone d) (hrank : (A i : Mat d).rank≤1)
    (z : Point d) (hz : z∈feasible (S₀+S A x) (eta 384 A x))
    (hmin : ∀ w∈feasible (S₀+S A x) (eta 384 A x),objective ε z≤objective ε w)
    (hplus : t-x i≤384*psi (x i)*inner ℝ (A i) z.2.2)
    (hminus : x i-t≤384*psi (x i)*inner ℝ (A i) z.2.1) :
    facePotential ε lam S₀ A (Function.update x i t)≤facePotential ε lam S₀ A x-lam*psi (x i) := by
  have hf := face_endpoint_feasible A S₀ x i ht hA hrank z hz hplus hminus
  have hv := value_le_feasible ε hε _ _ (eta_positive (by norm_num : (0:ℝ)≤384) A (Cube_update hx i ht.le)) z hf
  rw [←value_eq_of_min ε _ _ z hz hmin] at hv
  rw [facePotential,facePotential,penalty,penalty,
    sum_update_composite (fun (_ : Fin N) (r : ℝ) => psi r) x i t,psi_endpoint ht,add_zero]
  nlinarith

theorem endpoint_or_light [NeZero d] (A : Fin N → H d) (S₀ : H d) (x : Coordinates N)
    {ε lam : ℝ} (hε : 0<ε) (hε1 : ε≤1)
    (hA : ∀ i,A i∈psdCone d) (hA0 : ∀ i,A i≠0) (hrank : ∀ i,(A i : Mat d).rank≤1)
    (hx : ∀ i,|x i|<1)
    (hlo : -(100:ℝ) • (Hermitian.one : H d)≤S₀+S A x)
    (hhi : S₀+S A x≤(100:ℝ) • (Hermitian.one : H d))
    (z : Point d) (hz : z∈feasible (S₀+S A x) (eta 384 A x)) (hsub : objective ε z≤100)
    (hmin : ∀ w∈feasible (S₀+S A x) (eta 384 A x),objective ε z≤objective ε w) :
    (∃ (i : Fin N) (t : ℝ),|t|=1 ∧
      facePotential ε lam S₀ A (Function.update x i t)≤facePotential ε lam S₀ A x-lam*psi (x i)) ∨
    (∃ p : LightPoint d N,p.A=A ∧ p.x=x ∧ p.fixedPart=S₀ ∧ p.ε=ε ∧ p.primal=z) := by
  have hx1 : Cube x := fun i => (hx i).le
  have hxlo (i : Fin N) := (abs_lt.mp (hx i)).1
  have hxhi (i : Fin N) := (abs_lt.mp (hx i)).2
  have hposX (i : Fin N) : 0≤384*psi (x i)*inner ℝ (A i) z.2.1 :=
    mul_nonneg (mul_nonneg (by norm_num) (psi_pos (hx i)).le)
      (inner_nonneg_of_psd _ _ (hA i) hz.1.1.posSemidef)
  have hposY (i : Fin N) : 0≤384*psi (x i)*inner ℝ (A i) z.2.2 :=
    mul_nonneg (mul_nonneg (by norm_num) (psi_pos (hx i)).le)
      (inner_nonneg_of_psd _ _ (hA i) hz.1.2.posSemidef)
  by_cases hLA : ∀ i,384*psi (x i)*inner ℝ (A i) z.2.1<1+x i
  · by_cases hLB : ∀ i,384*psi (x i)*inner ℝ (A i) z.2.2<1-x i
    · exact Or.inr (lightPoint_of_optimizer A x S₀ hε hε1 hA hA0 hrank hx hlo hhi z hz hsub hmin hLA hLB)
    · push Not at hLB
      obtain ⟨i,hi⟩ := hLB
      refine Or.inl ⟨i,1,by norm_num,?_⟩
      exact face_endpoint_potential_le hε.le A S₀ x hx1 i (by norm_num) (hA i) (hrank i) z hz hmin hi (by linarith [hposX i,hxhi i])
  · push Not at hLA
    obtain ⟨i,hi⟩ := hLA
    refine Or.inl ⟨i,-1,by norm_num,?_⟩
    exact face_endpoint_potential_le hε.le A S₀ x hx1 i (by norm_num) (hA i) (hrank i) z hz hmin
      (by linarith [hposY i,hxlo i]) (by linarith)

lemma psi_ge_strip {x σ : ℝ} (hx : |x|<1) (hstrip : |x|≤1-σ) : σ≤psi x := by
  have hab := abs_nonneg x
  have hsq := sq_abs x
  have hb := psi_ge_base hx
  nlinarith [sq_nonneg (1-|x|)]

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_MovementBudget
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

lemma movementBudget_one_le (n : ℕ) (ε : ℚ) : 1 ≤ movementBudget n ε := le_max_left _ _

lemma movementBudget_pos (n : ℕ) (ε : ℚ) : 0 < movementBudget n ε :=
  lt_of_lt_of_le (by norm_num) (movementBudget_one_le n ε)

lemma threshold_pos (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : 0 < lam) : 0 < threshold n ε lam := by
  unfold threshold
  have hp := movementBudget_pos n ε
  positivity

lemma threshold_le_one (n : ℕ) (ε : ℚ) {lam : ℚ} (hlam : lam ≤ 1) : threshold n ε lam ≤ 1 := by
  unfold threshold
  have hp := movementBudget_pos n ε
  have h1 := movementBudget_one_le n ε
  apply (div_le_one (by positivity)).mpr
  nlinarith

lemma threshold_relation (n : ℕ) (ε lam : ℚ) :
    lam=512*threshold n ε lam*(movementBudget n ε)^2 := by
  have hp := (movementBudget_pos n ε).ne'
  unfold threshold
  field_simp

lemma stepSize_spec {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stepSize a M σ ∧ stepSize a M σ ≤ σ/4 ∧ stepSize a M σ ≤ 1/4 ∧
      M*stepSize a M σ ≤ a/4 := by
  have hp : 0 < a/(4*M) := by positivity
  have hs : stepSize a M σ ≤ a/(4*M) := min_le_right _ _ |>.trans (min_le_left _ _)
  refine ⟨by unfold stepSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_right _ _),?_⟩
  have hh := (le_div_iff₀ (show (0:ℚ) < 4*M by positivity)).mp hs
  linarith

lemma stencilSize_spec {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    0 < stencilSize n a M σ ∧ stencilSize n a M σ ≤ σ/8 ∧
    stencilSize n a M σ ≤ 1 ∧ stencilSize n a M σ ≤ a/(64*M*n) := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold stencilSize;positivity,min_le_left _ _,
    (min_le_right _ _).trans (min_le_left _ _),(min_le_right _ _).trans (min_le_right _ _)⟩

lemma meshSize_spec {n : ℕ} (hn : 0 < n) {a M s : ℚ} (ha : 0 < a) (hM : 0 < M) (hs : 0 < s) :
    0 < meshSize n a M s ∧ (n:ℚ)*meshSize n a M s/2 ≤ s*(a/(1024*M))/8 := by
  have hnr : (0:ℚ) < n := by exact_mod_cast hn
  refine ⟨by unfold meshSize;positivity,?_⟩
  unfold meshSize
  apply le_of_eq
  field_simp
  ring

lemma schedule_radius {n : ℕ} (hn : 0 < n) {a M σ : ℚ} (ha : 0 < a) (hM : 0 < M) (hσ : 0 < σ) :
    stepSize a M σ+2*stencilSize n a M σ ≤ σ/2 := by
  have hs := (stepSize_spec ha hM hσ).2.1
  have hh := (stencilSize_spec hn ha hM hσ).2.1
  linarith

open CurrentKS.State

lemma coarseBudgetQ_cast (d n : ℕ) (ε σ : ℚ) :
    (coarseBudgetQ d n ε σ:ℝ)=coarseBudget d n (ε:ℝ) (σ:ℝ) := by
  simp only [coarseBudgetQ,coarseBudget,Rat.cast_add,Rat.cast_mul,Rat.cast_div,
    Rat.cast_pow,Rat.cast_natCast,Rat.cast_abs,Rat.cast_ofNat,Rat.cast_one]

lemma curveBudget_cast (d n : ℕ) (ε σ lam : ℚ) :
    (curveBudget d n ε σ lam:ℝ)=potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
  simp only [curveBudget,potentialCurveBound,valueCurve2Q,valueCurve3Q,
    valueCurve2Bound,valueCurve3Bound,Rat.cast_add,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_natCast,Rat.cast_abs,Rat.cast_inv,Rat.cast_one,Rat.cast_ofNat,coarseBudgetQ_cast]

lemma curveBudget_one_le (d n : ℕ) {ε σ : ℚ} (hε : 0 < ε) (hσ : 0 < σ) (lam : ℚ) :
    1 ≤ curveBudget d n ε σ lam := by
  have hεr : (0:ℝ) < ε := by exact_mod_cast hε
  have hσr : (0:ℝ) < σ := by exact_mod_cast hσ
  have hh := valueCurve_bounds_nonneg (d:=d) (N:=n) hεr hσr
  have hl : (0:ℝ) ≤ |(lam:ℝ)| *(n:ℝ)*(1+800/(σ:ℝ)^3) := by positivity
  have hc : (1:ℝ) ≤ potentialCurveBound d n (ε:ℝ) (σ:ℝ) (lam:ℝ) := by
    unfold potentialCurveBound
    linarith
  rw [←curveBudget_cast] at hc
  exact_mod_cast hc

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_C1Rational
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.State.LightPoint
open CurrentKS.Schedule

variable {d n : ℕ}

lemma C1_eq_rational (p : LightPoint d n) (ε : ℚ) (hε : p.ε=(ε:ℝ)) :
    p.C1=(movementBudget n ε:ℝ) := by
  simp only [C1,E0,J,s0,movementBudget,hε,Rat.cast_max,Rat.cast_mul,Rat.cast_add,
    Rat.cast_div,Rat.cast_pow,Rat.cast_natCast,Rat.cast_ofNat,Rat.cast_one]

lemma Psi_eq_facePotential (p : LightPoint d n) :
    p.Psi=fun lam => facePotential p.ε lam p.fixedPart p.A := rfl

end CurrentKS.State.LightPoint

namespace CurrentKS.Difference
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational CurrentKS.Schedule
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d n : ℕ}

lemma pointCast_update (x : Fin n → ℚ) (i : Fin n) (t : ℚ) :
    pointCast (Function.update x i t)=Function.update (pointCast x) i (t:ℝ) := by
  funext j
  by_cases hj : j=i
  · subst j;simp [pointCast]
  · simp [pointCast,Function.update_of_ne hj]

theorem face_candidates_progress [NeZero d] [NeZero n]
    (A : Fin n → H d) (S₀ : H d) (x : Fin n → ℚ)
    (query : (Fin n → ℚ) → ℚ) (ε lam σ h a M s ρ : ℚ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεd : ε*d ≤ 1) (hlam : 0 < lam)
    (hσ : 0 < σ) (hx : ∀ i,|x i| ≤ 1-σ)
    (hA : ∀ i,A i∈psdCone d) (hA0 : ∀ i,A i≠0) (hrank : ∀ i,(A i : Mat d).rank ≤ 1)
    (hlo : -(Hermitian.one : H d) ≤ S₀+S A (pointCast x))
    (hhi : S₀+S A (pointCast x) ≤ (Hermitian.one : H d))
    (hη : eta 384 A (pointCast x) (Hermitian.one : H d) ≤ (384:ℝ) • (Hermitian.one : H d))
    (haeq : a=threshold n ε lam) (ha : 0 < a) (ha1 : a ≤ 1) (hM1 : 1 ≤ M)
    (hs : 0 < s) (hs1 : s ≤ 1/4) (hsσ : s ≤ σ/4) (hstep : M*s ≤ a/4)
    (hh : 0 < h) (hh1 : h ≤ 1) (hhsmall : h ≤ a/(64*M*n))
    (hρ : 0 < ρ) (hmesh : (n:ℚ)*ρ/2 ≤ s*(a/(1024*M))/8)
    (hreg : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) →
      ContDiffAt ℝ 3 (facePotential (ε:ℝ) (lam:ℝ) S₀ A) y)
    (hders : ∀ y,‖y-pointCast x‖ ≤ (s:ℝ)+2*(h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 2 (fun t : ℝ => facePotential (ε:ℝ) (lam:ℝ) S₀ A (y+t • u)) 0| ≤ (M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => facePotential (ε:ℝ) (lam:ℝ) S₀ A (y+t • u)) 0| ≤ (M:ℝ))
    (hquery : ∀ y,‖pointCast y-pointCast x‖ ≤ 2*(h:ℝ) →
      |(query y:ℝ)-facePotential (ε:ℝ) (lam:ℝ) S₀ A (pointCast y)| ≤
        (a:ℝ)*(h:ℝ)^2/(128*n)) :
    ∃ y∈allCandidates query x h a M s ρ,
      facePotential (ε:ℝ) (lam:ℝ) S₀ A (pointCast y) ≤
        facePotential (ε:ℝ) (lam:ℝ) S₀ A (pointCast x)-2*(a:ℝ)*(s:ℝ)^2 := by
  have hxr : ∀ i,|pointCast x i| < 1 := by
    intro i
    have hh : |(x i:ℝ)| ≤ 1-(σ:ℝ) := by exact_mod_cast hx i
    have hσr : (0:ℝ) < σ := by exact_mod_cast hσ
    change |(x i:ℝ)| < 1
    linarith
  obtain ⟨z,hz,hsub,hmin⟩ := normalized_minimizer (ε:=(ε:ℝ)) (S₀+S A (pointCast x))
    (eta 384 A (pointCast x)) (eta_positive (by norm_num : (0:ℝ) ≤ 384) A (fun i => (hxr i).le))
    (by exact_mod_cast hε) (by exact_mod_cast hεd) hlo hhi hη
  have h100 := scalar_hundred_bounds hlo hhi
  rcases endpoint_or_light (ε:=(ε:ℝ)) A S₀ (pointCast x) (by exact_mod_cast hε) (by exact_mod_cast hε1)
    hA hA0 hrank hxr h100.1 h100.2 z hz hsub hmin (lam:=(lam:ℝ)) with hend|hlight
  · obtain ⟨i,t,ht,hdec⟩ := hend
    obtain ⟨tq,htq,heq⟩ : ∃ tq : ℚ,|tq|=1 ∧ (tq:ℝ)=t := by
      by_cases hs : 0 ≤ t
      · rw [abs_of_nonneg hs] at ht
        exact ⟨1,by norm_num,by simpa using ht.symm⟩
      · rw [abs_of_neg (lt_of_not_ge hs)] at ht
        exact ⟨-1,by norm_num,by push_cast <;> linarith⟩
    have hp : (σ:ℝ) ≤ psi (pointCast x i) :=
      psi_ge_strip (hxr i) (show |(x i:ℝ)| ≤ 1-(σ:ℝ) by exact_mod_cast hx i)
    have hC := movementBudget_one_le n ε
    have he := threshold_relation n ε lam
    rw [←haeq] at he
    have hale : a ≤ lam := by nlinarith [sq_nonneg (movementBudget n ε-1)]
    have hdecq : 2*a*s^2 ≤ lam*σ := by
      have hm := mul_le_mul_of_nonneg_left hsσ hs.le
      have hm' := mul_le_mul_of_nonneg_left hs1 hσ.le
      have hass : 2*s^2 ≤ σ := by nlinarith
      have hscale := mul_le_mul_of_nonneg_left hass ha.le
      have hal := mul_le_mul_of_nonneg_right hale hσ.le
      nlinarith
    have hdecr : 2*(a:ℝ)*(s:ℝ)^2 ≤ (lam:ℝ)*(σ:ℝ) := by exact_mod_cast hdecq
    have hlamr : (0:ℝ) ≤ lam := by exact_mod_cast hlam.le
    refine ⟨Function.update x i tq,List.mem_append_left _ (endpoint_mem x i tq htq),?_⟩
    rw [pointCast_update,heq]
    linarith [mul_le_mul_of_nonneg_left hp hlamr]
  · obtain ⟨p,hpA,hpx,hpS,hpε,_⟩ := hlight
    have hfun : p.Psi (lam:ℝ)=facePotential (ε:ℝ) (lam:ℝ) S₀ A := by
      rw [p.Psi_eq_facePotential,hpA,hpS,hpε]
    have hrel : (lam:ℝ)=512*(a:ℝ)*p.C1^2 := by
      rw [p.C1_eq_rational ε hpε]
      exact_mod_cast (by simpa only [haeq] using threshold_relation n ε lam)
    have hh := p.computed_candidates_progress query x hpx (lam:ℝ) h a M s ρ
      ha ha1 hM1 hrel hs hs1 hstep ‹0 < h› hh1 hhsmall hρ hmesh
      (by simpa only [hfun] using hreg) (by simpa only [hfun] using hders)
      (by simpa only [hfun] using hquery)
    obtain ⟨y,hy,hd⟩ := hh
    exact ⟨y,List.mem_append_right _ hy,by simpa only [hfun,hpx] using hd⟩

end CurrentKS.Difference

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Lookup
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
variable {N n : ℕ}

lemma lookup_some {e : Fin n → Fin N} {i : Fin N} {j : Fin n}
    (h : lookup e i=some j) : e j=i := by
  have hh := List.find?_some h
  exact of_decide_eq_true hh

lemma lookup_none_iff (e : Fin n → Fin N) (i : Fin N) :
    lookup e i=none ↔ ∀ j,e j≠i := by
  simp [lookup,List.find?_eq_none]

lemma lookup_self {e : Fin n → Fin N} (he : Function.Injective e) (j : Fin n) :
    lookup e (e j)=some j := by
  cases hh : lookup e (e j) with
  | none => exact False.elim ((lookup_none_iff e (e j)).mp hh j rfl)
  | some k =>
    have hk := he (lookup_some hh)
    cases hk
    rfl

lemma map_extend {β γ : Type*} (f : β → γ) (e : Fin n → Fin N)
    (base : Fin N → β) (y : Fin n → β) :
    (fun i => f (extend e base y i))=extend e (fun i => f (base i)) (fun j => f (y j)) := by
  funext i
  unfold extend
  cases lookup e i <;> rfl

lemma activeIndices_mem (x : Fin N → ℚ) (i : Fin N) :
    i∈activeIndices x ↔ |x i|<1 := by simp [activeIndices]

lemma activeIndex_injective (x : Fin N → ℚ) : Function.Injective (activeIndex x) := by
  exact ((List.nodup_finRange N).filter _).injective_get

lemma activeIndex_range (x : Fin N → ℚ) (i : Fin N) :
    (∃ j,activeIndex x j=i) ↔ |x i|<1 := by
  rw [←activeIndices_mem]
  exact List.mem_iff_get.symm

lemma extend_cube {e : Fin n → Fin N} (x : Fin N → ℚ) (y : Fin n → ℚ)
    (hx : ∀ i,|x i|≤1) (hy : ∀ j,|y j|≤1) : ∀ i,|extend e x y i|≤1 := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hx i
  | some j => exact hy j

lemma sum_lookup {β : Type*} [AddCommMonoid β] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → Fin n → β) :
    (∑ i,(lookup e i).elim 0 (f i))=∑ j,f (e j) j := by
  symm
  apply Fintype.sum_of_injective e he
  · intro i hi
    have hn : ∀ j,e j≠i := fun j hj => hi ⟨j,hj⟩
    simp only [(lookup_none_iff e i).mpr hn,Option.elim_none]
  · intro j
    simp only [lookup_self he,Option.elim_some]

lemma sum_extend {β γ : Type*} [AddCommMonoid γ] (e : Fin n → Fin N)
    (he : Function.Injective e) (f : Fin N → β → γ) (base : Fin N → β) (y : Fin n → β) :
    (∑ i,f i (extend e base y i))=
      (∑ i,(lookup e i).elim (f i (base i)) (fun _ => 0))+(∑ j,f (e j) (y j)) := by
  rw [←sum_lookup e he (fun i j => f i (y j)),←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold extend
  cases lookup e i <;> simp

lemma real_active_outside_endpoint (x : Fin N → ℚ) (hx : ∀ i,|x i|≤1) (i : Fin N)
    (hi : lookup (activeIndex x) i=none) : |(x i:ℝ)|=1 := by
  have hn : ¬|x i|<1 := by
    intro h
    obtain ⟨j,hj⟩ := (activeIndex_range x i).mpr h
    exact (lookup_none_iff _ _).mp hi j hj
  have he : |x i|=1 := le_antisymm (hx i) (le_of_not_gt hn)
  exact_mod_cast he

end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_ParameterCube
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d N : ℕ}

lemma etaTheta_apply (c : ℝ) (A : Fin N → H d) (θ : Coordinates N) (Z : H d) :
    etaTheta c A θ Z = ∑ i,(c*θ i) • sandwich (A i) Z := by
  exact sum_apply Finset.univ (fun i => (c*θ i) • sandwichCLM (A i)) Z

lemma parameterCube_psi {x : Coordinates N} (hx : Cube x) : ParameterCube (fun i => psi (x i)) :=
  fun i => psi_bounds (hx i)

lemma etaTheta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {θ : Coordinates N}
    (hθ : ParameterCube θ) : ∀ Z ∈ psdCone d, etaTheta c A θ Z ∈ psdCone d := by
  intro Z hZ
  rw [etaTheta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (hθ i).1)

lemma sandwich_mono_order (A : H d) {U V : H d} (hUV : U ≤ V) : sandwich A U ≤ sandwich A V := by
  apply sub_nonneg.mp
  rw [← sandwich_sub]
  exact psd_nonneg (sandwich_psd A (V-U) ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr hUV)))

lemma etaTheta_difference_le {c ν δ R : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (θ φ : Coordinates N) (hdiff : ∀ i, θ i-φ i ≤ δ)
    (Z : H d) (hZ : Z ∈ psdCone d) (hZR : Z ≤ R • (Hermitian.one : H d)) :
    etaTheta c A θ Z-etaTheta c A φ Z ≤ (c*δ*R*ν) • (Hermitian.one : H d) := by
  have hsum : (∑ i,sandwich (A i) Z) ≤ (R*ν) • (Hermitian.one : H d) := by
    calc
      _ ≤ ∑ i,sandwich (A i) (R • (Hermitian.one : H d)) :=
        Finset.sum_le_sum fun i _ => sandwich_mono_order (A i) hZR
      _ = R • (∑ i,sandwich (A i) (Hermitian.one : H d)) := by
        simp only [sandwich_smul,Finset.smul_sum]
      _ ≤ R • (ν • (Hermitian.one : H d)) := smul_order hν hR
      _ = _ := by rw [smul_smul]
  calc
    _ = ∑ i,(c*(θ i-φ i)) • sandwich (A i) Z := by
      simp only [etaTheta_apply,← Finset.sum_sub_distrib,mul_sub]
      apply Finset.sum_congr rfl
      intro i _
      exact (sub_smul (c*θ i) (c*φ i) (sandwich (A i) Z)).symm
    _ ≤ ∑ i,(c*δ) • sandwich (A i) Z := by
      apply Finset.sum_le_sum
      intro i _
      exact scalar_mono_psd (sandwich_psd _ _ hZ) (mul_le_mul_of_nonneg_left (hdiff i) hc)
    _ = (c*δ) • (∑ i,sandwich (A i) Z) := by rw [Finset.smul_sum]
    _ ≤ (c*δ) • ((R*ν) • (Hermitian.one : H d)) := smul_order hsum (mul_nonneg hc hδ)
    _ = _ := by rw [smul_smul]; congr 1; ring

lemma etaTheta_shift_feasible {c ν δ R : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (θ φ : Coordinates N) (hdiff : ∀ i, φ i-θ i ≤ δ) (S : H d)
    (z : Point d) (hz : z ∈ feasible S (etaTheta c A θ))
    (hX : z.2.1 ≤ R • (Hermitian.one : H d)) (hY : z.2.2 ≤ R • (Hermitian.one : H d)) :
    (z.1+c*δ*R*ν,z.2) ∈ feasible S (etaTheta c A φ) := by
  obtain ⟨hpX,hpY,h₁,h₂⟩ := (feasible_iff _ _ _).mp hz
  refine (feasible_iff _ _ _).mpr ⟨hpX,hpY,?_,?_⟩
  · have hh := etaTheta_difference_le hc hδ hR A hν φ θ hdiff z.2.2 hpY.posSemidef hY
    have hb := add_le_add h₁ hh
    convert hb using 1 <;> first | rfl | module
  · have hh := etaTheta_difference_le hc hδ hR A hν φ θ hdiff z.2.1 hpX.posSemidef hX
    have hb := add_le_add h₂ hh
    convert hb using 1 <;> first | rfl | module

lemma objective_shift (ε t : ℝ) (z : Point d) :
    objective ε (z.1+t,z.2) = objective ε z+t := by simp only [objective] <;> ring

lemma etaTheta_value_le [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν δ : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1) (hδ : 0 ≤ δ)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ φ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) (hφ : ParameterCube φ)
    (hdiff : ∀ i,θ i-φ i ≤ δ) :
    value (ν/d) (S A x) (etaTheta 384 A θ) ≤
      value (ν/d) (S A x) (etaTheta 384 A φ)+38400*(d : ℝ)*δ := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d : ℝ) := div_pos hν hd
  obtain ⟨z,hz,hz100,hzmin⟩ := etaTheta_minimizer A hA htr hν hν₁ hvar x φ hx hφ
  have hb := S_bounds A hA htr hx
  have hl : -(100 : ℝ) • (Hermitian.one : H d) ≤ S A x :=
    (show -(100 : ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) by
      simpa only [neg_one_smul ℝ (Hermitian.one : H d)] using
        scalar_one_mono (d := d) (show (-100 : ℝ) ≤ -1 by norm_num)).trans hb.1
  have hu : S A x ≤ (100 : ℝ) • (Hermitian.one : H d) := hb.2.trans (by
    simpa only [one_smul] using scalar_one_mono (d := d) (show (1 : ℝ) ≤ 100 by norm_num))
  have hbox := sublevel_box (S A x) (etaTheta 384 A φ)
    (etaTheta_positive (by norm_num) A hφ) hε (show (0 : ℝ)<100 by norm_num) hl hu hz hz100
  have hshift := etaTheta_shift_feasible (show (0 : ℝ)≤384 by norm_num) hδ
    (show 0 ≤ 100/(ν/(d : ℝ)) by positivity) A hvar φ θ hdiff (S A x) z hz hbox.2.1.2 hbox.2.2.2
  have hmin := value_eq_of_min (ν/d) (S A x) (etaTheta 384 A φ) z hz hzmin
  calc
    _ ≤ objective (ν/d) (z.1+384*δ*(100/(ν/(d : ℝ)))*ν,z.2) :=
      value_le_feasible _ hε.le _ _ (etaTheta_positive (by norm_num) A hθ) _ hshift
    _ = objective (ν/d) z+384*δ*(100/(ν/(d : ℝ)))*ν := objective_shift _ _ _
    _ = _ := by rw [hmin]; congr 1; field_simp <;> ring

lemma sum_parameter_difference_le {θ φ : Coordinates N} {δ : ℝ}
    (h : ∀ i,θ i-φ i ≤ δ) : (∑ i,θ i)-(∑ i,φ i) ≤ (N : ℝ)*δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ _ : Fin N,δ := Finset.sum_le_sum fun i _ => h i
    _ = _ := by simp

lemma etaTheta_value_perturbation [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν δ lam : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1) (hδ : 0 ≤ δ) (hlam : 0 ≤ lam)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ φ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) (hφ : ParameterCube φ)
    (hdiff : ∀ i,|θ i-φ i| ≤ δ) :
    |(value (ν/d) (S A x) (etaTheta 384 A θ)+lam*∑ i,θ i)-
      (value (ν/d) (S A x) (etaTheta 384 A φ)+lam*∑ i,φ i)| ≤
      (38400*(d : ℝ)+lam*N)*δ := by
  have h₁ : ∀ i,θ i-φ i ≤ δ := fun i => (abs_le.mp (hdiff i)).2
  have h₂ : ∀ i,φ i-θ i ≤ δ := fun i => by have h := (abs_le.mp (hdiff i)).1; linarith
  have hv₁ := etaTheta_value_le A hA htr hν hν₁ hδ hvar x θ φ hx hθ hφ h₁
  have hv₂ := etaTheta_value_le A hA htr hν hν₁ hδ hvar x φ θ hx hφ hθ h₂
  have hs₁ := mul_le_mul_of_nonneg_left (sum_parameter_difference_le h₁) hlam
  have hs₂ := mul_le_mul_of_nonneg_left (sum_parameter_difference_le h₂) hlam
  apply abs_le.mpr
  constructor <;> nlinarith

end
end CurrentKS.State

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RootTolerance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.State.line_zero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalSDP
open scoped BigOperators

variable {d N : ℕ}

noncomputable section
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State CurrentKS.Scalar
open Matrix Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

lemma rootTolerance_pos {lam error : ℚ} (hlam : 0 ≤ lam) (he : 0 < error) :
    0 < rootTolerance d N lam error := by
  unfold rootTolerance
  positivity

lemma rootTolerance_bound {lam error : ℚ} (hlam : 0 ≤ lam) (he : 0 < error) :
    (38400*d+lam*N)*rootTolerance d N lam error ≤ error/2 := by
  have hD : 0 < (2*(38400*(d:ℚ)+lam*N+1)) := by positivity
  have hpos := rootTolerance_pos (d := d) (N := N) hlam he
  have hid : 2*(38400*(d:ℚ)+lam*N+1)*rootTolerance d N lam error=error := by
    unfold rootTolerance
    field_simp
  nlinarith

theorem potentialQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (x : Fin N → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (he : 0 < error) (he1 : error ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hx : Cube (fun i => (x i:ℝ))) :
    |(potentialQuery coords x ν lam error:ℝ)-
      (value ((ν:ℝ)/d) (S (rationalAtoms coords) (fun i => (x i:ℝ)))
        (eta 384 (rationalAtoms coords) (fun i => (x i:ℝ)))+
        (lam:ℝ)*∑ i,psi (x i:ℝ))| ≤ (error:ℝ) := by
  let δ := rootTolerance d N lam error
  let θ := fun i => approxPsi (x i) δ
  let xr : Coordinates N := fun i => (x i:ℝ)
  let θr : Coordinates N := fun i => (θ i:ℝ)
  let A := rationalAtoms coords
  have hδ : 0 < δ := rootTolerance_pos hlam he
  have hroot (i : Fin N) := approxPsi_spec (x i) δ (hx i) hδ
  have hθ : ParameterCube θr := by
    intro i
    change 0 ≤ (approxPsi (x i) δ:ℝ) ∧ (approxPsi (x i) δ:ℝ) ≤ 1
    exact ⟨by exact_mod_cast (hroot i).1.1,by exact_mod_cast (hroot i).1.2⟩
  have hdiff : ∀ i,|θr i-psi (xr i)| ≤ (δ:ℝ) := fun i => (hroot i).2
  have hq := (valueQueryPoint_correct coords x θ hA htr hν hν1
    (by positivity : 0 < error/4) (by linarith : error/4 ≤ 1) hvar hx hθ).2
  have hp := etaTheta_value_perturbation A hA htr (ν := (ν:ℝ)) (δ := (δ:ℝ)) (lam := (lam:ℝ)) (by exact_mod_cast hν)
    (by exact_mod_cast hν1) (by exact_mod_cast hδ.le) (by exact_mod_cast hlam)
    hvar xr θr (fun i => psi (xr i)) hx hθ (parameterCube_psi hx) hdiff
  let mid : ℝ := value ((ν:ℝ)/d) (S A xr) (etaTheta 384 A θr)+(lam:ℝ)*∑ i,θr i
  have hqm : |(potentialQuery coords x ν lam error:ℝ)-mid| ≤ (error:ℝ)/2 := by
    dsimp only [potentialQuery,mid]
    push_cast
    have heq : ((ν/d:ℚ):ℝ)=(ν:ℝ)/d := by push_cast; rfl
    simp only [heq,Rat.cast_div,Rat.cast_ofNat] at hq
    convert hq using 1 <;> first | rfl | ((try dsimp [θ,θr,A,xr,δ]); ring_nf)
  have hpm : |mid-(value ((ν:ℝ)/d) (S A xr) (eta 384 A xr)+
      (lam:ℝ)*∑ i,psi (xr i))| ≤ (error:ℝ)/2 := by
    apply hp.trans
    exact_mod_cast rootTolerance_bound (d := d) (N := N) hlam he
  change |(potentialQuery coords x ν lam error:ℝ)-
    (value ((ν:ℝ)/d) (S A xr) (eta 384 A xr)+(lam:ℝ)*∑ i,psi (xr i))| ≤ _
  exact (abs_sub_le _ mid _).trans (by linarith)

end
end CurrentKS.RationalSDP

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FixedPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

variable {d N n : ℕ}

lemma S_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d) (y : Coordinates n) :
    S A (extend e base y)=fixedPart e base A+S (fun j => A (e j)) y := by
  exact sum_extend e he (fun (i : Fin N) (t : ℝ) => (t • A i : H d)) base y

lemma penalty_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) :
    (∑ i,psi (extend e base y i))=∑ j,psi (y j) := by
  rw [sum_extend e he (fun _ t => psi t) base y]
  have hz : (∑ i,(lookup e i).elim (psi (base i)) (fun _ => 0))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases hi : lookup e i with
    | none => exact psi_endpoint (hb i hi)
    | some j => rfl
  rw [hz,zero_add]

lemma eta_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) (c : ℝ) :
    eta c A (extend e base y)=eta c (fun j => A (e j)) y := by
  apply ContinuousLinearMap.ext
  intro Z
  rw [eta_apply,eta_apply]
  have hsum := sum_extend e he (fun (i : Fin N) (t : ℝ) => ((c*psi t) • sandwich (A i) Z : H d)) base y
  rw [hsum]
  have hz : (∑ i,(lookup e i).elim ((c*psi (base i)) • sandwich (A i) Z) (fun _ => 0))=0 := by
    apply Finset.sum_eq_zero
    intro i _
    cases hi : lookup e i with
    | none => simp only [Option.elim_none,psi_endpoint (hb i hi),mul_zero,zero_smul]
    | some j => rfl
  rw [hz,zero_add]

lemma potential_extend (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hb : ∀ i,lookup e i=none → |base i|=1) (y : Coordinates n) (ε lam : ℝ) :
    value ε (S A (extend e base y)) (eta 384 A (extend e base y))+
      lam*∑ i,psi (extend e base y i)=
    value ε (fixedPart e base A+S (fun j => A (e j)) y) (eta 384 (fun j => A (e j)) y)+
      lam*∑ j,psi (y j) := by
  rw [S_extend e he,eta_extend e he base A hb,penalty_extend e he base hb]

end CurrentKS.RationalFace

namespace CurrentKS.RationalSDP
open CurrentKS.RationalFace

variable {d N n : ℕ}

open CurrentKS.Hermitian CurrentKS.HermitianCoordinates CurrentKS.Variational CurrentKS.State CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius

lemma faceQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (y : Fin (activeIndices base).length → ℚ)
    (hA : ∀ i,rationalAtoms coords i ∈ psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0<ν) (hν1 : ν≤1) (hlam : 0≤lam)
    (he : 0<error) (he1 : error≤1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i|≤1) (hy : ∀ j,|y j|≤1) :
    |(faceQuery coords base y ν lam error:ℝ)-
      (value ((ν:ℝ)/d)
        (fixedPart (activeIndex base) (fun i => (base i:ℝ)) (rationalAtoms coords)+
          S (fun j => rationalAtoms coords (activeIndex base j)) (fun j => (y j:ℝ)))
        (eta 384 (fun j => rationalAtoms coords (activeIndex base j)) (fun j => (y j:ℝ)))+
        (lam:ℝ)*∑ j,psi (y j:ℝ))|≤(error:ℝ) := by
  have hcube : Cube (fun i => ((extend (activeIndex base) base y i : ℚ):ℝ)) := by
    intro i
    change |((extend (activeIndex base) base y i : ℚ):ℝ)| ≤ 1
    exact_mod_cast extend_cube (e := activeIndex base) base y hb hy i
  have hq := potentialQuery_correct coords (extend (activeIndex base) base y)
    hA htr hν hν1 hlam he he1 hvar hcube
  have heq := potential_extend (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) (real_active_outside_endpoint base hb)
    (fun j => (y j:ℝ)) ((ν:ℝ)/d) (lam:ℝ)
  have hext := map_extend (fun q : ℚ => (q:ℝ)) (activeIndex base) base y
  have hext' : ∀ i, ((extend (activeIndex base) base y i : ℚ):ℝ) =
      extend (activeIndex base) (fun i => (base i:ℝ)) (fun j => (y j:ℝ)) i :=
    fun i => congrFun hext i
  simp_rw [hext'] at hq
  rw [heq] at hq
  exact hq

end CurrentKS.RationalSDP

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_RealExtendCube
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.State CurrentKS.Variational
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N n : ℕ}

lemma real_extend_cube (e : Fin n → Fin N) (base : Coordinates N) (y : Coordinates n)
    (hb : Cube base) (hy : Cube y) : Cube (extend e base y) := by
  intro i
  unfold extend
  cases lookup e i with
  | none => exact hb i
  | some j => exact hy j

lemma face_order_bounds (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hA : ∀ i,A i∈psdCone d) (htr : ∑ i,Hermitian.realTrace (A i)=1)
    (hb : Cube base) (y : Coordinates n) (hy : Cube y) :
    -(Hermitian.one : H d)≤fixedPart e base A+S (fun j => A (e j)) y ∧
    fixedPart e base A+S (fun j => A (e j)) y≤(Hermitian.one : H d) := by
  rw [←S_extend e he]
  exact S_bounds A hA htr (real_extend_cube e base y hb hy)

lemma face_eta_one_bound (e : Fin n → Fin N) (he : Function.Injective e)
    (base : Coordinates N) (A : Fin N → H d)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(Hermitian.one : H d))
    (hb : Cube base) (hfixed : ∀ i,lookup e i=none → |base i|=1)
    (y : Coordinates n) (hy : Cube y) :
    eta 384 (fun j => A (e j)) y (Hermitian.one : H d)≤(384:ℝ) • (Hermitian.one : H d) := by
  rw [←eta_extend e he base A hfixed y]
  have hv : (∑ i,sandwich (A i) (Hermitian.one : H d))≤(1:ℝ) • (Hermitian.one : H d) := by simpa using hvar
  simpa only [mul_one] using eta_one_bound (by norm_num : (0:ℝ)≤384) A hv
    (real_extend_cube e base y hb hy)

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_FaceState
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d N : ℕ}

lemma variance_le_one (A : Fin N → H d) {ν : ℚ} (hν1 : ν ≤ 1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ (ν:ℝ) • (Hermitian.one : H d)) :
    (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ (Hermitian.one : H d) := by
  calc
    _ ≤ (ν:ℝ) • (Hermitian.one : H d) := hvar
    _ ≤ (1:ℝ) • (Hermitian.one : H d) := scalar_one_mono (by exact_mod_cast hν1)
    _ = _ := one_smul ℝ _

lemma epsilon_spec [NeZero d] {ν : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) :
    0 < ν/(d:ℚ) ∧ ν/(d:ℚ) ≤ 1 ∧ ν/(d:ℚ)*(d:ℚ) ≤ 1 := by
  have hd : (0:ℚ) < d := by exact_mod_cast NeZero.pos d
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast NeZero.pos d
  refine ⟨div_pos hν hd,(div_le_one hd).mpr (hν1.trans hd1),?_⟩
  simpa only [div_mul_cancel₀ _ hd.ne'] using hν1

lemma activeQuery_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) (y : Fin (activeIndices base).length → ℚ)
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam error : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 ≤ lam)
    (he : 0 < error) (he1 : error ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hy : ∀ j,|y j| ≤ 1) :
    |(faceQuery coords base y ν lam error:ℝ)-activePotential coords base ν lam (pointCast y)| ≤ (error:ℝ) := by
  have hh := faceQuery_correct coords base y hA htr hν hν1 hlam he he1 hvar hb hy
  simp only [activePotential,facePotential,penalty,pointCast,Rat.cast_div,Rat.cast_natCast]
  exact hh

lemma nearby_rational_cube (x y : Fin N → ℚ) {σ r : ℚ} (hr : 0 ≤ r)
    (hx : ∀ i,|x i| ≤ 1-σ) (hy : ‖pointCast y-pointCast x‖ ≤ (r:ℝ)) (hrσ : r ≤ σ) :
    ∀ i,|y i| ≤ 1 := by
  intro i
  have hc := (pi_norm_le_iff_of_nonneg (show (0:ℝ) ≤ r by exact_mod_cast hr)).mp hy i
  change ‖(y i:ℝ)-(x i:ℝ)‖ ≤ (r:ℝ) at hc
  rw [Real.norm_eq_abs] at hc
  have hx' : |(x i:ℝ)| ≤ 1-(σ:ℝ) := by exact_mod_cast hx i
  have hr' : (r:ℝ) ≤ (σ:ℝ) := by exact_mod_cast hrσ
  have htri := abs_sub_le (y i:ℝ) (x i:ℝ) 0
  simp only [sub_zero] at htri
  have hh : |(y i:ℝ)| ≤ 1 := by linarith
  exact_mod_cast hh

end
end CurrentKS.RationalFace

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters2
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Schedule

lemma stencil_error_bounds {n : ℕ} (hn : 0 < n) {a h : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1) :
    0 < a*h^2/(128*n) ∧ a*h^2/(128*n) ≤ 1 := by
  have hn0 : (0:ℚ) < n := by exact_mod_cast hn
  have hn1 : (1:ℚ) ≤ n := by exact_mod_cast hn
  refine ⟨by positivity,(div_le_one (by positivity)).mpr ?_⟩
  have hh2 : h^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg h)
  nlinarith

lemma selection_error_bounds {a s : ℚ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hs : 0 < s) (hs1 : s ≤ 1/4) :
    0 < a*s^2/4 ∧ a*s^2/4 ≤ 1 := by
  refine ⟨by positivity,(div_le_one (by norm_num : (0:ℚ) < 4)).mpr ?_⟩
  have hs2 : s^2 ≤ 1 := by nlinarith
  have hm := mul_le_mul_of_nonneg_right ha1 (sq_nonneg s)
  nlinarith

lemma parameters_valid {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (parameters d n ν lam).Valid n := by
  have hd0 : (0:ℚ) < d := by exact_mod_cast hd
  have hd1 : (1:ℚ) ≤ d := by exact_mod_cast hd
  have hep : 0 < ν/(d:ℚ) := div_pos hν hd0
  have hep1 : ν/(d:ℚ) ≤ 1 := (div_le_one hd0).mpr (hν1.trans hd1)
  have hσ : 0 < lam^2/ν := by positivity
  have ha := threshold_pos n (ν/(d:ℚ)) hlam
  have ha1 := threshold_le_one n (ν/(d:ℚ)) hlam1
  have hM := curveBudget_one_le d n hep hσ lam
  have hMp : 0 < curveBudget d n (ν/(d:ℚ)) (lam^2/ν) lam := lt_of_lt_of_le (by norm_num) hM
  have hs := stepSize_spec ha hMp hσ
  have hh := stencilSize_spec hn ha hMp hσ
  have hρ := meshSize_spec hn ha hMp hs.1
  have he := stencil_error_bounds hn ha ha1 hh.1 hh.2.2.1
  have hg := selection_error_bounds ha ha1 hs.1 hs.2.2.1
  exact ⟨hep,hep1,hσ,ha,ha1,hM,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,
    hh.1,hh.2.1,hh.2.2.1,hh.2.2.2,hρ.1,hρ.2,schedule_radius hn ha hMp hσ,
    he.1,he.2,hg.1,hg.2⟩

end CurrentKS.Schedule

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_FaceStencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalFace
open CurrentKS.RationalSDP CurrentKS.Schedule CurrentKS.Difference CurrentKS.Descent

variable {d N : ℕ}

noncomputable section
open CurrentKS.Hermitian CurrentKS.State CurrentKS.Variational CurrentKS.Scalar
open scoped BigOperators MatrixOrder Matrix.Norms.Frobenius ContDiff

lemma faceStencil_correct [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    let p := parameters d (activeIndices base).length ν lam
    ∀ y,‖pointCast y-pointCast (faceState base)‖ ≤ 2*(p.h:ℝ) →
      |(faceStencil coords base ν lam y:ℝ)-activePotential coords base ν lam (pointCast y)| ≤
        (p.a:ℝ)*(p.h:ℝ)^2/(128*(activeIndices base).length) := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  dsimp only
  intro y hy
  have hyc := nearby_rational_cube (faceState base) y (r:=2*p.h) (σ:=p.σ)
    (by linarith [hp.stencil_pos]) hx (by simpa only [Rat.cast_mul,Rat.cast_ofNat] using hy)
    (by linarith [hp.stencil_strip,hp.strip_pos])
  have hq := activeQuery_correct coords base y hA htr hν hν1 hlam.le
    hp.stencilError_pos hp.stencilError_le hvar hb hyc
  apply hq.trans_eq
  simp only [p,parameters,Rat.cast_div,Rat.cast_mul,Rat.cast_pow,Rat.cast_ofNat,Rat.cast_natCast]

lemma faceCandidates_progress_oai [NeZero d] (coords : Fin N → Fin d × Fin d → ℚ)
    (base : Fin N → ℚ) [NeZero (activeIndices base).length]
    (hA : ∀ i,rationalAtoms coords i∈psdCone d)
    (hA0 : ∀ i,rationalAtoms coords i≠0)
    (hrank : ∀ i,(rationalAtoms coords i : Mat d).rank ≤ 1)
    (htr : ∑ i,Hermitian.realTrace (rationalAtoms coords i)=1)
    {ν lam : ℚ} (hν : 0 < ν) (hν1 : ν ≤ 1) (hlam : 0 < lam) (hlam1 : lam ≤ 1)
    (hvar : (∑ i,sandwich (rationalAtoms coords i) (Hermitian.one : H d)) ≤
      (ν:ℝ) • (Hermitian.one : H d))
    (hb : ∀ i,|base i| ≤ 1) (hx : ∀ i,|faceState base i| ≤ 1-lam^2/ν) :
    let p := parameters d (activeIndices base).length ν lam
    ∃ y∈faceCandidates coords base ν lam,
      activePotential coords base ν lam (pointCast y) ≤
        activePotential coords base ν lam (pointCast (faceState base))-2*(p.a:ℝ)*(p.s:ℝ)^2 := by
  let p := parameters d (activeIndices base).length ν lam
  have hp : p.Valid (activeIndices base).length :=
    parameters_valid (NeZero.pos d) (NeZero.pos _) hν hν1 hlam hlam1
  have hepd : p.ε*(d:ℚ) ≤ 1 := (epsilon_spec (d:=d) hν hν1).2.2
  have hbr : Cube (fun i => (base i:ℝ)) := fun i => (show |(base i:ℝ)| ≤ 1 by exact_mod_cast hb i)
  have hxc : Cube (pointCast (faceState base)) := by
    intro i
    change |(base (activeIndex base i):ℝ)| ≤ 1
    exact_mod_cast hb (activeIndex base i)
  have hord := face_order_bounds (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) hA htr hbr _ hxc
  have hη := face_eta_one_bound (activeIndex base) (activeIndex_injective base)
    (fun i => (base i:ℝ)) (rationalAtoms coords) (variance_le_one _ hν1 hvar)
    hbr (real_active_outside_endpoint base hb) _ hxc
  have hregular := activePotential_regular (lam:=lam) coords base hA htr hν hν1 hp.strip_pos hvar hb hx
    (show (0:ℝ) ≤ (p.s+2*p.h:ℚ) by exact_mod_cast (show (0:ℚ) ≤ p.s+2*p.h by linarith [hp.step_pos,hp.stencil_pos]))
    (show ((p.s+2*p.h:ℚ):ℝ) ≤ (p.σ:ℝ)/2 by exact_mod_cast hp.radius)
  have hreg : ∀ y,‖y-pointCast (faceState base)‖ ≤ (p.s:ℝ)+2*(p.h:ℝ) →
      ContDiffAt ℝ 3 (activePotential coords base ν lam) y := by
    intro y hy
    exact (hregular y (by simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using hy)).1
  have hders : ∀ y,‖y-pointCast (faceState base)‖ ≤ (p.s:ℝ)+2*(p.h:ℝ) → ∀ u,‖u‖ ≤ 1 →
      |iteratedDeriv 2 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤ (p.M:ℝ) ∧
      |iteratedDeriv 3 (fun t : ℝ => activePotential coords base ν lam (y+t • u)) 0| ≤ (p.M:ℝ) := by
    intro y hy
    exact (hregular y (by simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_ofNat] using hy)).2
  exact face_candidates_progress (fun j => rationalAtoms coords (activeIndex base j))
    (fixedPart (activeIndex base) (fun i => (base i:ℝ)) (rationalAtoms coords)) (faceState base)
    (faceStencil coords base ν lam) p.ε lam p.σ p.h p.a p.M p.s p.ρ
    hp.epsilon_pos hp.epsilon_le hepd hlam hp.strip_pos hx (fun j => hA _) (fun j => hA0 _)
    (fun j => hrank _) hord.1 hord.2 hη rfl hp.threshold_pos hp.threshold_le hp.bound_one
    hp.step_pos hp.step_le hp.step_strip hp.step_curvature hp.stencil_pos hp.stencil_le
    hp.stencil_curvature hp.mesh_pos hp.mesh_error hreg hders
    (faceStencil_correct coords base hA htr hν hν1 hlam hlam1 hvar hb hx)

end
end CurrentKS.RationalFace

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.RationalFace.faceCandidates_progress_oai := @OAI.CurrentKS.RationalFace.faceCandidates_progress_oai
