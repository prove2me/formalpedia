-- Prove2me | solution 1 for OAI.CurrentKS.State.etaTheta_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:31.271343+00:00
-- url     : https://prove2.me/submissions/60d0c924-6ccd-42a8-809d-0f2c24d9f55d

import Mathlib
import Definitions.Def_OAIQ241TT002

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
private local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r430a28_1 : NormedSpace ℝ (H d) := inferInstance
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
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

lemma etaTheta_positive {c : ℝ} (hc : 0 ≤ c) (A : Fin N → H d) {θ : Coordinates N}
    (hθ : ParameterCube θ) : ∀ Z ∈ psdCone d, etaTheta c A θ Z ∈ psdCone d := by
  intro Z hZ
  rw [etaTheta_apply]
  exact psd_sum _ _ fun i _ => psd_smul (sandwich_psd _ _ hZ) (mul_nonneg hc (hθ i).1)

lemma etaTheta_one_bound {c ν : ℝ} (hc : 0 ≤ c) (A : Fin N → H d)
    (hν : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    {θ : Coordinates N} (hθ : ParameterCube θ) :
    etaTheta c A θ (Hermitian.one : H d) ≤ (c*ν) • (Hermitian.one : H d) := by
  rw [etaTheta_apply,SemigroupAction.mul_smul]
  apply le_trans _ (smul_order hν hc)
  rw [Finset.smul_sum]
  apply Finset.sum_le_sum
  intro i _
  exact scalar_mono_psd (sandwich_psd _ _ one_mem_psdCone)
    (mul_le_of_le_one_right hc (hθ i).2)

lemma etaTheta_minimizer_oai [NeZero d] (A : Fin N → H d)
    (hA : ∀ i,A i ∈ psdCone d) (htr : ∑ i,Hermitian.realTrace (A i) = 1)
    {ν : ℝ} (hν : 0 < ν) (hν₁ : ν ≤ 1)
    (hvar : (∑ i,sandwich (A i) (Hermitian.one : H d)) ≤ ν • (Hermitian.one : H d))
    (x θ : Coordinates N) (hx : Cube x) (hθ : ParameterCube θ) :
    ∃ z ∈ feasible (S A x) (etaTheta 384 A θ), objective (ν/d) z ≤ 100 ∧
      ∀ w ∈ feasible (S A x) (etaTheta 384 A θ), objective (ν/d) z ≤ objective (ν/d) w := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hε : 0 < ν/(d : ℝ) := div_pos hν hd
  have hb := S_bounds A hA htr hx
  have hz := scalar_feasible (S A x) (etaTheta 384 A θ)
    (show -(1 : ℝ) • (Hermitian.one : H d) ≤ S A x by simpa only [neg_one_smul ℝ (Hermitian.one : H d)] using hb.1)
    (show S A x ≤ (1 : ℝ) • (Hermitian.one : H d) by simpa using hb.2)
    (etaTheta_one_bound (by norm_num) A hvar hθ) (show (0 : ℝ)<1/20 by norm_num)
  have hf : objective (ν/(d : ℝ)) (1+(1/20 : ℝ)⁻¹+(384*ν)*(1/20),(1/20 : ℝ) • (Hermitian.one : H d),
      (1/20 : ℝ) • (Hermitian.one : H d)) ≤ 100 := by
    rw [scalar_objective]
    have he : (d : ℝ)*(ν/d) = ν := mul_div_cancel₀ ν (ne_of_gt hd)
    norm_num
    nlinarith
  apply exists_minimizer (S A x) (etaTheta 384 A θ) (etaTheta_positive (by norm_num) A hθ) hε
    (show (0 : ℝ)<100 by norm_num) _ _ _ hz hf
  · exact (show -(100 : ℝ) • (Hermitian.one : H d) ≤ -(Hermitian.one : H d) by
      convert scalar_one_mono (d := d) (show (-100 : ℝ) ≤ -1 by norm_num) using 1 <;> first | rfl | module).trans hb.1
  · exact hb.2.trans (show (Hermitian.one : H d) ≤ (100 : ℝ) • Hermitian.one by
      simpa only [one_smul] using scalar_one_mono (show (1 : ℝ)≤100 by norm_num))

end
end CurrentKS.State

end OAI
end

theorem solution : type_of% @OAI.CurrentKS.State.etaTheta_minimizer_oai := @OAI.CurrentKS.State.etaTheta_minimizer_oai
