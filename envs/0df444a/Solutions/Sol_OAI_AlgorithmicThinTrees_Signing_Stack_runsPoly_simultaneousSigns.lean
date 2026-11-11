-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T23:14:36.442197+00:00
-- url     : https://prove2.me/submissions/8a93b211-4e60-4506-9fe1-cee64f9f8d2f

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT014
import Theorems.Thm_OAI_CurrentKS_Realization_runsPoly_normalizedRun

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
theorem dite_eq_right {α : Sort _} {c : Prop} {_ : Decidable c} {a : c → α} {b : ¬c → α} (h : ¬c) :
    dite c a b = b h := dif_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Space
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.HermitianCoordinates
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.HermitianCoordinates.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH
local instance instNormedSpaceRealSubtypeMatMemSubmoduleH_r30b459_1 : NormedSpace ℝ (H d) := inferInstance
lemma assemble_extract (A : H d) : assemble (extract A)=A := by
  apply Subtype.ext
  ext i j
  have hh := Matrix.IsHermitian.apply A.property i j
  have hd := Matrix.IsHermitian.apply A.property i i
  rcases lt_trichotomy i j with hij | hij | hji
  · apply Complex.ext <;>
      simp [assemble,extract,encode,decode,hij,hij.le,not_le.mpr hij]
  · subst j
    apply Complex.ext
    · simp [assemble,extract,encode,decode]
    · have him := congrArg Complex.im hd
      simp only [Complex.star_def,Complex.conj_im] at him
      simp [assemble,extract,encode,decode]
      linarith
  · apply Complex.ext
    · have hre := congrArg Complex.re hh
      simp only [Complex.star_def,Complex.conj_re] at hre
      simpa [assemble,extract,encode,decode,hji,hji.le,not_le.mpr hji,
        min_eq_right hji.le,max_eq_left hji.le] using hre
    · have him := congrArg Complex.im hh
      simp only [Complex.star_def,Complex.conj_im] at him
      simpa [assemble,extract,encode,decode,hji,hji.le,not_lt.mpr hji.le,
        not_le.mpr hji] using him

end
end CurrentKS.HermitianCoordinates

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

theorem traceSign_mem (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A = -1 ∨ traceSign A = 1 := by
  unfold traceSign
  split_ifs <;> simp

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

theorem eigenvalue_eq_realTrace (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1)
    (i : Fin d) (hi : hA.eigenvalues i ≠ 0) :
    hA.eigenvalues i = realTrace A := by
  classical
  unfold realTrace
  rw [hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  symm
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hj : hA.eigenvalues j = 0 := by
      by_contra hj
      exact hji (nonzero_eigenvalue_unique A hA hrank j i hj hi)
    simp [hj]
  · simp

theorem eigenvalue_eq_zero_or_trace (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) (i : Fin d) :
    hA.eigenvalues i = 0 ∨ hA.eigenvalues i = realTrace A := by
  by_cases hi : hA.eigenvalues i = 0
  · exact Or.inl hi
  · exact Or.inr (eigenvalue_eq_realTrace A hA hrank i hi)

theorem realTrace_eq_zero_iff (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) :
    realTrace A = 0 ↔ A = 0 := by
  constructor
  · intro ht
    apply hA.eigenvalues_eq_zero_iff.mp
    funext i
    rcases eigenvalue_eq_zero_or_trace A hA hrank i with hi | hi
    · exact hi
    · exact hi.trans ht
  · rintro rfl
    simp [realTrace]

theorem traceSign_mul_trace (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A * realTrace A = |realTrace A| := by
  unfold traceSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem traceSign_sq (A : Matrix (Fin d) (Fin d) ℂ) :
    traceSign A * traceSign A = 1 := by
  rcases traceSign_mem A with h | h <;> rw [h] <;> norm_num

theorem traceSign_smul_posSemidef (A : Matrix (Fin d) (Fin d) ℂ)
    (hA : A.IsHermitian) (hrank : A.rank ≤ 1) :
    (traceSign A • A).PosSemidef := by
  change ((traceSign A : ℂ) • A).PosSemidef
  have hd : ((traceSign A : ℂ) • Matrix.diagonal
      ((RCLike.ofReal : ℝ → ℂ) ∘ hA.eigenvalues)).PosSemidef := by
    rw [← Matrix.diagonal_smul]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    change 0 ≤ (traceSign A : ℂ) * (hA.eigenvalues i : ℂ)
    rw [← Complex.ofReal_mul, Complex.zero_le_real]
    rcases eigenvalue_eq_zero_or_trace A hA hrank i with hi | hi
    · simp [hi]
    · rw [hi, traceSign_mul_trace]
      exact abs_nonneg _
  have hp := hd.mul_mul_conjTranspose_same (↑hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)
  have he := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] at he
  simpa only [Matrix.smul_mul, Matrix.mul_smul, ← he] using hp

theorem realTrace_smul (r : ℝ) (A : Matrix (Fin d) (Fin d) ℂ) :
    realTrace (r • A) = r * realTrace A := by
  simp [realTrace, Matrix.trace, Matrix.diag, Finset.mul_sum]

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Normalizer
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

variable {d N : ℕ}

lemma normalizer_nonneg (H : Fin N → Matrix (Fin d) (Fin d) ℂ) : 0 ≤ normalizer H :=
  Finset.sum_nonneg fun index _ => abs_nonneg (realTrace (H index))

lemma normalizedMatrix_posSemidef (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hH : ∀ i, (H i).IsHermitian) (hr : ∀ i, (H i).rank ≤ 1) (i : Fin N) :
    (normalizedMatrix H i).PosSemidef := by
  change ((normalizer H)⁻¹ • (traceSign (H i) • H i)).PosSemidef
  change ((((normalizer H)⁻¹ : ℝ) : ℂ) • (traceSign (H i) • H i)).PosSemidef
  exact (traceSign_smul_posSemidef (H i) (hH i) (hr i)).smul
    (by exact_mod_cast inv_nonneg.mpr (normalizer_nonneg H))

lemma normalizedMatrix_rank (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hr : ∀ i, (H i).rank ≤ 1) (i : Fin N) : (normalizedMatrix H i).rank ≤ 1 := by
  simp only [normalizedMatrix,smul_smul]
  change (((normalizer H)⁻¹*traceSign (H i) : ℝ) • H i).rank ≤ 1
  let r : ℝ := (normalizer H)⁻¹*traceSign (H i)
  change (r • H i).rank ≤ 1
  have he : r • H i = (r • (1 : Matrix (Fin d) (Fin d) ℂ))*H i := by
    rw [Matrix.smul_mul,one_mul]
  rw [he]
  exact (Matrix.rank_mul_le_right _ _).trans (hr i)

lemma normalized_trace_sum (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (hD : normalizer H ≠ 0) :
    (∑ i,realTrace (normalizedMatrix H i)) = 1 := by
  simp only [normalizedMatrix,realTrace_smul,traceSign_mul_trace,← Finset.mul_sum]
  exact inv_mul_cancel₀ hD

lemma reconstruct_matrix (H : Fin N → Matrix (Fin d) (Fin d) ℂ) (hD : normalizer H ≠ 0) (i : Fin N) :
    normalizer H • (traceSign (H i) • normalizedMatrix H i) = H i := by
  simp only [normalizedMatrix,smul_smul]
  have hh : normalizer H * (traceSign (H i) * ((normalizer H)⁻¹ * traceSign (H i))) = 1 := by
    calc
      _ = (normalizer H*(normalizer H)⁻¹)*(traceSign (H i)*traceSign (H i)) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hD,traceSign_sq,mul_one]
  rw [hh,one_smul]

lemma normalizedMatrix_eq_zero_iff (H : Fin N → Matrix (Fin d) (Fin d) ℂ)
    (hD : normalizer H ≠ 0) (i : Fin N) : normalizedMatrix H i = 0 ↔ H i = 0 := by
  constructor
  · intro hi
    rw [← reconstruct_matrix H hD i,hi,smul_zero,smul_zero]
  · intro hi
    simp [normalizedMatrix,hi]

end
end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Optimization_Coordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_originalView
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.RationalInput
open scoped BigOperators ComplexOrder
open CurrentKS.Hermitian CurrentKS.HermitianCoordinates

lemma index_injective (x : Input) : Function.Injective (index x) :=
  ((List.nodup_finRange x.N).filter _).injective_get

lemma index_range (x : Input) (i : Fin x.N) : (∃ j,index x j=i) ↔ trace x i ≠ 0 := by
  change (∃ j,(indices x).get j=i) ↔ _
  rw [← List.mem_iff_get]
  simp [indices]

lemma index_trace_ne (x : Input) (j : Fin (indices x).length) : trace x (index x j) ≠ 0 :=
  (index_range x _).mp ⟨j,rfl⟩

noncomputable section

lemma trace_cast (x : Input) (i : Fin x.N) : (trace x i : ℝ)=CurrentKS.realTrace (x.matrix i) := by
  simp [trace,CurrentKS.realTrace,Matrix.trace,Matrix.diag,Input.matrix,toComplex]

lemma orientation_cast (x : Input) (i : Fin x.N) : (orientation x i : ℝ)=traceSign (x.matrix i) := by
  have hh : 0 ≤ trace x i ↔ (0:ℝ) ≤ CurrentKS.realTrace (x.matrix i) := by
    rw [←trace_cast];exact_mod_cast Iff.rfl
  simp only [orientation,traceSign,hh]
  split_ifs <;> norm_num

lemma scale_cast (x : Input) : (scale x : ℝ)=normalizer x.matrix := by
  simp [scale,normalizer,←trace_cast]

lemma coordinates_cast (x : Input) (hx : Admissible x) (i : Fin x.N) :
    (fun p => (coordinates x i p:ℝ))=HermitianCoordinates.encode ⟨x.matrix i,(hx i).1⟩ := by
  funext p
  simp only [coordinates,HermitianCoordinates.encode,Input.matrix,Matrix.map_apply,toComplex]
  split_ifs <;> rfl

lemma decode_coordinates (x : Input) (hx : Admissible x) (i : Fin x.N) :
    decode (fun p => (coordinates x i p:ℝ))=x.matrix i := by
  rw [coordinates_cast x hx i]
  exact congrArg Subtype.val (assemble_extract (⟨x.matrix i,(hx i).1⟩ : H x.d))

lemma trace_zero_iff (x : Input) (hx : Admissible x) (i : Fin x.N) :
    trace x i=0 ↔ x.matrix i=0 := by
  rw [← realTrace_eq_zero_iff (x.matrix i) (hx i).1 (hx i).2,←trace_cast]
  exact_mod_cast Iff.rfl

lemma scale_pos (x : Input) (hne : (indices x).length ≠ 0) : 0 < scale x := by
  have hl : 0 < (indices x).length := Nat.pos_of_ne_zero hne
  let j : Fin (indices x).length := ⟨0,hl⟩
  exact Finset.sum_pos' (fun i _ => abs_nonneg _) ⟨index x j,Finset.mem_univ _,
    abs_pos.mpr (index_trace_ne x j)⟩

lemma dimension_ne (x : Input) (hx : Admissible x) (hne : (indices x).length ≠ 0) : x.d ≠ 0 := by
  intro hd
  let i := index x ⟨0,Nat.pos_of_ne_zero hne⟩
  have hz : x.matrix i=0 := by
    ext j k
    have hj := j.isLt
    omega
  exact index_trace_ne x _ ((trace_zero_iff x hx i).mpr hz)

lemma decode_normalizedCoordinates (x : Input) (hx : Admissible x) (j : Fin (indices x).length) :
    decode (fun p => (normalizedCoordinates x j p:ℝ))=normalizedMatrix x.matrix (index x j) := by
  have he : (fun p => (normalizedCoordinates x j p:ℝ))=
      (scale x:ℝ)⁻¹ • ((orientation x (index x j):ℝ) • (fun p => (coordinates x (index x j) p:ℝ))) := by
    funext p
    simp [normalizedCoordinates]
  rw [he,decode_smul,decode_smul,decode_coordinates x hx,scale_cast,orientation_cast]
  rfl

lemma normalized_input_properties (x : Input) (hx : Admissible x)
    (hne : (indices x).length ≠ 0) :
    let A := fun j => assemble (WithLp.toLp 2 fun p => (normalizedCoordinates x j p:ℝ))
    (∀ j,A j∈psdCone x.d) ∧ (∀ j,A j≠0) ∧
    (∀ j,(A j:Mat x.d).rank ≤ 1) ∧ (∑ j,Hermitian.realTrace (A j))=1 := by
  let A := fun j => assemble (WithLp.toLp 2 fun p => (normalizedCoordinates x j p:ℝ))
  have hA (j) : (A j:Mat x.d)=normalizedMatrix x.matrix (index x j) :=
    decode_normalizedCoordinates x hx j
  have hD : normalizer x.matrix ≠ 0 := by
    rw [←scale_cast]
    exact_mod_cast (scale_pos x hne).ne'
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    change (A j:Mat x.d).PosSemidef
    rw [hA]
    exact normalizedMatrix_posSemidef x.matrix (fun i => (hx i).1) (fun i => (hx i).2) _
  · intro j hj
    change A j=0 at hj
    have hz : normalizedMatrix x.matrix (index x j)=0 := by rw [←hA j,hj];rfl
    exact index_trace_ne x j ((trace_zero_iff x hx _).mpr
      ((normalizedMatrix_eq_zero_iff x.matrix hD _).mp hz))
  · intro j
    rw [hA]
    exact normalizedMatrix_rank x.matrix (fun i => (hx i).2) _
  · change (∑ j,Hermitian.realTrace (A j))=1
    have he : (∑ j,CurrentKS.realTrace (normalizedMatrix x.matrix (index x j)))=
        ∑ i,CurrentKS.realTrace (normalizedMatrix x.matrix i) := by
      apply Fintype.sum_of_injective (index x) (index_injective x)
      · intro i hi
        have hz : trace x i=0 := by
          by_contra hz
          exact hi ((index_range x i).mpr hz)
        have hm := (trace_zero_iff x hx i).mp hz
        rw [(normalizedMatrix_eq_zero_iff x.matrix hD i).mpr hm]
        simp [CurrentKS.realTrace]
      · intro j;rfl
    have ht := normalized_trace_sum x.matrix hD
    rw [←he] at ht
    convert ht using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro j _
    change CurrentKS.realTrace (A j:Mat x.d)=_
    rw [hA]

end
end CurrentKS.RationalInput

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_BitSupport
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.RationalBits

lemma Parts.mul {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c) (q*r) :=
  KS.W30.mul_parts_le_two_pow q r b c hq.1 hq.2 hr.1 hr.2
lemma Parts.inv {b:ℕ} {q:ℚ} (hq:Parts b q) : Parts b q⁻¹ :=
  KS.W30.inv_parts_le_two_pow q b hq.1 hq.2
lemma Parts.div {b c:ℕ} {q r:ℚ} (hq:Parts b q) (hr:Parts c r) : Parts (b+c) (q/r) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

end CurrentKS.RationalBits

namespace CurrentKS
open scoped BigOperators
open CurrentKS.RationalBits

lemma payload_length (n : ℕ) : (Computability.encodeNat n).length=n.size := by
  have hp (p : PosNum) : (Computability.encodePosNum p).length=p.natSize := by
    induction p <;> simp_all [Computability.encodePosNum,PosNum.natSize]
  have hn (p : Num) : (Computability.encodeNum p).length=p.natSize := by
    cases p with
    | zero => rfl
    | pos p => exact hp p
  unfold Computability.encodeNat
  rw [hn,Num.natSize_to_nat,Num.to_of_nat]

end CurrentKS

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_NaturalPolynomial
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W23

namespace NaturalPolynomial

theorem eval_mono (p : NaturalPolynomial) : Monotone p.eval := by
  intro x y hxy
  induction p with
  | constant c => exact le_rfl
  | «variable» => exact hxy
  | add p q hp hq => exact Nat.add_le_add hp hq
  | mul p q hp hq => exact Nat.mul_le_mul hp hq
  | power p k hp => exact Nat.pow_le_pow_left hp k

end NaturalPolynomial
end KS.W23

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_RoutineLength
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_off_port _root_.OAI.KS.W01.FixedStack.liftPortsInstruction_on_port _root_.OAI.KS.W01.FixedStack.liftPorts_project_init _root_.OAI.KS.W01.SignedRationalSerializer.inputPort _root_.OAI.KS.W01.SignedRationalSerializer.outputPort _root_.OAI.KS.W01.SignedRationalSerializer.stackCount _root_.OAI.KS.W03.MultiplicationInitialize.input_port _root_.OAI.KS.W03.MultiplicationMachine.input_port _root_.OAI.KS.W03.MultiplicationMachine.output_port _root_.OAI.KS.W03.MultiplicationMachine.stack_count _root_.OAI.KS.W03.MultiplicationMachine.state_count _root_.OAI.KS.W03.MultiplicationNormalize.output_port _root_.OAI.KS.W04.BinaryStackMoves.oneConfig_original _root_.OAI.KS.W04.BinaryStackMoves.twoConfig_original _root_.OAI.KS.W04.CleanRationalCompare.cleaned_output _root_.OAI.KS.W04.ReusableArrayLookup.program_input _root_.OAI.KS.W04.ReusableArrayLookup.program_output _root_.OAI.KS.W06.RationalCompare.machine_inputStack _root_.OAI.KS.W06.RationalCompare.machine_outputStack _root_.OAI.KS.W06.RationalCompare.machine_stackCount _root_.OAI.KS.W06.RationalSignClassifier.program_output _root_.OAI.KS.W11.FramedArray.skipProgram_toMachine _root_.OAI.KS.W12.FixedDot.machine_inputStack _root_.OAI.KS.W12.FixedDot.machine_outputStack _root_.OAI.KS.W12.FixedDot.machine_stackCount _root_.OAI.KS.W15.RationalMultiply.machine_inputStack _root_.OAI.KS.W15.RationalMultiply.machine_outputStack _root_.OAI.KS.W15.RationalMultiply.machine_stackCount _root_.OAI.KS.W19.FixedRun.pack_on_port _root_.OAI.KS.W29.FixedBranch.branch_initial _root_.OAI.KS.W29.FixedBranch.branch_states _root_.OAI.KS.W29.FixedBranch.branch_toMachine _root_.OAI.KS.W29.FixedBranch.dispatch_left _root_.OAI.KS.W29.FixedBranch.dispatch_right _root_.OAI.KS.W29.FixedBranch.dispatch_start _root_.OAI.KS.W29.FixedSequential.liftPorts_input _root_.OAI.KS.W29.FixedSequential.liftPorts_output _root_.OAI.KS.W29.FixedSequential.liftPorts_toMachine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.RoutineLength
open KS.W01.FixedStack KS.W29.FixedSequential KS.W03.MachineCombinators

lemma action_length (a : KS.W29.StackAction) (w : List Bool) :
    (a.apply w).length≤w.length+1 := by
  cases a <;> simp [KS.W29.StackAction.apply]; omega

lemma step_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (b : Bool)
    (j : Fin M.stackCount) : ((M.step s b).«stacks» j).length ≤ (s.«stacks» j).length+1 := by
  rcases s with ⟨control,tapes⟩
  cases control with
  | none => simp [KS.W01.FixedStack.Machine.step]
  | some c => exact action_length _ _

lemma run_length (M : KS.W01.FixedStack.Machine) (s : KS.W01.FixedStack.Config M.stackCount M.states) (bits : List Bool)
    (j : Fin M.stackCount) : ((M.run s bits).«stacks» j).length ≤ (s.«stacks» j).length+bits.length := by
  induction bits generalizing s with
  | nil => simp [KS.W01.FixedStack.Machine.run]
  | cons b bs ih =>
    have h := ih (M.step s b)
    have hs := step_length M s b j
    simp only [KS.W01.FixedStack.Machine.run,List.length_cons]
    omega

lemma output_length {k : ℕ} {P : Program k} {before after : Fin k → List Bool} {ticks : ℕ}
    (h : RunSpec P before after ticks) (j : Fin k) :
    (after j).length≤(before j).length+ticks := by
  have hr := run_length P.toMachine ⟨some P.initial,before⟩ (List.replicate ticks false) j
  rw [h _ (List.length_replicate ..)] at hr
  simpa using hr

end CurrentKS.RoutineLength

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoutine
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

variable {α β γ δ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word} {ed : δ → Word}
  {f : α → β} {g : β → γ}

lemma Realizes.output_length (r : Realizes ea eb f) (x : α) :
    (eb (f x)).length≤(ea x).length+r.cost x := by
  have h := RoutineLength.output_length (r.routine.spec x) 0
  simpa only [io_zero] using h

lemma prodCode_length (p : α×β) : (prodCode ea eb p).length=2*(ea p.1).length+1+(eb p.2).length := by
  simp only [prodCode,PairRoutine.pair,List.length_append,KS.W01.length_frame]
lemma le_prodCode_left (p : α×β) : (ea p.1).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega
lemma le_prodCode_right (p : α×β) : (eb p.2).length≤(prodCode ea eb p).length := by rw [prodCode_length];omega

instance poly_first (ea : α → Word) (eb : β → Word) : PolyTime (first ea eb) := by
  refine ⟨⟨6*X+5,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  have h2 := le_prodCode_right (ea:=ea) (eb:=eb) p
  change 5*(ea p.1).length+(eb p.2).length+5≤6*(prodCode ea eb p).length+5
  omega
instance poly_second (ea : α → Word) (eb : β → Word) : PolyTime (second ea eb) := by
  refine ⟨⟨4*X+3,?_⟩⟩
  intro p
  have h1 := le_prodCode_left (ea:=ea) (eb:=eb) p
  change 4*(ea p.1).length+3≤4*(prodCode ea eb p).length+3
  omega
instance poly_then (r : Realizes ea eb f) (s : Realizes eb ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.then s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q.comp (X+p),?_⟩⟩
  intro x
  have hl := r.output_length x
  have hs := (hq (f x)).trans (q.eval_mono (hl.trans (Nat.add_le_add_left (hp x) _)))
  have hh := Nat.add_le_add (hp x) hs
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_comp,NaturalPolynomial.eval_variable]
  exact hh
instance poly_both {g : α → γ} (r : Realizes ea eb f) (s : Realizes ea ec g) [PolyTime r] [PolyTime s] :
    PolyTime (r.both s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨16*X+13*p+q+15,?_⟩⟩
  intro x
  have hl := r.output_length x
  have h1 := hp x
  have h2 := hq x
  change PairRoutine.pairingTicks ea (fun x => eb (f x)) r.cost s.cost x≤
    16*(ea x).length+13*p.eval (ea x).length+q.eval (ea x).length+15
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RationalElimination
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W17

theorem schurTail_isSymm {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm) :
    (schurTail M).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  simp only [schurTail]
  rw [hM.apply i.succ j.succ, hM.apply 0 j.succ, hM.apply 0 i.succ]
  rw [mul_comm (M 0 j.succ) (M 0 i.succ)]

end KS.W17

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β γ : Type*} {L f g : ι → ℕ}

lemma IsPoly.mono (hf : IsPoly L f) (h : ∀i,g i≤f i) : IsPoly L g := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => (h i).trans (hp i)⟩
lemma IsPoly.add (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i+g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p+q,fun i => Nat.add_le_add (hp i) (hq i)⟩
lemma IsPoly.mul (hf : IsPoly L f) (hg : IsPoly L g) : IsPoly L (fun i => f i*g i) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  exact ⟨p*q,fun i => Nat.mul_le_mul (hp i) (hq i)⟩
lemma IsPoly.pow (hf : IsPoly L f) (k : ℕ) : IsPoly L (fun i => (f i)^k) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p^k,fun i => Nat.pow_le_pow_left (hp i) k⟩
lemma isPoly_const (L : ι → ℕ) (c : ℕ) : IsPoly L (fun _ => c) := ⟨.constant c,fun _ => le_rfl⟩
lemma IsPoly.eval (hf : IsPoly L f) (p : NaturalPolynomial) : IsPoly L (fun i => p.eval (f i)) := by
  obtain ⟨q,hq⟩ := hf
  exact ⟨p.comp q,fun i => by simpa only [NaturalPolynomial.eval_comp] using p.eval_mono (hq i)⟩
lemma IsPoly.reindex {κ : Type*} (hf : IsPoly L f) (a : κ → ι) : IsPoly (L ∘ a) (f ∘ a) := by
  obtain ⟨p,hp⟩ := hf
  exact ⟨p,fun i => hp (a i)⟩

variable {ea : α → Word} {eb : β → Word} {ec : γ → Word} {F : α → β} {G : β → γ}

lemma RunsPoly.of_poly (r : Realizes ea eb F) [PolyTime r] (a : ι → α)
    (h : IsPoly L (fun i => (ea (a i)).length)) : RunsPoly L r a := by
  refine ⟨h,?_⟩
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  exact (h.eval p).mono (fun i => hp (a i))
lemma RunsPoly.output {r : Realizes ea eb F} {a : ι → α} (h : RunsPoly L r a) :
    IsPoly L (fun i => (eb (F (a i))).length) := (h.input.add h.cost).mono (fun i => r.output_length (a i))
lemma RunsPoly.then {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s (fun i => F (a i))) : RunsPoly L (r.then s) a :=
  ⟨hr.input,hr.cost.add hs.cost⟩
lemma RunsPoly.then_poly {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    (s : Realizes eb ec G) [PolyTime s] : RunsPoly L (r.then s) a :=
  hr.then (RunsPoly.of_poly s _ hr.output)
lemma RunsPoly.both {G : α → γ} {r : Realizes ea eb F} {s : Realizes ea ec G} {a : ι → α}
    (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.both s) a := by
  refine ⟨hr.input,?_⟩
  have h := (((((isPoly_const L 4).mul hr.input).add ((isPoly_const L 12).mul hr.output)).add hr.cost).add hs.cost).add (isPoly_const L 15)
  apply h.mono
  intro i
  change PairRoutine.pairingTicks ea (fun x => eb (F x)) r.cost s.cost (a i)≤_
  simp only [PairRoutine.pairingTicks,KS.W01.length_frame]
  omega
lemma RunsPoly.congr {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {F' : α → β} (h : ∀x,F x=F' x) : RunsPoly L (r.congr h) a := by
  have he : F=F' := funext h
  subst F'
  exact hr
lemma RunsPoly.changeOutput {r : Realizes ea eb F} {a : ι → α} (hr : RunsPoly L r a)
    {δ : Type*} (ed : δ → Word) (g : α → δ) (h : ∀x,eb (F x)=ed (g x)) :
    RunsPoly L (r.changeOutput ed g h) a := ⟨hr.input,hr.cost⟩
lemma RunsPoly.ite {P : α → Bool} {G : α → β} {b : Realizes ea boolCode P}
    {r : Realizes ea eb F} {s : Realizes ea eb G} {a : ι → α}
    (hb : RunsPoly L b a) (hr : RunsPoly L r a) (hs : RunsPoly L s a) :
    RunsPoly L (b.ite r s) a := by
  unfold Realizes.ite
  have ht := hb.both (RunsPoly.of_poly (identity ea) a hb.input)
  apply ht.then
  refine ⟨ht.output,?_⟩
  apply ((hr.cost.add hs.cost).add (isPoly_const L 6)).mono
  intro i
  change 5+(if P (a i) then r.cost (a i) else s.cost (a i))+1 ≤ r.cost (a i)+s.cost (a i)+6
  split <;> omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialArithmeticFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word} {a : ι → α}

lemma RunsPoly.ratOp (operation : KS.W13.ExpressionMachine.BinaryOp) {input : ι → ℚ × ℚ}
    (hinput : IsPoly L (fun index => (prodCode ratCode ratCode (input index)).length)) :
    RunsPoly L (ratOp operation) input := by
  refine ⟨hinput, ?_⟩
  apply (hinput.eval (5 * NaturalPolynomial.variable +
    6000000 * (NaturalPolynomial.variable + 1) ^ 3 + 6)).mono
  intro index
  have hlength := RoutineLength.output_length
    (KS.W13.ExpressionMachine.binaryArithmetic_spec operation (input index).1 (input index).2 [] []) 10
  have houtput : (ratCode (operation.eval (input index).1 (input index).2)).length ≤
      KS.W13.ExpressionMachine.binaryBudget (input index).1 (input index).2 := by
    simpa [KS.W13.ExpressionMachine.registers] using hlength
  have hpair : (ratCode (input index).1).length + (ratCode (input index).2).length ≤
      (prodCode ratCode ratCode (input index)).length := by
    rw [prodCode_length]
    omega
  have hpower := Nat.pow_le_pow_left (Nat.add_le_add_right hpair 1) 3
  have hleft := le_prodCode_left (ea := ratCode) (eb := ratCode) (input index)
  change ArithmeticRoutine.ticks operation (input index).1 (input index).2 ≤
    5 * (prodCode ratCode ratCode (input index)).length +
      6000000 * ((prodCode ratCode ratCode (input index)).length + 1) ^ 3 + 6
  simp only [ArithmeticRoutine.ticks, ArithmeticRoutine.encode,
    KS.W13.ExpressionMachine.binaryBudget, KS.W01.ratLength] at houtput ⊢
  simp only [ratCode] at *
  omega

variable {f g : α → ℚ} {r : Realizes ea ratCode f} {s : Realizes ea ratCode g}
lemma RunsPoly.mul (hr : RunsPoly L r a) (hs : RunsPoly L s a) : RunsPoly L (r.mul s) a :=
  (hr.both hs).then (RunsPoly.ratOp _ (hr.both hs).output)
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ListRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine

variable {α β γ : Type*}

lemma fold_cons (xs ys : List α) : xs.foldl (fun acc x => x::acc) ys=xs.reverse++ys := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => simp only [List.foldl_cons,ih,List.reverse_cons,List.append_assoc,List.cons_append,List.nil_append]

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLoops
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.KS.W12.RowDot.tailTape_cons _root_.OAI.KS.W13.ExpressionMachine.encodeStack_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word}

lemma len_listCode (ea : α → Word) (xs : List α) :
    (listCode ea xs).length=(xs.map (fun x => 2*(ea x).length+1)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.map_cons,List.sum_cons,ih]
lemma sum_map_bound (xs : List α) (f : α → ℕ) (B : ℕ) (h : ∀ x∈xs,f x≤B) :
    (xs.map f).sum≤xs.length*B := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
lemma listCode_length_bound (xs : List α) (B : ℕ) (h : ∀ x∈xs,(ea x).length≤B) :
    (listCode ea xs).length≤xs.length*(2*B+1) := by
  rw [len_listCode]
  apply sum_map_bound
  intro x hx
  have := h x hx
  omega
lemma list_length_le_code (ea : α → Word) (xs : List α) : xs.length≤(listCode ea xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [listCode_cons,prodCode_length,List.length_cons];omega
lemma mem_length_le_code (xs : List α) {x : α} (hx : x∈xs) :
    (ea x).length≤(listCode ea xs).length := by
  induction xs with
  | nil => simp at hx
  | cons y ys ih =>
      simp only [List.mem_cons] at hx
      rw [listCode_cons,prodCode_length]
      dsimp only
      rcases hx with rfl|hx
      · omega
      · have := ih hx;omega
lemma listCode_reverse_length (ea : α → Word) (xs : List α) :
    (listCode ea xs.reverse).length=(listCode ea xs).length := by
  simp only [len_listCode,List.map_reverse,List.sum_reverse]

instance poly_map {f : α → β} (r : Realizes ea eb f) [PolyTime r] : PolyTime r.map := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let Q := X+p
  refine ⟨⟨2*X+X*(3*X+p+6*Q+8)+X*(2*Q+1)+4,?_⟩⟩
  intro xs
  let L := (listCode ea xs).length
  have hn : xs.length≤L := list_length_le_code ea xs
  have ho : ∀ x∈xs,(eb (f x)).length≤L+p.eval L := by
    intro x hx
    have hl : (ea x).length≤L := mem_length_le_code xs hx
    exact (r.output_length x).trans (Nat.add_le_add hl ((hp x).trans (p.eval_mono hl)))
  have hs := sum_map_bound xs (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*L+p.eval L+6*(L+p.eval L)+8) (by
      intro x hx
      have hl : (ea x).length≤L := mem_length_le_code xs hx
      have hc := (hp x).trans (p.eval_mono hl)
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound (ea:=fun x => eb (f x)) xs (L+p.eval L) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost xs≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*L+2+((xs.map _).sum+1)+(listCode (fun x => eb (f x)) xs).length+1≤_
  change _≤2*L+L*(3*L+p.eval L+6*(L+p.eval L)+8)+L*(2*(L+p.eval L)+1)+4
  omega

lemma fold_scan_bound (F : α → β → α) (cost : α×β → ℕ) (s : α) (xs : List β) (S E C : ℕ)
    (hs : ∀ ys zs,xs=ys++zs → (ea (ys.foldl F s)).length≤S)
    (he : ∀ x∈xs,(eb x).length≤E)
    (hc : ∀ a x,(ea a).length≤S → (eb x).length≤E → cost (a,x)≤C) :
    FoldRoutine.scanTicks ea eb F cost s xs≤xs.length*(3*E+10*S+C+12)+1 := by
  induction xs generalizing s with
  | nil => simp [FoldRoutine.scanTicks]
  | cons x xs ih =>
      have h0 := hs [] (x::xs) rfl
      have h1 := hs [x] xs rfl
      have hx := he x (by simp)
      have hc0 := hc s x h0 hx
      have ht := ih (F s x) (by
        intro ys zs hz
        have h := hs (x::ys) zs (by simp only [List.cons_append];rw [hz])
        simpa only [List.foldl_cons] using h) (fun y hy => he y (by simp [hy]))
      simp only [FoldRoutine.scanTicks,FoldRoutine.bodyTicks,KS.W01.length_frame,List.length_cons,Nat.add_mul,Nat.one_mul]
      simp only [List.foldl_nil,List.foldl_cons] at h0 h1
      omega

instance poly_fold {f : α×β → α} (r : Realizes (prodCode ea eb) ea f) [PolyTime r] [FoldSize r] :
    PolyTime r.fold := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := FoldSize.bound (r:=r)
  refine ⟨⟨5*q+2*X+X*(3*X+10*q+p.comp (2*q+1+X)+12)+7,?_⟩⟩
  intro u
  let L := (prodCode ea (listCode eb) u).length
  let S := q.eval L
  have he : (listCode eb u.2).length≤L := le_prodCode_right u
  have hn := (list_length_le_code eb u.2).trans he
  have hs := hq u.1 u.2
  have h0 : (ea u.1).length≤S := hs [] u.2 rfl
  have hN : (ea (u.2.foldl (fun a b => f (a,b)) u.1)).length≤S := hs u.2 [] (by simp)
  have hc : ∀ a x,(ea a).length≤S → (eb x).length≤L → r.cost (a,x)≤p.eval (2*S+1+L) := by
    intro a x ha hx
    apply (hp (a,x)).trans (p.eval_mono ?_)
    rw [prodCode_length]
    dsimp only
    omega
  have hscan := fold_scan_bound (ea:=ea) (eb:=eb) (fun a b => f (a,b)) r.cost u.1 u.2 S L
    (p.eval (2*S+1+L)) hs (fun x hx => (mem_length_le_code u.2 hx).trans he) hc
  have hscan' := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change FoldRoutine.ticks ea eb (fun a b => f (a,b)) r.cost u.1 u.2≤_
  simp only [FoldRoutine.ticks]
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change _≤5*S+2*L+L*(3*L+10*S+p.eval (2*S+1+L)+12)+7
  change _≤_ at hscan'
  change (FramedMapRoutine.tape eb u.2).length≤L at he
  omega

lemma iterate_ticks_bound {f : α → α} (r : Realizes ea ea f) (x : α) (n C : ℕ)
    (h : ∀ i,i<n → r.cost (f^[i] x)≤C) :
    IterateRoutine.loopTicks r.cost f n x≤n*(C+2)+1 := by
  induction n generalizing x with
  | zero => simp [IterateRoutine.loopTicks]
  | succ n ih =>
      have h0 := h 0 (by omega)
      have ht := ih (f x) (by
        intro i hi
        simpa only [←Function.iterate_succ_apply] using h (i+1) (by omega))
      simp only [Function.iterate_zero, id_eq] at h0
      simp only [IterateRoutine.loopTicks,Nat.add_mul,Nat.one_mul]
      omega
instance poly_iterate {f : α → α} (r : Realizes ea ea f) [PolyTime r] [IterateSize r] :
    PolyTime r.iterate := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := IterateSize.bound (r:=r)
  refine ⟨⟨3*X+X*(p.comp q+2)+3,?_⟩⟩
  intro u
  let L := (prodCode natCode ea u).length
  have hi : (ea u.2).length+u.1≤L := by simp only [L,prodCode_length,natCode,List.length_replicate];omega
  have hn : u.1≤L := by omega
  have ht := iterate_ticks_bound r u.2 u.1 (p.eval (q.eval L)) (by
    intro i hi'
    exact (hp _).trans (p.eval_mono ((hq u.2 i).trans (q.eval_mono (by omega)))))
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
  change 3*u.1+2+IterateRoutine.loopTicks r.cost f u.1 u.2≤3*L+L*(p.eval (q.eval L)+2)+3
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Realization_ArrayRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α γ : Type*}

lemma fold_length (xs : List α) (n : ℕ) : xs.foldl (fun k _ => k+1) n=n+xs.length := by
  induction xs generalizing n with
  | nil => simp
  | cons x xs ih => simp [ih,Nat.add_comm,Nat.add_left_comm]

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialLists
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma prefix_code_length (ea : α → Word) (xs ys zs : List α) (h : xs=ys++zs) :
    (listCode ea ys).length≤(listCode ea xs).length := by
  rw [h,listCode_append,List.length_append];omega
lemma prefix_length (xs ys zs : List α) (h : xs=ys++zs) : ys.length≤xs.length := by
  rw [h,List.length_append];omega

instance poly_appendList (ea : α → Word) : PolyTime (appendList ea) := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  exact Nat.add_le_add_right (Nat.mul_le_mul_left 5 (le_prodCode_left p)) 4
instance poly_reverseBody (ea : α → Word) : PolyTime (reverseBody ea) := by
  unfold reverseBody;infer_instance
instance size_reverseBody (ea : α → Word) : FoldSize (reverseBody ea) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_cons,listCode_append,List.length_append,listCode_reverse_length]
  have hp := prefix_code_length ea xs ys zs h
  change _≤(prodCode (listCode ea) (listCode ea) (s,xs)).length
  rw [prodCode_length]
  try dsimp only
  omega
instance poly_reverseList (ea : α → Word) : PolyTime (reverseList ea) := by
  unfold reverseList;infer_instance

instance poly_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime (mapCtxBody ec ea eb r) := by
  dsimp only [mapCtxBody]
  apply poly_both
instance size_mapCtxBody {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    FoldSize (mapCtxBody ec ea eb r) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  let U := 3*X+1+p.comp (3*X+1)
  refine ⟨⟨3*X+1+X*(2*U+1),?_⟩⟩
  intro s xs ys zs h
  rw [fold_mapCtx]
  let L := (prodCode (prodCode ec (listCode eb)) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left s).trans (le_prodCode_left (s,xs))
  have ha : (listCode eb s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have he : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have hn : ys.length≤L := (list_length_le_code ea ys).trans he
  have ho : ∀ x∈ys,(eb (f (s.1,x))).length≤3*L+1+p.eval (3*L+1) := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he' := (mem_length_le_code ys hx).trans he
      simp only [prodCode_length]
      try dsimp only
      omega
    exact (r.output_length (s.1,x)).trans (Nat.add_le_add hl ((hp _).trans (p.eval_mono hl)))
  have hm := listCode_length_bound (ea:=fun x => eb (f (s.1,x))) ys (3*L+1+p.eval (3*L+1)) ho
  have hm' := hm.trans (Nat.mul_le_mul_right _ hn)
  have heq : listCode eb (ys.map (fun x => f (s.1,x)))=listCode (fun x => eb (f (s.1,x))) ys := by
    simp only [listCode,FramedMapRoutine.tape,List.flatMap_map]
  rw [prodCode_length]
  dsimp only
  rw [listCode_append,List.length_append,listCode_reverse_length,heq]
  change 2*(ec s.1).length+1+((listCode (fun x => eb (f (s.1,x))) ys).length+(listCode eb s.2).length)≤_
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp,U]
  change _≤3*L+1+L*(2*(3*L+1+p.eval (3*L+1))+1)
  omega
instance poly_mapCtx {f : γ×α → β} (r : Realizes (prodCode ec ea) eb f) [PolyTime r] :
    PolyTime r.mapCtx := by
  unfold Realizes.mapCtx
  infer_instance

instance poly_natAdd : PolyTime natAdd := by
  refine ⟨⟨5*X+4,?_⟩⟩
  intro p
  have h := le_prodCode_left (ea:=natCode) (eb:=natCode) p
  simp only [natCode,List.length_replicate] at h
  change 5*p.1+4≤5*(prodCode natCode natCode p).length+4
  omega

instance poly_rangeStep : PolyTime rangeStepRealizes := by dsimp only [rangeStepRealizes];apply poly_both
lemma range_iterate_size (s : ℕ×List ℕ) (k : ℕ) :
    (rangeStep^[k] s).1=s.1+k ∧
    (listCode natCode (rangeStep^[k] s).2).length≤(listCode natCode s.2).length+k*(2*(s.1+k)+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      change (rangeStep^[k] s).1+1=s.1+(k+1) ∧ _
      constructor
      · omega
      · change (listCode natCode ((rangeStep^[k] s).1::(rangeStep^[k] s).2)).length≤_
        rw [listCode_cons,prodCode_length]
        simp only [natCode,List.length_replicate]
        try dsimp only
        nlinarith [ih.2]
instance size_rangeStep : IterateSize rangeStepRealizes := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s k
  have h := range_iterate_size s k
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*(rangeStep^[k] s).1+1+(listCode natCode (rangeStep^[k] s).2).length≤10*(2*s.1+1+(listCode natCode s.2).length+k+1)^2
  rw [h.1]
  nlinarith [h.2]
instance poly_range : PolyTime range := by unfold range;infer_instance

instance poly_lengthBody (ea : α → Word) : PolyTime ((first natCode ea).then natSucc) := by infer_instance
instance size_lengthBody (ea : α → Word) : FoldSize ((first natCode ea).then natSucc) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  change (natCode (ys.foldl (fun k _ => k+1) s)).length≤_
  rw [fold_length]
  have hs := le_prodCode_left (ea:=natCode) (eb:=listCode ea) (s,xs)
  have hn := ((prefix_length xs ys zs h).trans (list_length_le_code ea xs)).trans (le_prodCode_right (ea:=natCode) (s,xs))
  simp only [natCode,List.length_replicate] at hs ⊢
  change s+ys.length≤2*(prodCode natCode (listCode ea) (s,xs)).length
  omega
instance poly_lengthList (ea : α → Word) : PolyTime (lengthList ea) := by unfold lengthList;infer_instance
instance poly_tabulate {f : γ×ℕ → α} (r : Realizes (prodCode ec natCode) ea f) [PolyTime r] :
    PolyTime r.tabulate := by unfold Realizes.tabulate;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialScalar
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
attribute [-simp] _root_.OAI.CurrentKS.Realization.listCode_cons _root_.OAI.KS.W01.sumBudget_cons _root_.OAI.KS.W12.RowDot.tailTape_cons
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable

instance poly_ratOp (op : KS.W13.ExpressionMachine.BinaryOp) : PolyTime (ratOp op) := by
  refine ⟨⟨5*X+6000000*(X+1)^3+6,?_⟩⟩
  intro p
  have hl := RoutineLength.output_length (KS.W13.ExpressionMachine.binaryArithmetic_spec op p.1 p.2 [] []) 10
  have ht : (ratCode (op.eval p.1 p.2)).length≤KS.W13.ExpressionMachine.binaryBudget p.1 p.2 := by simpa [KS.W13.ExpressionMachine.registers] using hl
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 3
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change ArithmeticRoutine.ticks op p.1 p.2≤5*(prodCode ratCode ratCode p).length+6000000*((prodCode ratCode ratCode p).length+1)^3+6
  simp only [ArithmeticRoutine.ticks,ArithmeticRoutine.encode,KS.W13.ExpressionMachine.binaryBudget,KS.W01.ratLength] at ht ⊢
  simp only [ratCode] at *
  omega

instance poly_ratLE : PolyTime ratLE := by
  refine ⟨⟨5*X+2048*(X+1)^2+8,?_⟩⟩
  intro p
  have hi : (ratCode p.1).length+(ratCode p.2).length ≤ (prodCode ratCode ratCode p).length := by rw [prodCode_length];omega
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right hi 1) 2
  have ha := le_prodCode_left (ea:=ratCode) (eb:=ratCode) p
  change CompareRoutine.ticks p.1 p.2≤5*(prodCode ratCode ratCode p).length+2048*((prodCode ratCode ratCode p).length+1)^2+8
  simp only [CompareRoutine.ticks,CompareRoutine.encode,KS.W29.polynomialFuel,List.length_append]
  simp only [ratCode] at *
  omega

instance poly_ratFloor : PolyTime ratFloor := by
  refine ⟨⟨192*(X+1)^2+2,?_⟩⟩
  intro q
  have hl := RoutineLength.output_length (KS.W20.FloorRationalMachine.polynomial_spec q) 5
  have ht : (ratCode (⌊q⌋ : ℚ)).length≤64*((ratCode q).length+1)^2 := by
    simpa [KS.W20.FloorRationalMachine.state,KS.W19.SignedFloorMachine.«stacks»,KS.W29.polynomialFuel] using hl
  change FloorCleanRoutine.ticks q≤192*((ratCode q).length+1)^2+2
  simp only [FloorCleanRoutine.ticks,KS.W29.polynomialFuel,FloorCleanRoutine.encode]
  simp only [ratCode] at *
  omega

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_conditional {f g : α → β} (r : Realizes ea eb f) (s : Realizes ea eb g)
    [PolyTime r] [PolyTime s] : PolyTime (conditional r s) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=r)
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=s)
  refine ⟨⟨p+q+6,?_⟩⟩
  intro x
  have hr := (hp x.2).trans (p.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  have hs := (hq x.2).trans (q.eval_mono (le_prodCode_right (ea:=boolCode) (eb:=ea) x))
  change 5+(if x.1 then r.cost x.2 else s.cost x.2)+1≤p.eval _+q.eval _+6
  split <;> omega
instance poly_ite {p : α → Bool} {f g : α → β} (b : Realizes ea boolCode p)
    (r : Realizes ea eb f) (s : Realizes ea eb g) [PolyTime b] [PolyTime r] [PolyTime s] : PolyTime (b.ite r s) := by unfold Realizes.ite; exact poly_then (b.both (identity ea)) (conditional r s)
instance poly_add {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.add s) := by unfold Realizes.add; exact poly_then (r.both s) (ratOp .add)
instance poly_sub {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.sub s) := by unfold Realizes.sub; exact poly_then (r.both s) (ratOp .sub)
instance poly_mul {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.mul s) := by unfold Realizes.mul; exact poly_then (r.both s) (ratOp .mul)
instance poly_div {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.div s) := by unfold Realizes.div; exact poly_then (r.both s) (ratOp .div)
instance poly_le {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.le s) := by unfold Realizes.le;infer_instance
instance poly_neg {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.neg := by unfold Realizes.neg;infer_instance
instance poly_abs {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.abs := by unfold Realizes.abs;infer_instance
instance poly_roundScalar : PolyTime roundScalar := by unfold roundScalar;infer_instance
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialArrays
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma fold_add_eq (xs : List ℚ) (q : ℚ) : xs.foldl (fun a b => a+b) q=q+xs.sum := by
  induction xs generalizing q with
  | nil => simp
  | cons x xs ih => simp [ih,add_assoc]
lemma rat_sum_lengths_le (xs : List ℚ) :
    (xs.map KS.W01.ratLength).sum+xs.length≤(listCode ratCode xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,listCode_cons,prodCode_length]
      change KS.W01.ratLength x+_+_≤2*KS.W01.ratLength x+1+_
      omega
instance size_ratAdd : FoldSize (ratOp .add) := by
  refine ⟨⟨40*X+40,?_⟩⟩
  intro s xs ys zs h
  change (ratCode (ys.foldl (fun a b => a+b) s)).length≤_
  rw [fold_add_eq]
  have h1 := KS.W01.ratLength_sum_le ys
  have h2 := KS.W01.ratLength_add_le s ys.sum
  have hs := le_prodCode_left (ea:=ratCode) (eb:=listCode ratCode) (s,xs)
  have hy := (rat_sum_lengths_le ys).trans ((prefix_code_length ratCode xs ys zs h).trans
    (le_prodCode_right (ea:=ratCode) (s,xs)))
  change KS.W01.ratLength s≤_ at hs
  change KS.W01.ratLength (s+ys.sum)≤40*(prodCode ratCode (listCode ratCode) (s,xs)).length+40
  omega
instance poly_sumRationals : PolyTime sumRationals := by
  unfold sumRationals
  apply poly_congr
instance poly_l1Rationals : PolyTime l1Rationals := by unfold l1Rationals;apply poly_then

instance poly_lookupStep (ea : α → Word) : PolyTime (lookupStepRealizes ea) := by
  dsimp only [lookupStepRealizes]
  apply poly_congr
lemma lookup_fold_size (ea : α → Word) (s : ℕ×α) (xs : List α) (K B : ℕ)
    (hk : s.1≤K) (ha : (ea s.2).length≤B) (hx : ∀x∈xs,(ea x).length≤B) :
    (xs.foldl (fun s x => lookupStep (s,x)) s).1≤K ∧
    (ea (xs.foldl (fun s x => lookupStep (s,x)) s).2).length≤B := by
  induction xs generalizing s with
  | nil => exact ⟨hk,ha⟩
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      · dsimp only [lookupStep]
        split_ifs <;> (try dsimp only) <;> omega
      · dsimp only [lookupStep]
        split_ifs <;> try dsimp only
        · exact ha
        · exact hx x (by simp)
        · exact ha
      · intro y hy;exact hx y (by simp [hy])
instance size_lookupStep (ea : α → Word) : FoldSize (lookupStepRealizes ea) := by
  refine ⟨⟨3*X+1,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode natCode ea) (listCode ea) (s,xs)).length
  have hk : s.1≤L := by
    have hl := (le_prodCode_left (ea:=natCode) (eb:=ea) s).trans (le_prodCode_left (eb:=listCode ea) (s,xs))
    simpa only [natCode,List.length_replicate] using hl
  have ha : (ea s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have ht := lookup_fold_size ea s ys L L hk ha (fun x hx => (mem_length_le_code ys hx).trans hy)
  change (prodCode natCode ea _).length≤3*L+1
  rw [prodCode_length]
  simp only [natCode,List.length_replicate]
  omega
instance poly_getD (ea : α → Word) (a : α) : PolyTime (getD ea a) := by unfold getD;infer_instance

instance poly_zipWith {f : α×β → γ} (r : Realizes (prodCode ea eb) ec f) (a : α) (b : β)
    [PolyTime r] : PolyTime (r.zipWith a b) := by unfold Realizes.zipWith;apply poly_then
instance poly_vectorAdd : PolyTime vectorAdd := by unfold vectorAdd;infer_instance
instance poly_vectorScaleBody : PolyTime vectorScaleBody := by unfold vectorScaleBody;exact poly_ratOp .mul
instance poly_vectorScale : PolyTime vectorScale := by unfold vectorScale;infer_instance
instance poly_matrixAdd : PolyTime matrixAdd := by unfold matrixAdd;infer_instance
instance poly_matrixScale : PolyTime matrixScale := by unfold matrixScale;infer_instance
instance poly_dot : PolyTime dot := by unfold dot;apply poly_then
instance poly_matVec : PolyTime matVec := by unfold matVec;apply poly_then
instance poly_quadratic : PolyTime quadratic := by unfold quadratic;apply poly_then

lemma ratLength_natCast (n : ℕ) : KS.W01.ratLength (n : ℚ)≤4*n+11 := by
  apply (KS.W01.ratLength_le_of_parts (n : ℚ) n n ?_ ?_).trans (by omega)
  · simpa only [Rat.num_natCast,Int.natAbs_natCast] using (Nat.le_of_lt (Nat.lt_two_pow_self (n:=n)))
  · simpa only [Rat.den_natCast] using (Nat.one_le_two_pow (n:=n))
instance size_ratSucc : IterateSize ((identity ratCode).add (constant ratCode ratCode 1)) := by
  refine ⟨⟨20*X+60,?_⟩⟩
  intro q n
  change (ratCode ((fun x : ℚ => x+1)^[n] q)).length≤_
  rw [iterate_ratSucc]
  have h := KS.W01.ratLength_add_le q (n : ℚ)
  have hn := ratLength_natCast n
  change KS.W01.ratLength (q+(n : ℚ))≤20*(KS.W01.ratLength q+n)+60
  omega
instance poly_natToRat : PolyTime natToRat := by unfold natToRat;infer_instance
instance size_natMulStep : IterateSize ((first natCode natCode).both natAdd) := by
  refine ⟨⟨10*(X+1)^2,?_⟩⟩
  intro s n
  change (prodCode natCode natCode ((fun a : ℕ×ℕ => (a.1,a.1+a.2))^[n] s)).length≤_
  rcases s with ⟨k,z⟩
  rw [fold_natAdd]
  simp only [prodCode_length,natCode,List.length_replicate]
  change 2*k+1+(n*k+z)≤10*(2*k+1+z+n+1)^2
  nlinarith
instance poly_natMul : PolyTime natMul := by unfold natMul;infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialBranchFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_fold _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_iterate _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_map _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_ratSucc _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}
lemma isPoly_dite {P : ι → Prop} [DecidablePred P] {f : (i : ι) → P i → ℕ}
    {g : (i : ι) → ¬P i → ℕ}
    (hf : IsPoly (fun i : {i // P i} => L i.val) (fun i => f i.val i.property))
    (hg : IsPoly (fun i : {i // ¬P i} => L i.val) (fun i => g i.val i.property)) :
    IsPoly L (fun i => if h : P i then f i h else g i h) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  refine ⟨p+q,?_⟩
  intro i
  by_cases h : P i
  · simp only [dite_eq_left h]
    exact (hp ⟨i,h⟩).trans (Nat.le_add_right _ _)
  · simp only [dite_eq_right h]
    exact (hq ⟨i,h⟩).trans (Nat.le_add_left _ _)

lemma RunsPoly.ite_on {P : α → Bool} {F G : α → β} {b : Realizes ea boolCode P}
    {r : Realizes ea eb F} {s : Realizes ea eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hc : IsPoly L (fun i => if P (a i) then r.cost (a i) else s.cost (a i))) :
    RunsPoly L (b.ite r s) a := by
  unfold Realizes.ite
  have ht := hb.both (RunsPoly.of_poly (identity ea) a hb.input)
  apply ht.then
  refine ⟨ht.output,?_⟩
  have h := ((isPoly_const L 5).add hc).add (isPoly_const L 1)
  simp only [Nat.add_assoc] at h ⊢
  exact h

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_Pivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

section TrivialStar

variable [StarRing K] [TrivialStar K]

omit [Fintype n] [DecidableEq n] in
theorem pivot_schur_formula {a : K} (ha : a ≠ 0)
    (b : n → K) (D : Matrix n n K) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D := by
  ext i j
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, pivotSchur]
  ring

omit [DecidableEq n] [StarRing K] [TrivialStar K] in
theorem pivot_lift_cancel {a : K} (ha : a ≠ 0) (b y : n → K) :
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) +
      ((scalarPivot a)⁻¹ * (pivotRow b)) *ᵥ y = 0 := by
  ext u
  cases u
  simp [scalarPivot_inv ha, scalarPivot, pivotRow, Matrix.mul_apply, Matrix.mulVec,
    dotProduct, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] in
theorem pivotWitnessLift_quadratic {a : K} (ha : a ≠ 0)
    (b y : n → K) (D : Matrix n n K) :
    pivotWitnessLift a b y ⬝ᵥ (pivotBlock a b D *ᵥ pivotWitnessLift a b y) =
      y ⬝ᵥ (pivotSchur a b D *ᵥ y) := by
  let := scalarPivotInvertible ha
  have hA : (scalarPivot a).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simp [scalarPivot]
  have h := Matrix.schur_complement_eq₁₁
    (pivotRow b) D
    (fun _ : Unit => -(a⁻¹ * ∑ j, b j * y j)) y hA
  rw [pivot_lift_cancel ha, pivot_schur_formula ha] at h
  have hblock : Matrix.fromBlocks (scalarPivot a) (pivotRow b) (pivotRow b)ᴴ D =
      pivotBlock a b D := by
    ext i j
    cases i <;> cases j <;> simp [pivotBlock, pivotRow, Matrix.fromBlocks]
  rw [hblock] at h
  simpa only [← Matrix.dotProduct_mulVec, star_trivial, Matrix.zero_mulVec,
    zero_dotProduct, zero_add, pivotWitnessLift] using h

end TrivialStar

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivot
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.PivotHistory.restore_push _root_.OAI.KS.W17.schurWitnessLift_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

open Matrix

namespace KS.W07

theorem quadratic_submatrix_equiv {n m K : Type*} [Fintype n] [Fintype m]
    [CommSemiring K] (M : Matrix n n K) (x : n → K) (e : m ≃ n) :
    (x ∘ e) ⬝ᵥ (M.submatrix e e *ᵥ (x ∘ e)) = x ⬝ᵥ (M *ᵥ x) := by
  rw [Matrix.submatrix_mulVec_equiv]
  have hc : (x ∘ e) ∘ e.symm = x := by funext i; simp
  rw [hc]
  exact comp_equiv_dotProduct_comp_equiv x (M *ᵥ x) e

theorem fin_pivotBlock {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n) =
      pivotBlock (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) := by
  ext i j
  cases i with
  | inl i => cases i; cases j <;> rfl
  | inr i =>
    cases j with
    | inl j => cases j; exact hM.apply 0 i.succ
    | inr j => rfl

theorem fin_pivotSchur {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : M.IsSymm) :
    pivotSchur (M 0 0) (fun i => M 0 i.succ) (KS.W17.trailingMatrix M) =
      KS.W17.schurTail M := by
  ext i j
  simp only [pivotSchur, KS.W17.schurTail, KS.W17.trailingMatrix, hM.apply 0 i.succ]

theorem fin_pivotWitnessLift {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ∘ pivotIndexEquiv n =
      pivotWitnessLift (M 0 0) (fun i => M 0 i.succ) y := by
  funext i
  cases i with
  | inl i =>
    cases i
    simp [pivotIndexEquiv, KS.W17.schurWitnessLift,
      pivotWitnessLift, div_eq_mul_inv, mul_comm]
  | inr i => rfl

theorem fin_schurWitnessLift_quadratic {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (hM : M.IsSymm)
    (ha : M 0 0 ≠ 0) (y : Fin n → ℚ) :
    KS.W17.schurWitnessLift M y ⬝ᵥ (M *ᵥ KS.W17.schurWitnessLift M y) =
      y ⬝ᵥ (KS.W17.schurTail M *ᵥ y) := by
  rw [← quadratic_submatrix_equiv M (KS.W17.schurWitnessLift M y) (pivotIndexEquiv n),
    fin_pivotBlock M hM, fin_pivotWitnessLift M y,
    pivotWitnessLift_quadratic ha, fin_pivotSchur M hM]

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

open Matrix

variable {n : Type*} [Fintype n]

theorem scalarPivot_posDef {a : ℝ} (ha : 0 < a) : (scalarPivot a).PosDef := by
  have heq : scalarPivot a = Matrix.diagonal (fun _ : Unit => a) := by
    ext i j
    cases i; cases j
    simp [scalarPivot]
  rw [heq]
  exact Matrix.PosDef.diagonal (fun _ => ha)

omit [Fintype n] in
theorem real_pivot_schur_formula {a : ℝ} (ha : a ≠ 0)
    (b : n → ℝ) (D : Matrix n n ℝ) :
    D - (pivotRow b)ᴴ * (scalarPivot a)⁻¹ *
      (pivotRow b) = pivotSchur a b D :=
  pivot_schur_formula ha b D

theorem pivotSchur_posSemidef {a : ℝ} (ha : 0 < a)
    (b : n → ℝ) (D : Matrix n n ℝ) (hM : (pivotBlock a b D).PosSemidef) :
    (pivotSchur a b D).PosSemidef := by
  let _ := scalarPivotInvertible (ne_of_gt ha)
  have hM' : (Matrix.fromBlocks (scalarPivot a)
      (pivotRow b)
      (pivotRow b)ᴴ D).PosSemidef := by
    exact hM
  have h := (Matrix.PosDef.fromBlocks₁₁
    (pivotRow b) D (scalarPivot_posDef ha)).mp hM'
  exact real_pivot_schur_formula (ne_of_gt ha) b D ▸ h

omit [Fintype n] in
theorem rat_pivotSchur_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotSchur a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotSchur (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  simp [pivotSchur]

omit [Fintype n] in
theorem rat_pivotBlock_cast (a : ℚ) (b : n → ℚ) (D : Matrix n n ℚ) :
    (pivotBlock a b D).map (fun q : ℚ => (q : ℝ)) =
      pivotBlock (a : ℝ) (fun i => (b i : ℝ)) (D.map (fun q : ℚ => (q : ℝ))) := by
  ext i j
  cases i <;> cases j <;> rfl

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FinPivotPSD
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.KS.W17.schurEntryExpr_eval _root_.OAI.KS.W17.schurTail_zero_pivot
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W07

theorem rational_isSymm_of_cast_posSemidef {n : Type*} [Fintype n]
    {M : Matrix n n ℚ} (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    M.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  apply Rat.cast_injective (α := ℝ)
  simpa using hM.isHermitian.apply i j

theorem fin_schurTail_posSemidef {n : ℕ}
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    ((KS.W17.schurTail M).map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  by_cases hz : M 0 0 = 0
  · have hs : KS.W17.schurTail M = KS.W17.trailingMatrix M := by
      ext i j
      simp [KS.W17.schurTail, KS.W17.trailingMatrix, hz]
    rw [hs]
    exact hM.submatrix Fin.succ
  · have hsym := rational_isSymm_of_cast_posSemidef hM
    have ha0 : 0 ≤ M 0 0 := by
      have h := hM.diag_nonneg (i := (0 : Fin (n + 1)))
      simp only [Matrix.map_apply] at h
      exact_mod_cast h
    have ha : (0 : ℝ) < (M 0 0 : ℝ) := by
      exact_mod_cast (lt_of_le_of_ne ha0 (Ne.symm hz))
    have hsub := hM.submatrix (pivotIndexEquiv n)
    change ((M.submatrix (pivotIndexEquiv n) (pivotIndexEquiv n)).map
      (fun q : ℚ => (q : ℝ))).PosSemidef at hsub
    rw [fin_pivotBlock M hsym, rat_pivotBlock_cast] at hsub
    have h := pivotSchur_posSemidef ha _ _ hsub
    rw [← rat_pivotSchur_cast, fin_pivotSchur M hsym] at h
    exact h

end KS.W07

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCoordinates
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

variable {α β : Type*} {ea : α → Word}
local instance coordinates_natLE : PolyTime natLE := by unfold natLE;infer_instance
local instance coordinates_natEq_r30b459_1 : PolyTime natEq := by unfold natEq;infer_instance
local instance coordinates_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
local instance coordinates_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
local instance coordinates_identityEntry_r30b459_1 : PolyTime identityEntry := by unfold identityEntry;infer_instance
local instance coordinates_identityMatrix_r30b459_1 : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
local instance coordinates_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then

instance poly_natLT : PolyTime natLT := by unfold natLT;infer_instance
instance poly_scaleMatrix {f : α → ℚ} {g : α → MatrixData}
    (r : Realizes ea ratCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.scaleMatrix s) := by unfold Realizes.scaleMatrix;apply poly_then
instance poly_negateMatrix : PolyTime negateMatrix := by unfold negateMatrix;infer_instance
instance poly_reEntry : PolyTime reEntry := by unfold reEntry;infer_instance
instance poly_imEntry : PolyTime imEntry := by unfold imEntry;infer_instance
instance poly_squareTabulate {f : (MatrixData×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode matrixCode natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime (squareTabulate r) := by unfold squareTabulate;apply poly_then
instance poly_realDecode : PolyTime realDecode := by unfold realDecode;apply poly_then
instance poly_singletonList (ea : α → Word) : PolyTime (singletonList ea) := by unfold singletonList;apply poly_then
instance poly_replicateList (ea : α → Word) : PolyTime (replicateList ea) := by unfold replicateList;infer_instance
instance poly_blockScalar : PolyTime blockScalar := by unfold blockScalar;apply poly_then
instance poly_withLevel : PolyTime withLevel := by unfold withLevel;apply poly_both
instance poly_matrixSub : PolyTime matrixSub := by
  unfold matrixSub
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance poly_zeroRect : PolyTime zeroRect := by unfold zeroRect;apply poly_then
instance poly_blockDiagonal : PolyTime blockDiagonal := by unfold blockDiagonal;apply poly_then
instance poly_vdD : PolyTime vdD := by unfold vdD;infer_instance
instance poly_vdRest : PolyTime vdRest := by unfold vdRest;infer_instance
instance poly_vdAtoms : PolyTime vdAtoms := by unfold vdAtoms;infer_instance
instance poly_vdParams : PolyTime vdParams := by unfold vdParams;infer_instance
instance poly_vdX : PolyTime vdX := by unfold vdX;infer_instance
instance poly_vdTheta : PolyTime vdTheta := by unfold vdTheta;infer_instance
instance poly_vdEps : PolyTime vdEps := by unfold vdEps;infer_instance
instance poly_realDimension : PolyTime realDimension := by unfold realDimension;infer_instance
instance poly_valueDimension : PolyTime valueDimension := by unfold valueDimension;infer_instance
instance poly_coordinateIndexRealizes (b : Bool) : PolyTime (coordinateIndexRealizes b) := by unfold coordinateIndexRealizes;first | infer_instance | apply poly_then
instance poly_coordinateEntry (b : Bool) : PolyTime (coordinateEntry b) := by unfold coordinateEntry;infer_instance
instance poly_coordinates (b : Bool) : PolyTime (coordinates b) := by unfold coordinates;first | infer_instance | apply poly_then
instance poly_matrixVariable (b : Bool) : PolyTime (matrixVariable b) := by unfold matrixVariable;first | infer_instance | apply poly_then

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMatrixFold
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

lemma QParts.mono {H K : ℕ} {q : ℚ} (h : QParts H q) (hk : H≤K) : QParts K q :=
  ⟨h.1.trans (Nat.pow_le_pow_right (by decide) hk),h.2.trans (Nat.pow_le_pow_right (by decide) hk)⟩
lemma qparts_length (q : ℚ) : QParts (ratCode q).length q := KS.W01.rational_parts_le_two_pow_length q
lemma QParts.mul {H K : ℕ} {q r : ℚ} (hq : QParts H q) (hr : QParts K r) : QParts (H+K) (q*r) :=
  KS.W30.mul_parts_le_two_pow _ _ _ _ hq.1 hq.2 hr.1 hr.2
lemma QParts.length {H : ℕ} {q : ℚ} (hq : QParts H q) : (ratCode q).length≤4*H+7 := by
  have h := KS.W01.ratLength_le_of_parts q H H hq.1 hq.2
  change KS.W01.ratLength q≤4*H+7
  omega

instance poly_accumMatrix : PolyTime accumMatrixRealizes := by
  unfold accumMatrixRealizes
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_both
  · exact poly_matrixAdd
instance poly_normalPencil : PolyTime normalPencil := by unfold normalPencil;apply poly_then

end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoots
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_binarySucc _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize

instance poly_ratNumBinary : PolyTime ratNumBinary := by unfold ratNumBinary;infer_instance
instance poly_unframeNat : PolyTime unframeNat := by unfold unframeNat;apply poly_reindex
instance poly_ratDenBinary : PolyTime ratDenBinary := by unfold ratDenBinary;apply poly_then
instance poly_ratDenSize : PolyTime ratDenSize := by unfold ratDenSize;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_DeterminantBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

open Matrix

theorem abs_adjugate_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hB : 1 ≤ B) (hA : ∀ i j, |A i j| ≤ (B : ℤ)) (i j : Fin n) :
    |A.adjugate i j| ≤ (n.factorial : ℤ) * (B : ℤ) ^ n := by
  rw [Matrix.adjugate_apply]
  apply abs_det_le
  intro k l
  by_cases hk : k = j
  · subst k
    by_cases hl : l = i
    · subst l
      simpa using (show (1 : ℤ) ≤ (B : ℤ) by exact_mod_cast hB)
    · simp [Matrix.updateRow, Function.update, hl]
  · simpa [Matrix.updateRow, Function.update, hk] using hA k l

theorem natAbs_adjugate_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (B : ℕ)
    (hB : 1 ≤ B) (hA : ∀ i j, (A i j).natAbs ≤ B) (i j : Fin n) :
    (A.adjugate i j).natAbs ≤ n.factorial * B ^ n := by
  have hh : ∀ i j, |A i j| ≤ (B : ℤ) := by
    intro k l
    rw [← Int.natCast_natAbs]
    exact_mod_cast hA k l
  have hd := abs_adjugate_le A B hB hh i j
  rw [← Int.natCast_natAbs] at hd
  exact_mod_cast hd

theorem natAbs_adjugate_le_two_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ 2 ^ b) (i j : Fin n) :
    (A.adjugate i j).natAbs ≤ 2 ^ (n * n + b * n) := by
  calc
    (A.adjugate i j).natAbs ≤ n.factorial * (2 ^ b) ^ n :=
      natAbs_adjugate_le A (2 ^ b) (Nat.one_le_two_pow) hA i j
    _ ≤ 2 ^ (n * n) * (2 ^ b) ^ n :=
      Nat.mul_le_mul_right _ (factorial_le_two_pow_sq n)
    _ = 2 ^ (n * n + b * n) := by rw [← pow_mul, ← pow_add]

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_InverseBounds
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

open scoped Rat

theorem integer_matrix_inverse_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ)
    (i j : Fin n) :
    ((A.map (fun z : ℤ => (z : ℚ)))⁻¹) i j =
      (A.adjugate i j : ℚ) / (A.det : ℚ) := by
  have hadj := (Int.castRingHom ℚ).map_adjugate A
  have hdet := (Int.castRingHom ℚ).map_det A
  change A.adjugate.map (fun z : ℤ => (z : ℚ)) =
    (A.map (fun z : ℤ => (z : ℚ))).adjugate at hadj
  change (A.det : ℚ) = (A.map (fun z : ℤ => (z : ℚ))).det at hdet
  rw [Matrix.inv_def, ← hdet, ← hadj]
  simp [Matrix.smul_apply, Ring.inverse_eq_inv, div_eq_mul_inv, mul_comm]

theorem rational_matrix_inverse_entry {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hdet : A.det ≠ 0) (i j : Fin n) :
    A⁻¹ i j = ((A.den : ℤ) * A.num.adjugate i j : ℤ) /. A.num.det := by
  have hD : (A.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.den_ne_zero
  let : Invertible (A.den : ℚ) := invertibleOfNonzero hD
  have hN : A.num.map (fun z : ℤ => (z : ℚ)) = (A.den : ℚ) • A := by
    ext k l
    exact cleared_matrix_entry A k l
  have hi : A⁻¹ = (A.den : ℚ) • (A.num.map (fun z : ℤ => (z : ℚ)))⁻¹ := by
    rw [hN, Matrix.inv_smul A (A.den : ℚ) (isUnit_iff_ne_zero.mpr hdet)]
    simp [smul_smul, invOf_eq_inv, hD]
  rw [hi, Matrix.smul_apply, smul_eq_mul, integer_matrix_inverse_entry]
  simp only [Rat.divInt_eq_div, Int.cast_mul, Int.cast_natCast]
  exact (mul_div_assoc _ _ _).symm

theorem cleared_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (hdet : A.det ≠ 0) : A.num.det ≠ 0 := by
  have hD : (A.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr A.den_ne_zero
  have hN : A.num.map (fun z : ℤ => (z : ℚ)) = (A.den : ℚ) • A := by
    ext k l
    exact cleared_matrix_entry A k l
  intro hz
  have heq : ((A.den : ℚ) • A).det = 0 := by
    rw [← hN, ← Int.cast_det, hz, Int.cast_zero]
  have hz' : ((A.den : ℚ) ^ n) * A.det = 0 := by
    simpa only [Matrix.det_smul, Fintype.card_fin] using heq
  exact (mul_ne_zero (pow_ne_zero _ hD) hdet) hz'

theorem rational_inverse_parts_size_le {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (b : ℕ) (hnum : ∀ i j, (A i j).num.natAbs ≤ 2 ^ b)
    (hden : ∀ i j, (A i j).den ≤ 2 ^ b) (hdet : A.det ≠ 0)
    (i j : Fin n) :
    let K := b * (n * n) + (n * n + (b * (n * n) + b) * n)
    Nat.size (A⁻¹ i j).num.natAbs ≤ K + 1 ∧
      Nat.size (A⁻¹ i j).den ≤ K + 1 := by
  let c := b * (n * n) + b
  let e := n * n + c * n
  let K := b * (n * n) + e
  have hN : ∀ k l, (A.num k l).natAbs ≤ 2 ^ c :=
    fun k l => cleared_num_le_two_pow A b hnum hden k l
  have hnum' : (((A.den : ℤ) * A.num.adjugate i j : ℤ)).natAbs ≤ 2 ^ K := by
    rw [Int.natAbs_mul, Int.natAbs_natCast]
    calc
      A.den * (A.num.adjugate i j).natAbs ≤
          2 ^ (b * (n * n)) * 2 ^ e :=
        Nat.mul_le_mul (matrix_den_le_two_pow A b hden)
          (natAbs_adjugate_le_two_pow A.num c hN i j)
      _ = 2 ^ K := (pow_add 2 _ _).symm
  have hden' : A.num.det.natAbs ≤ 2 ^ K := by
    apply le_trans (natAbs_det_le_two_pow A.num c hN)
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_add_left e _)
  have hs : 2 ^ K < 2 ^ (K + 1) := by
    exact Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _)
  change Nat.size (A⁻¹ i j).num.natAbs ≤ K + 1 ∧ Nat.size (A⁻¹ i j).den ≤ K + 1
  rw [rational_matrix_inverse_entry A hdet]
  exact ⟨divInt_num_size_le _ _ (cleared_det_ne_zero A hdet) _ (lt_of_le_of_lt hnum' hs),
    divInt_den_size_le _ _ (cleared_det_ne_zero A hdet) _ (lt_of_le_of_lt hden' hs)⟩

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Machines_InverseHeight
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KS.W30

theorem inverseBitBound_mono_dim {n N : ℕ} (b : ℕ) (hn : n ≤ N) :
    inverseBitBound n b ≤ inverseBitBound N b := by
  have hs := Nat.mul_le_mul hn hn
  have hb := Nat.mul_le_mul_left b hs
  exact Nat.add_le_add_right
    (Nat.add_le_add hb (Nat.add_le_add hs
      (Nat.mul_le_mul (Nat.add_le_add_right hb b) hn))) 1

theorem inverseBitBound_le_polynomial (n b : ℕ) :
    inverseBitBound n b ≤ 6 * (b + 1) * (n + 1) ^ 3 := by
  unfold inverseBitBound
  ring_nf
  omega

theorem inverseBitBound_twice_le_polynomial (n b : ℕ) :
    inverseBitBound n (inverseBitBound n b) ≤ 32 * (b + 1) * (n + 1) ^ 6 := by
  unfold inverseBitBound
  ring_nf
  omega

theorem inverseBitBound_twice_le_input_polynomial {n b L : ℕ} (hn : n ≤ L) (hb : b ≤ L) :
    inverseBitBound n (inverseBitBound n b) ≤ 32 * (L + 1) ^ 7 := by
  apply le_trans (inverseBitBound_twice_le_polynomial n b)
  calc
    32 * (b + 1) * (n + 1) ^ 6 ≤ 32 * (L + 1) * (L + 1) ^ 6 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 32 (Nat.add_le_add_right hb 1))
        (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) 6)
    _ = 32 * (L + 1) ^ 7 := by ring

end KS.W30

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_PivotHistory
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace KS.W07

open Matrix

theorem PivotTrace.state_posSemidef {N k t : ℕ}
    {M : Matrix (Fin N) (Fin N) ℚ} {p : Fin k → Fin N} {r : Fin t → Fin N}
    {S : Matrix (Fin t) (Fin t) ℚ} (h : PivotTrace M p r S)
    (hM : (M.map (fun q : ℚ => (q : ℝ))).PosSemidef) :
    (S.map (fun q : ℚ => (q : ℝ))).PosSemidef := by
  induction h with
  | initial => exact hM
  | zero _ _ ih => exact fin_schurTail_posSemidef _ ih
  | positive _ _ ih => exact fin_schurTail_posSemidef _ ih

end KS.W07

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStored
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}

lemma flatten_code_le (ea : α → Word) (xs : List (List α)) :
    (listCode ea xs.flatten).length≤(listCode (listCode ea) xs).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.flatten_cons,listCode_append,List.length_append,listCode_cons,prodCode_length]
      omega
instance size_appendList (ea : α → Word) : FoldSize (appendList ea) := by
  refine ⟨⟨2*X,?_⟩⟩
  intro s xs ys zs h
  rw [fold_append_flatten,listCode_append,List.length_append]
  have hs := le_prodCode_left (ea:=listCode ea) (eb:=listCode (listCode ea)) (s,xs)
  have hy := (flatten_code_le ea ys).trans ((prefix_code_length (listCode ea) xs ys zs h).trans (le_prodCode_right (ea:=listCode ea) (s,xs)))
  change _≤2*(prodCode (listCode ea) (listCode (listCode ea)) (s,xs)).length
  dsimp only at hs hy
  omega
instance poly_flattenList (ea : α → Word) : PolyTime (flattenList ea) := by unfold flattenList;infer_instance
instance poly_joinList (ea : α → Word) : PolyTime (joinList ea) := by unfold joinList;infer_instance
instance poly_singleton (ea : α → Word) : PolyTime (singleton ea) := by unfold singleton;apply poly_then
instance poly_filterCtx {p : γ×α → Bool} (r : Realizes (prodCode ec ea) boolCode p) [PolyTime r] :
    PolyTime r.filterCtx := by unfold Realizes.filterCtx;infer_instance

instance poly_natToBinary : PolyTime natToBinary := by unfold natToBinary;infer_instance

instance poly_natLE : PolyTime natLE := by unfold natLE;infer_instance
instance poly_natEq : PolyTime natEq := by unfold natEq;infer_instance
instance poly_matrixEntry : PolyTime matrixEntry := by unfold matrixEntry;infer_instance
instance poly_matrixTabulate {f : (α×ℕ)×ℕ → ℚ}
    (r : Realizes (prodCode (prodCode ea natCode) natCode) ratCode f) [PolyTime r] :
    PolyTime r.matrixTabulate := by unfold Realizes.matrixTabulate;apply poly_then
instance poly_identityEntry : PolyTime identityEntry := by unfold identityEntry;infer_instance
instance poly_identityMatrix : PolyTime identityMatrix := by unfold identityMatrix;apply poly_then
instance poly_transposeMatrix : PolyTime transposeMatrix := by unfold transposeMatrix;apply poly_then
instance poly_matrixMul : PolyTime matrixMul := by unfold matrixMul;apply poly_then
instance poly_fromBlocks : PolyTime fromBlocks := by unfold fromBlocks;apply poly_then
instance poly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime r] [PolyTime rn] :
    PolyTime (r.tabulateFin rn) := by unfold Realizes.tabulateFin;infer_instance
instance poly_familyFirst {n : α → ℕ} : PolyTime (familyFirst (ea:=ea) (n:=n)) := by unfold familyFirst;apply poly_reindex
instance poly_familyIndex {n : α → ℕ} : PolyTime (familyIndex (ea:=ea) (n:=n)) := by unfold familyIndex;apply poly_reindex

instance poly_pow {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] (k : ℕ) : PolyTime (r.pow k) := by
  induction k with
  | zero => unfold Realizes.pow;infer_instance
  | succ k ih => unfold Realizes.pow;infer_instance
instance poly_min {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.min s) := by unfold Realizes.min;infer_instance
instance poly_max {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.max s) := by unfold Realizes.max;infer_instance
instance poly_inv {f : α → ℚ} (r : Realizes ea ratCode f) [PolyTime r] : PolyTime r.inv := by unfold Realizes.inv;infer_instance
instance poly_lt {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.lt s) := by unfold Realizes.lt;infer_instance
instance poly_eq {f g : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g) [PolyTime r] [PolyTime s] : PolyTime (r.eq s) := by unfold Realizes.eq;infer_instance

instance poly_better (ea : α → Word) : PolyTime (better ea) := by unfold better;infer_instance

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialCurvature
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_vectorNeg : PolyTime vectorNeg := by unfold vectorNeg;apply poly_map
instance poly_squareSum : PolyTime squareSum := by unfold squareSum;apply poly_then
instance poly_vectorDivide : PolyTime vectorDivide := by unfold vectorDivide;apply poly_mapCtx
instance poly_initialScale : PolyTime initialScale := by unfold initialScale;apply poly_then
instance poly_intCeil : PolyTime intCeil := by unfold intCeil;apply poly_congr
instance poly_nearest : PolyTime nearest := by unfold nearest;apply poly_congr
instance poly_nearestMesh : PolyTime nearestMesh := by unfold nearestMesh;apply poly_mul
instance poly_roundMesh : PolyTime roundMesh := by unfold roundMesh;apply poly_mapCtx
instance poly_cuN : PolyTime cuN := by unfold cuN;apply poly_then
instance poly_cuRest : PolyTime cuRest := by unfold cuRest;apply poly_then
instance poly_cuH : PolyTime cuH := by unfold cuH;apply poly_then
instance poly_cuScalars : PolyTime cuScalars := by unfold cuScalars;apply poly_then
instance poly_cuA : PolyTime cuA := by unfold cuA;apply poly_then
instance poly_cuMore : PolyTime cuMore := by unfold cuMore;apply poly_then
instance poly_cuM : PolyTime cuM := by unfold cuM;apply poly_then
instance poly_cuLast : PolyTime cuLast := by unfold cuLast;apply poly_then
instance poly_cuS : PolyTime cuS := by unfold cuS;apply poly_then
instance poly_cuRho : PolyTime cuRho := by unfold cuRho;apply poly_then
instance poly_cuShift : PolyTime cuShift := by unfold cuShift;apply poly_changeOutput
instance poly_updateVector : PolyTime updateVector := by unfold updateVector;apply poly_congr
instance poly_endpointEntry : PolyTime endpointEntry := by unfold endpointEntry;apply poly_then
instance poly_endpointCandidates : PolyTime endpointCandidates := by unfold endpointCandidates;apply poly_congr
instance poly_freezeScalar : PolyTime freezeScalar := by unfold freezeScalar;apply poly_congr
instance poly_freezeVector : PolyTime freezeVector := by unfold freezeVector;apply poly_mapCtx
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFind
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binarySucc _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixMul _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natToBinary _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_transposeMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_ratAdd _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
variable {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
lemma foldl_property {f : β → α → β} (P : β → Prop) (xs : List α) (s : β)
    (hs : P s) (hf : ∀ x∈xs,∀a,P a → P (f a x)) : P (xs.foldl f s) := by
  induction xs generalizing s with
  | nil => exact hs
  | cons x xs ih => exact ih (f s x) (hf x (by simp) s hs) (fun y hy => hf y (by simp [hy]))
lemma find_fold_size {p : γ×α → Bool} {f : γ×α → β}
    (value : Realizes (prodCode ec ea) eb f) [PolyTime value]
    (r : Realizes (prodCode (prodCode ec eb) ea) (prodCode ec eb)
      (fun z => (z.1.1,if p (z.1.1,z.2) then f (z.1.1,z.2) else z.1.2))) : FoldSize r := by
  obtain ⟨q,hq⟩ := PolyTime.bound (r:=value)
  let U := 3*X+1+q.comp (3*X+1)
  refine ⟨⟨3*X+1+U,?_⟩⟩
  intro s xs ys zs h
  let L := (prodCode (prodCode ec eb) (listCode ea) (s,xs)).length
  have hc : (ec s.1).length≤L := (le_prodCode_left s).trans (le_prodCode_left (s,xs))
  have hb : (eb s.2).length≤L := (le_prodCode_right s).trans (le_prodCode_left (s,xs))
  have hy : (listCode ea ys).length≤L := (prefix_code_length ea xs ys zs h).trans (le_prodCode_right (s,xs))
  have hv : ∀x∈ys,(eb (f (s.1,x))).length≤U.eval L := by
    intro x hx
    have hl : (prodCode ec ea (s.1,x)).length≤3*L+1 := by
      have he := (mem_length_le_code ys hx).trans hy
      rw [prodCode_length];dsimp only;omega
    have h := (value.output_length (s.1,x)).trans
      (Nat.add_le_add hl ((hq _).trans (q.eval_mono hl)))
    simp only [U,NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,NaturalPolynomial.eval_variable,NaturalPolynomial.eval_comp]
    exact h
  have hh := foldl_property (f:=fun a x => (a.1,if p (a.1,x) then f (a.1,x) else a.2))
    (fun a : γ×β => a.1=s.1 ∧ (eb a.2).length≤L+U.eval L) ys s
    ⟨rfl,hb.trans (Nat.le_add_right _ _)⟩ (by
      intro x hx a ha
      refine ⟨ha.1,?_⟩
      dsimp only
      split
      · rw [ha.1];exact (hv x hx).trans (Nat.le_add_left _ _)
      · exact ha.2)
  rw [prodCode_length,hh.1]
  change _≤3*L+1+U.eval L
  have hb' := hh.2
  dsimp only at *
  omega
instance poly_findValue {p : γ×α → Bool} {f : γ×α → β}
    (test : Realizes (prodCode ec ea) boolCode p) (value : Realizes (prodCode ec ea) eb f)
    [PolyTime test] [PolyTime value] : PolyTime (test.findValue value) := by
  let old := first (prodCode ec eb) ea
  let cx := (old.then (first ec eb)).both (second (prodCode ec eb) ea)
  let body := (old.then (first ec eb)).both ((cx.then test).ite (cx.then value) (old.then (second ec eb)))
  have : FoldSize body := find_fold_size value body
  dsimp only [Realizes.findValue]
  apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSchedule
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_saD : PolyTime saD := by unfold saD;infer_instance
instance poly_saRest : PolyTime saRest := by unfold saRest;infer_instance
instance poly_saN : PolyTime saN := by unfold saN;apply poly_then
instance poly_saScalars : PolyTime saScalars := by unfold saScalars;apply poly_then
instance poly_saNu : PolyTime saNu := by unfold saNu;apply poly_then
instance poly_saLam : PolyTime saLam := by unfold saLam;apply poly_then
instance poly_saEpsilon : PolyTime saEpsilon := by unfold saEpsilon;apply poly_div
instance poly_saSigma : PolyTime saSigma := by unfold saSigma;apply poly_div
instance poly_movementBudget : PolyTime movementBudget := by unfold movementBudget;apply poly_max
instance poly_saThreshold : PolyTime saThreshold := by unfold saThreshold;apply poly_div
instance poly_saCoarse : PolyTime saCoarse := by unfold saCoarse;apply poly_add
instance poly_saCurve2 : PolyTime saCurve2 := by unfold saCurve2;apply poly_mul
instance poly_saCurve3 : PolyTime saCurve3 := by unfold saCurve3;apply poly_mul
instance poly_saBudget : PolyTime saBudget := by unfold saBudget;apply poly_add
instance poly_saStep : PolyTime saStep := by unfold saStep;apply poly_min
instance poly_saStencil : PolyTime saStencil := by unfold saStencil;apply poly_min
instance poly_saMesh : PolyTime saMesh := by unfold saMesh;apply poly_div
instance poly_parameters_singleton : PolyTime parameters.singletonRat := by unfold parameters.singletonRat;apply poly_then
instance poly_parameters : PolyTime parameters := by unfold parameters;apply poly_changeOutput
instance poly_parameterField (i : ℕ) : PolyTime (parameterField i) := by
  unfold parameterField
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · refine @poly_both _ _ _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_reindex
  · infer_instance
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceBasics
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_activeIndices : PolyTime activeIndices := by unfold activeIndices;apply poly_then
instance poly_extendEntry : PolyTime extendEntry := by unfold extendEntry;apply poly_congr
instance poly_extendVector : PolyTime extendVector := by unfold extendVector;apply poly_then
instance poly_fD : PolyTime fD := by unfold fD;apply poly_then
instance poly_fRest : PolyTime fRest := by unfold fRest;apply poly_then
instance poly_fAtoms : PolyTime fAtoms := by unfold fAtoms;apply poly_then
instance poly_fArgs : PolyTime fArgs := by unfold fArgs;apply poly_then
instance poly_fBase : PolyTime fBase := by unfold fBase;apply poly_then
instance poly_fScalars : PolyTime fScalars := by unfold fScalars;apply poly_then
instance poly_fNu : PolyTime fNu := by unfold fNu;apply poly_then
instance poly_fLam : PolyTime fLam := by unfold fLam;apply poly_then
instance poly_fIndices : PolyTime fIndices := by unfold fIndices;apply poly_congr
instance poly_fN : PolyTime fN := by unfold fN;apply poly_congr
instance poly_fSchedule : PolyTime fSchedule := by unfold fSchedule;apply poly_then
instance poly_gather : PolyTime gather := by unfold gather;apply poly_mapCtx
instance poly_fState : PolyTime fState := by unfold fState;apply poly_congr
instance poly_fpP : PolyTime fpP := by unfold fpP;apply poly_then
instance poly_fpY : PolyTime fpY := by unfold fpY;apply poly_then
instance poly_fpExtend : PolyTime fpExtend := by unfold fpExtend;apply poly_congr
instance poly_fpPotential : PolyTime fpPotential := by unfold fpPotential;apply poly_changeOutput
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialRoundedStep
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23 RationalGridSize
open scoped BigOperators

instance poly_roundedUpdate : PolyTime roundedUpdate := by unfold roundedUpdate;apply poly_then
instance poly_statePencil : PolyTime statePencil := by unfold statePencil;apply poly_then
instance poly_stateParameters : PolyTime stateParameters := by unfold stateParameters;apply poly_then
instance poly_stateY : PolyTime stateY := by unfold stateY;apply poly_then
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialSearch
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_searchPencil : PolyTime searchPencil := by unfold searchPencil;apply poly_then
instance poly_searchParameters : PolyTime searchParameters := by unfold searchParameters;apply poly_then
instance poly_searchY : PolyTime searchY := by unfold searchY;apply poly_then
instance poly_searchDim : PolyTime searchDim := by unfold searchDim;infer_instance
instance poly_searchStep : PolyTime searchStepRealizes := by unfold searchStepRealizes;apply poly_div
instance poly_searchMesh : PolyTime searchMeshRealizes := by unfold searchMeshRealizes;apply poly_div
instance poly_searchInit : PolyTime searchInit := by unfold searchInit;apply poly_changeOutput

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOptimize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_optB : PolyTime optB := by unfold optB;apply poly_then
instance poly_optF : PolyTime optF := by unfold optF;apply poly_then
instance poly_optScalars : PolyTime optScalars := by unfold optScalars;apply poly_then
instance poly_optDelta : PolyTime optDelta := by unfold optDelta;apply poly_then
instance poly_optRest : PolyTime optRest := by unfold optRest;apply poly_then
instance poly_optRadius : PolyTime optRadius := by unfold optRadius;apply poly_both
instance poly_optUpper : PolyTime optUpper := by unfold optUpper;apply poly_then
instance poly_optLevel : PolyTime optLevel := by unfold optLevel;apply poly_add
instance poly_optLevelPencil : PolyTime optLevelPencil := by unfold optLevelPencil;apply poly_congr
instance poly_osP : PolyTime osP := by unfold osP;apply poly_then
instance poly_osK : PolyTime osK := by unfold osK;apply poly_then
instance poly_osY : PolyTime osY := by unfold osY;apply poly_then

lemma RunsPoly.then_with {α β γ : Type*} {ea : α → Word} {eb : β → Word} {ec : γ → Word}
    {F : α → β} {G : β → γ} {ι : Type*} {L : ι → ℕ}
    {r : Realizes ea eb F} {s : Realizes eb ec G} {a : ι → α}
    (hr : RunsPoly L r a)
    (hs : IsPoly L (fun i => (eb (F (a i))).length) → RunsPoly L s (fun i => F (a i))) :
    RunsPoly L (r.then s) a := hr.then (hs hr.output)

end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialValueQuery
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_veP : PolyTime veP := by unfold veP;infer_instance
instance poly_veY : PolyTime veY := by unfold veY;infer_instance
instance poly_veD : PolyTime veD := by unfold veD;apply poly_then
instance poly_veN : PolyTime veN := by unfold veN;apply poly_then
instance poly_veEye : PolyTime veEye := by unfold veEye;apply poly_then
instance poly_veEps : PolyTime veEps := by unfold veEps;apply poly_then
instance poly_veTime : PolyTime veTime := by unfold veTime;apply poly_then
instance poly_veVariable (b : Bool) : PolyTime (veVariable b) := by unfold veVariable;apply poly_then
instance poly_sandwich : PolyTime sandwich := by unfold sandwich;apply poly_then
instance poly_lowerBox (b : Bool) : PolyTime (lowerBox b) := by unfold lowerBox;apply poly_then
instance poly_upperBox (b : Bool) : PolyTime (upperBox b) := by unfold upperBox;apply poly_then
instance poly_tinyMatrix : PolyTime tinyMatrix := by unfold tinyMatrix;apply poly_then
instance poly_blockWith {α : Type*} {ea : α → Word} {f g : α → MatrixData}
    (r : Realizes ea matrixCode f) (s : Realizes ea matrixCode g) [PolyTime r] [PolyTime s] :
    PolyTime (r.blockWith s) := by unfold Realizes.blockWith;infer_instance
instance poly_traceMatrix : PolyTime traceMatrix := by unfold traceMatrix;apply poly_then
instance poly_valueObjective : PolyTime valueObjective := by unfold valueObjective;apply poly_add
instance poly_vqData : PolyTime vqData := by unfold vqData;apply poly_then
instance poly_vqDelta : PolyTime vqDelta := by unfold vqDelta;apply poly_then
instance poly_valueLipschitz : PolyTime valueLipschitz := by unfold valueLipschitz;apply poly_mul
instance poly_valueOuterRadius : PolyTime valueOuterRadius := by unfold valueOuterRadius;apply poly_mul
instance poly_valueInnerRadius : PolyTime valueInnerRadius := by unfold valueInnerRadius;apply poly_div
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialPotential
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine

instance poly_ppD : PolyTime ppD := by unfold ppD;apply poly_then
instance poly_ppRest : PolyTime ppRest := by unfold ppRest;apply poly_then
instance poly_ppAtoms : PolyTime ppAtoms := by unfold ppAtoms;apply poly_then
instance poly_ppArgs : PolyTime ppArgs := by unfold ppArgs;apply poly_then
instance poly_ppX : PolyTime ppX := by unfold ppX;apply poly_then
instance poly_ppScalars : PolyTime ppScalars := by unfold ppScalars;apply poly_then
instance poly_ppNu : PolyTime ppNu := by unfold ppNu;apply poly_then
instance poly_ppLam : PolyTime ppLam := by unfold ppLam;apply poly_then
instance poly_ppError : PolyTime ppError := by unfold ppError;apply poly_then
instance poly_ppN : PolyTime ppN := by unfold ppN;apply poly_congr
instance poly_ppRootTolerance : PolyTime ppRootTolerance := by unfold ppRootTolerance;apply poly_div
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialMapFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_l1Rationals _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_sumRationals _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word} {f : α → β}
lemma runsPoly_map (r : Realizes ea eb f) (xs : ι → List α)
    (ha : IsPoly L (fun i => (listCode ea (xs i)).length))
    (hc : ∃ p : NaturalPolynomial,∀i x,x∈xs i → r.cost x≤p.eval (L i)) :
    RunsPoly L r.map xs := by
  obtain ⟨p,hp⟩ := hc
  obtain ⟨q,hq⟩ := ha
  refine ⟨⟨q,hq⟩,⟨2*q+q*(3*q+p+6*(q+p)+8)+q*(2*(q+p)+1)+4,?_⟩⟩
  intro i
  let A := q.eval (L i)
  let C := p.eval (L i)
  have hn : (xs i).length≤A := (list_length_le_code ea (xs i)).trans (hq i)
  have he : ∀x∈xs i,(ea x).length≤A := fun x hx => (mem_length_le_code (xs i) hx).trans (hq i)
  have ho : ∀x∈xs i,(eb (f x)).length≤A+C := fun x hx =>
    (r.output_length x).trans (Nat.add_le_add (he x hx) (hp i x hx))
  have hs := sum_map_bound (xs i) (fun x => FramedMapRoutine.bodyTicks ea (fun x => eb (f x)) r.cost x+1)
    (3*A+C+6*(A+C)+8) (by
      intro x hx
      have hl := he x hx
      have hc' := hp i x hx
      have hout := ho x hx
      simp only [FramedMapRoutine.bodyTicks,KS.W01.length_frame]
      omega)
  have ht := listCode_length_bound (ea:=fun x => eb (f x)) (xs i) (A+C) ho
  have hs' := hs.trans (Nat.mul_le_mul_right _ hn)
  have ht' := ht.trans (Nat.mul_le_mul_right _ hn)
  change FramedMapRoutine.ticks ea (fun x => eb (f x)) r.cost (xs i)≤_
  simp only [FramedMapRoutine.ticks,FramedMapRoutine.scanTicks]
  change 2*(listCode ea (xs i)).length+2+((xs i).map _).sum+1+
    (listCode (fun x => eb (f x)) (xs i)).length+1≤_
  change _≤2*A+A*(3*A+C+6*(A+C)+8)+A*(2*(A+C)+1)+4
  have hl : (listCode ea (xs i)).length≤A := hq i
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFinFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}
lemma runsPoly_tabulateFin {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hc : ∃p : NaturalPolynomial,∀i j,r.cost ⟨a i,j⟩≤p.eval (L i)) :
    RunsPoly L (r.tabulateFin rn) a := by
  unfold Realizes.tabulateFin
  apply RunsPoly.congr
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_map _ _ hw
  obtain ⟨p,hp⟩ := hc
  refine ⟨p,?_⟩
  intro i x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  exact hp i j
lemma runsPoly_tabulateFin_family {n : α → ℕ} {f : (Σ a,Fin (n a)) → β}
    (r : Realizes (finFamilyCode ea n) eb f) (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length))
    (hc : RunsPoly (fun s : Σ i,Fin (n (a i)) => L s.1) r (fun s => ⟨a s.1,s.2⟩)) :
    RunsPoly L (r.tabulateFin rn) a := by
  apply runsPoly_tabulateFin r rn a ha
  obtain ⟨p,hp⟩ := hc.cost
  exact ⟨p,fun i j => hp ⟨i,j⟩⟩
lemma isPoly_finFamily {n : α → ℕ} (rn : Realizes ea natCode n) [PolyTime rn]
    (a : ι → α) (ha : IsPoly L (fun i => (ea (a i)).length)) :
    IsPoly (fun s : Σ i,Fin (n (a i)) => L s.1)
      (fun s => (finFamilyCode ea n ⟨a s.1,s.2⟩).length) := by
  have hn := (RunsPoly.of_poly rn a ha).output
  have h := ((isPoly_const L 2).mul ha).add ((isPoly_const L 1).add hn)
  apply (h.reindex (fun s : Σ i,Fin (n (a i)) => s.1)).mono
  intro s
  simp only [finFamilyCode,prodCode_length,natCode,List.length_replicate,Function.comp_apply]
  have hj := s.2.isLt
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialStencil
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ}
instance poly_fiP : PolyTime fiP := by unfold fiP;apply poly_familyFirst
instance poly_fiI : PolyTime fiI := by unfold fiI;apply poly_familyIndex
instance poly_fdS : PolyTime fdS := by unfold fdS;apply poly_familyFirst
instance poly_fdP : PolyTime fdP := by unfold fdP;apply poly_then
instance poly_fdI : PolyTime fdI := by unfold fdI;apply poly_then
instance poly_fdJ : PolyTime fdJ := by unfold fdJ;apply poly_familyIndex
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceChoice
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι : Type*} {L : ι → ℕ}
instance poly_vectorSub : PolyTime vectorSub := by unfold vectorSub;apply poly_zipWith
instance poly_curvatureCandidates : PolyTime curvatureCandidates := by unfold curvatureCandidates;apply poly_congr
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialFaceFuel
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

local notation "X" => NaturalPolynomial.variable
instance size_minDatum : FoldSize ((first ratCode ratCode).min (second ratCode ratCode)) := by
  refine ⟨⟨X,?_⟩⟩
  intro s xs ys zs he
  let L := (prodCode ratCode vectorCode (s,xs)).length
  have hs : (ratCode s).length≤L := le_prodCode_left (s,xs)
  have hy : (vectorCode ys).length≤L := (prefix_code_length ratCode xs ys zs he).trans (le_prodCode_right (s,xs))
  exact foldl_property (fun a : ℚ => (ratCode a).length≤L) ys s hs (by
    intro x hx a ha
    change (ratCode (min a x)).length≤L
    rw [min_def]
    split
    · exact ha
    · exact (mem_length_le_code ys hx).trans hy)
instance poly_minList : PolyTime minList := by unfold minList;apply poly_congr
instance poly_fUniformDrop : PolyTime fUniformDrop := by unfold fUniformDrop;apply poly_congr
instance poly_packFace {α : Type*} {ea : α → Word} {f : α → FaceParams}
    {g : (a : α) → Fin (f a).N → ℚ}
    (p : Realizes ea faceCode f) (y : Realizes ea vectorCode (fun a => List.ofFn (g a)))
    [PolyTime p] [PolyTime y] : PolyTime (packFace p y) := by
  unfold packFace;apply poly_changeOutput
instance poly_faceStart : PolyTime faceStart := by
  unfold faceStart
  refine @poly_packFace _ _ _ _ _ _ ?_ ?_
  · exact poly_identity _
  · apply poly_congr
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialIterateFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_abs _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_add _root_.OAI.CurrentKS.Realization.poly_appendList _root_.OAI.CurrentKS.Realization.poly_better _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_conditional _root_.OAI.CurrentKS.Realization.poly_consList _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_div _root_.OAI.CurrentKS.Realization.poly_dot _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_eq _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_familyFirst _root_.OAI.CurrentKS.Realization.poly_familyIndex _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_filterCtx _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_flattenList _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_fromBlocks _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_getD _root_.OAI.CurrentKS.Realization.poly_identityEntry _root_.OAI.CurrentKS.Realization.poly_identityMatrix _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_inv _root_.OAI.CurrentKS.Realization.poly_ite _root_.OAI.CurrentKS.Realization.poly_joinList _root_.OAI.CurrentKS.Realization.poly_le _root_.OAI.CurrentKS.Realization.poly_lengthBody _root_.OAI.CurrentKS.Realization.poly_lengthList _root_.OAI.CurrentKS.Realization.poly_lookupStep _root_.OAI.CurrentKS.Realization.poly_lt _root_.OAI.CurrentKS.Realization.poly_mapCtx _root_.OAI.CurrentKS.Realization.poly_mapCtxBody _root_.OAI.CurrentKS.Realization.poly_matVec _root_.OAI.CurrentKS.Realization.poly_matrixAdd _root_.OAI.CurrentKS.Realization.poly_matrixEntry _root_.OAI.CurrentKS.Realization.poly_matrixMul _root_.OAI.CurrentKS.Realization.poly_matrixScale _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixTabulate _root_.OAI.CurrentKS.Realization.poly_max _root_.OAI.CurrentKS.Realization.poly_min _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_mul _root_.OAI.CurrentKS.Realization.poly_natAdd _root_.OAI.CurrentKS.Realization.poly_natEq _root_.OAI.CurrentKS.Realization.poly_natIsZero _root_.OAI.CurrentKS.Realization.poly_natLE _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natMul _root_.OAI.CurrentKS.Realization.poly_natPred _root_.OAI.CurrentKS.Realization.poly_natSucc _root_.OAI.CurrentKS.Realization.poly_natToBinary _root_.OAI.CurrentKS.Realization.poly_natToRat _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_neg _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_pow _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_quadratic _root_.OAI.CurrentKS.Realization.poly_range _root_.OAI.CurrentKS.Realization.poly_rangeStep _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratLE _root_.OAI.CurrentKS.Realization.poly_ratOp _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_reverseBody _root_.OAI.CurrentKS.Realization.poly_reverseList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundScalar _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_singleton _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_sub _root_.OAI.CurrentKS.Realization.poly_tabulate _root_.OAI.CurrentKS.Realization.poly_tabulateFin _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorAdd _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorScale _root_.OAI.CurrentKS.Realization.poly_vectorScaleBody _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.poly_zipWith _root_.OAI.CurrentKS.Realization.size_appendList _root_.OAI.CurrentKS.Realization.size_lengthBody _root_.OAI.CurrentKS.Realization.size_lookupStep _root_.OAI.CurrentKS.Realization.size_mapCtxBody _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natMulStep _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.CurrentKS.Realization.size_rangeStep _root_.OAI.CurrentKS.Realization.size_reverseBody _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α : Type*} {L : ι → ℕ} {ea : α → Word} {f : α → α}
lemma runsPoly_iterate (r : Realizes ea ea f) (a : ι → ℕ×α)
    (ha : IsPoly L (fun i => (prodCode natCode ea (a i)).length))
    (hc : ∃p : NaturalPolynomial,∀i j,j<(a i).1 → r.cost (f^[j] (a i).2)≤p.eval (L i)) :
    RunsPoly L r.iterate a := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hc
  refine ⟨⟨p,hp⟩,⟨3*p+p*(q+2)+3,?_⟩⟩
  intro i
  have hn : (a i).1≤p.eval (L i) := by
    have h := hp i
    simp only [prodCode_length,natCode,List.length_replicate] at h
    omega
  have ht := iterate_ticks_bound r (a i).2 (a i).1 (q.eval (L i)) (hq i)
  have ht' := ht.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change 3*(a i).1+2+IterateRoutine.loopTicks r.cost f (a i).1 (a i).2≤
    3*p.eval (L i)+p.eval (L i)*(q.eval (L i)+2)+3
  omega
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOriginalFields
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_accumMatrix _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_normalPencil _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_originalD : PolyTime originalD := by unfold originalD;apply poly_then
instance poly_originalRecords : PolyTime originalRecords := by unfold originalRecords;apply poly_then
instance poly_originalN : PolyTime originalN := by unfold originalN;apply poly_congr
instance poly_recordEntry (imag : Bool) : PolyTime (recordEntry imag) := by unfold recordEntry;apply poly_then
instance poly_recordCoordinate : PolyTime recordCoordinate := by unfold recordCoordinate;apply poly_congr
instance poly_recordCoordinates : PolyTime recordCoordinates := by unfold recordCoordinates;apply poly_then
instance poly_originalRecord : PolyTime originalRecord := by unfold originalRecord;apply poly_congr
instance poly_recordTrace : PolyTime recordTrace := by unfold recordTrace;apply poly_then
instance poly_originalTrace : PolyTime originalTrace := by unfold originalTrace;apply poly_congr
instance poly_originalTraces : PolyTime originalTraces := by unfold originalTraces;apply poly_tabulateFin
instance poly_originalScale : PolyTime originalScale := by unfold originalScale;apply poly_congr
instance poly_originalOrientation : PolyTime originalOrientation := by unfold originalOrientation;apply poly_congr
instance poly_nonzeroIndices : PolyTime nonzeroIndices := by unfold nonzeroIndices;apply poly_congr
instance poly_originalIndices : PolyTime originalIndices := by unfold originalIndices;apply poly_congr
instance poly_originalCountRealizes : PolyTime originalCountRealizes := by unfold originalCountRealizes;apply poly_congr
instance poly_originalIndex : PolyTime originalIndex := by unfold originalIndex;apply poly_changeOutput
instance poly_originalNormalizedMatrix : PolyTime originalNormalizedMatrix := by unfold originalNormalizedMatrix;apply poly_congr
instance poly_originalFaceRealizes : PolyTime originalFaceRealizes := by unfold originalFaceRealizes;apply poly_changeOutput
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialVariance
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

instance poly_mgN : PolyTime mgN := by unfold mgN;apply poly_then
instance poly_mgRest : PolyTime mgRest := by unfold mgRest;apply poly_then
instance poly_mgM : PolyTime mgM := by unfold mgM;apply poly_then
instance poly_mgDen : PolyTime mgDen := by unfold mgDen;apply poly_then
instance poly_mgShift : PolyTime mgShift := by unfold mgShift;apply poly_changeOutput
end CurrentKS.Realization

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Complexity_PolynomialOriginalSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

lemma originalFace_good (x : Input) (hx : Admissible x) (hn : originalCount x≠0) :
    (originalFace x).GoodAtoms := by
  have h := RationalInput.normalized_input_properties x hx hn
  exact ⟨RationalInput.dimension_ne x hx hn,hn,h.1,h.2.1,h.2.2.1,h.2.2.2⟩

variable {ι : Type*} {L : ι → ℕ}
lemma runsPoly_originalNormalizedSigns (a : ι → Input)
    (ha : IsPoly L (fun i => (originalCode (a i)).length))
    (hx : ∀i,Admissible (a i)) (hn : ∀i,originalCount (a i)≠0) :
    RunsPoly L originalNormalizedSigns a := by
  unfold originalNormalizedSigns
  apply RunsPoly.then_with (RunsPoly.of_poly originalFaceRealizes a ha)
  intro hi
  exact runsPoly_normalizedRun _ hi (fun i => originalFace_good (a i) (hx i) (hn i))

lemma runsPoly_originalExtendedSigns (a : ι → Input)
    (ha : IsPoly L (fun i => (originalCode (a i)).length))
    (hx : ∀i,Admissible (a i)) (hn : ∀i,originalCount (a i)≠0) :
    RunsPoly L originalExtendedSigns a := by
  unfold originalExtendedSigns
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.both
  · exact RunsPoly.of_poly _ a ha
  · exact (RunsPoly.of_poly _ a ha).both (runsPoly_originalNormalizedSigns a ha hx hn)

lemma runsPoly_originalOutputBit (a : ι → (Σ x : Input,Fin x.N))
    (ha : IsPoly L (fun i => (finFamilyCode originalCode Input.N (a i)).length))
    (hx : ∀i,Admissible (a i).1) (hn : ∀i,originalCount (a i).1≠0) :
    RunsPoly L originalOutputBit a := by
  have hp := RunsPoly.of_poly (familyFirst (ea:=originalCode) (n:=Input.N)) a ha
  have hs := hp.then (runsPoly_originalExtendedSigns _ hp.output hx hn)
  have hi := RunsPoly.of_poly (familyIndex (ea:=originalCode) (n:=Input.N)) a ha
  have hv := (hi.both hs).then_poly (getD ratCode 0)
  have hm := (RunsPoly.of_poly originalOrientation a ha).mul hv
  have hc := RunsPoly.of_poly (constant (finFamilyCode originalCode Input.N) ratCode 1) a ha
  unfold originalOutputBit Realizes.eq
  apply RunsPoly.congr
  apply RunsPoly.congr
  apply RunsPoly.ite
  · exact (hm.both hc).then_poly _
  · exact (hc.both hm).then_poly _
  · exact RunsPoly.of_poly _ a ha

lemma runsPoly_originalSigningFramed (a : ι → Input)
    (ha : IsPoly L (fun i => (originalCode (a i)).length))
    (hx : ∀i,Admissible (a i)) : RunsPoly L originalSigningFramed a := by
  have hb := RunsPoly.of_poly (originalCountRealizes.then natIsZero) a ha
  have ht := RunsPoly.of_poly (((constant originalCode boolCode true).both originalN).then (replicateList boolCode)) a ha
  have hs : RunsPoly (fun i : {i // originalCount (a i)≠0} => L i.val)
      (originalOutputBit.tabulateFin originalN) (fun i => a i.val) := by
    have hw := ha.reindex (fun i : {i // originalCount (a i)≠0} => i.val)
    apply runsPoly_tabulateFin_family _ _ _ hw
    exact runsPoly_originalOutputBit _ (isPoly_finFamily originalN _ hw)
      (fun i => hx i.1.val) (fun i => i.1.property)
  have hc : IsPoly L (fun i => if originalCount (a i)=0 then
      (((constant originalCode boolCode true).both originalN).then (replicateList boolCode)).cost (a i)
      else (originalOutputBit.tabulateFin originalN).cost (a i)) := by
    exact isPoly_dite (ht.cost.reindex (fun i : {i // originalCount (a i)=0} => i.val)) hs.cost
  unfold originalSigningFramed
  apply RunsPoly.congr
  apply hb.ite_on
  simpa only [decide_eq_true_eq] using hc
end CurrentKS.Realization

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_BinaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Binary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_binaryToRat : PolyTime binaryToRat := by unfold binaryToRat;infer_instance

instance poly_binaryDiv (d : ℕ) : PolyTime (binaryDiv d) := by unfold binaryDiv;infer_instance

instance poly_binaryMod (d : ℕ) : PolyTime (binaryMod d) := by unfold binaryMod;infer_instance

instance poly_binaryModUnary (d : ℕ) [hd : Fact (0<d)] : PolyTime (binaryModUnary d) := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=binaryMod d)
  refine ⟨⟨5*p+4*X+NaturalPolynomial.constant (6*d+4),?_⟩⟩
  intro n
  have ho := (binaryMod d).output_length n
  have hn := Nat.mod_lt n hd.out
  have hh := hp n
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤_
  change (binaryMod d).cost n+(6*(n%d)+4*(binaryNatCode (n%d)).length+4)≤
    5*p.eval (binaryNatCode n).length+4*(binaryNatCode n).length+(6*d+4)
  omega

instance poly_ratDenRat : PolyTime ratDenRat := by unfold ratDenRat;infer_instance

instance poly_scalarProductBinary : PolyTime scalarProductBinary := by
  unfold scalarProductBinary;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Squares
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational squares. -/

section

namespace AlgorithmicThinTrees.RationalGram
open CurrentKS.RationalBits

lemma base4Squares_length (k n : ℕ) : (base4Squares k n).length ≤ 3*k := by
  induction k generalizing n with
  | zero => simp [base4Squares]
  | succ k ih =>
    simp only [base4Squares,List.length_append,List.length_replicate,List.length_map]
    have hh := ih (n/4)
    have hd := Nat.mod_lt n (by decide : 0<4)
    omega

lemma base4Squares_entry (k n a : ℕ) (ha : a ∈ base4Squares k n) : a ≤ 2^k := by
  induction k generalizing n a with
  | zero => simp [base4Squares] at ha
  | succ k ih =>
    simp only [base4Squares,List.mem_append,List.mem_replicate,List.mem_map] at ha
    rcases ha with ⟨_,rfl⟩|⟨v,hv,rfl⟩
    · exact Nat.one_le_two_pow
    · rw [pow_succ]
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left 2 (ih (n/4) v hv)

lemma product_size {q : ℚ} {b : ℕ} (hq : Parts b q) :
    (q.num.natAbs*q.den).size ≤ 2*b+1 := by
  have h := Nat.mul_le_mul hq.1 hq.2
  rw [← pow_add] at h
  simpa only [Nat.size_pow,two_mul] using Nat.size_le_size h

lemma scalarFactors_length {q : ℚ} {b : ℕ} (hq : Parts b q) :
    (scalarFactors q).length ≤ 3*(2*b+1) := by
  rw [scalarFactors,List.length_map]
  exact (base4Squares_length _ _).trans (Nat.mul_le_mul_left 3 (product_size hq))

lemma scalarFactors_parts {q : ℚ} {b : ℕ} (hq : Parts b q)
    {v : ℚ} (hv : v ∈ scalarFactors q) : Parts (3*b+1) v := by
  rcases List.mem_map.mp hv with ⟨a,ha,rfl⟩
  have hanum := base4Squares_entry _ _ a ha
  have hb := product_size hq
  have hp : Parts (2*b+1) (a:ℚ) := by
    constructor
    · simpa using hanum.trans (Nat.pow_le_pow_right (by decide) hb)
    · simp [Nat.one_le_two_pow]
  have hd : Parts b (q.den:ℚ) := by
    constructor
    · simpa using hq.2
    · simp [Nat.one_le_two_pow]
  convert hp.div hd using 1
  all_goals try with_reducible_and_instances rfl
  omega

end AlgorithmicThinTrees.RationalGram
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_ScalarRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 AlgorithmicThinTrees.RationalGram
local notation "X" => NaturalPolynomial.variable

instance poly_squareScan : PolyTime squareScan := by
  let : Fact (0<4) := ⟨by decide⟩
  unfold squareScan
  apply poly_both

lemma squareScan_invariant (p : SquareScan) {b : ℕ}
    (hf : QParts b p.2.1) (hx : ∀v∈p.2.2,QParts b v) (k : ℕ) :
    let s := squareScanStep^[k] p
    s.1≤p.1 ∧ QParts (b+k) s.2.1 ∧ s.2.2.length≤p.2.2.length+3*k ∧
      ∀v∈s.2.2,QParts (b+k) v := by
  induction k with
  | zero => exact ⟨le_rfl,by simpa using hf,by simp,by simpa using hx⟩
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    dsimp only at ih ⊢
    generalize he : squareScanStep^[k] p=s at ih ⊢
    dsimp only [squareScanStep]
    refine ⟨(Nat.div_le_self _ _).trans ih.1,?_,?_,?_⟩
    · have htwo : QParts 1 (2:ℚ) := by norm_num [QParts]
      exact (htwo.mul ih.2.1).mono (by omega)
    · simp only [List.length_append,List.length_replicate]
      have hh := Nat.mod_lt s.1 (by decide : 0<4)
      omega
    · intro v hv
      simp only [List.mem_append,List.mem_replicate] at hv
      rcases hv with h|⟨_,rfl⟩
      · exact (ih.2.2.2 v h).mono (by omega)
      · exact ih.2.1.mono (by omega)

instance size_squareScan : IterateSize squareScan := by
  refine ⟨⟨100*(X+1)^2,?_⟩⟩
  intro p k
  let S := (squareScanCode p).length
  have hn := le_prodCode_left (ea:=binaryNatCode) (eb:=prodCode ratCode vectorCode) p
  have hr := le_prodCode_right (ea:=binaryNatCode) (eb:=prodCode ratCode vectorCode) p
  have hf := (le_prodCode_left p.2).trans hr
  have hx := (le_prodCode_right p.2).trans hr
  have hfx := (qparts_length p.2.1).mono hf
  have hxx : ∀v∈p.2.2,QParts S v := fun v hv =>
    (qparts_length v).mono ((mem_length_le_code p.2.2 hv).trans hx)
  obtain ⟨hN,hF,hX,hV⟩ := squareScan_invariant p hfx hxx k
  have hn' : (binaryNatCode (squareScanStep^[k] p).1).length≤S := by
    have h := Nat.size_le_size hN
    simpa only [binaryNatCode,KS.W01.natPayloadLength_eq_size,CurrentKS.payload_length]
      using h.trans (show p.1.size≤S by simpa only [binaryNatCode,CurrentKS.payload_length] using hn)
  have hl := (list_length_le_code ratCode p.2.2).trans hx
  have hb := (listCode_length_bound (squareScanStep^[k] p).2.2 (4*(S+k)+7)
    (fun v hv => (hV v hv).length)).trans
      (Nat.mul_le_mul_right _ (hX.trans (Nat.add_le_add_right hl _)))
  have hfl := hF.length
  change (squareScanCode (squareScanStep^[k] p)).length≤100*(S+k+1)^2
  simp only [squareScanCode,prodCode_length]
  change (ratCode (squareScanStep^[k] p).2.1).length≤4*(S+k)+7 at hfl
  change (vectorCode (squareScanStep^[k] p).2.2).length≤(S+3*k)*(2*(4*(S+k)+7)+1) at hb
  nlinarith only [hn',hb,hfl,Nat.zero_le S,Nat.zero_le k,sq_nonneg (S:ℤ),sq_nonneg (k:ℤ)]

instance poly_scalarFactorProgram : PolyTime scalarFactorProgram := by
  unfold scalarFactorProgram;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Arithmetic_UnaryArithmetic
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Unary arithmetic. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23
local notation "X" => NaturalPolynomial.variable

instance poly_natSub : PolyTime natSub := by unfold natSub;infer_instance

instance poly_natDivBinary : PolyTime natDivBinary := by unfold natDivBinary;infer_instance

instance poly_natDiv : PolyTime natDiv := by
  obtain ⟨p,hp⟩ := PolyTime.bound (r:=natDivBinary)
  refine ⟨⟨5*p+10*X+4,?_⟩⟩
  intro a
  have hc := hp a
  have ho := natDivBinary.output_length a
  have hn := Nat.div_le_self a.1 a.2
  have hl := le_prodCode_left (ea:=natCode) (eb:=natCode) a
  simp only [natCode,List.length_replicate] at hl
  change natDivBinary.cost a+(6*(a.1/a.2)+4*(binaryNatCode (a.1/a.2)).length+4)≤
    5*p.eval (prodCode natCode natCode a).length+10*(prodCode natCode natCode a).length+4
  omega

instance poly_natMod : PolyTime natMod := by unfold natMod;infer_instance

variable {α : Type*} {ea : α → Word} {f g : α → ℕ}
instance instPolyTimeNatNadd {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nadd s) := by unfold Realizes.nadd;infer_instance
instance instPolyTimeNatNmul {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmul s) := by unfold Realizes.nmul;infer_instance
instance instPolyTimeNatNsub {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nsub s) := by unfold Realizes.nsub;infer_instance
instance instPolyTimeNatNdiv {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.ndiv s) := by unfold Realizes.ndiv;infer_instance
instance instPolyTimeNatNmod {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nmod s) := by unfold Realizes.nmod;infer_instance
instance instPolyTimeBoolNeqOfNat {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.neq s) := by unfold Realizes.neq;infer_instance
instance instPolyTimeBoolNltOfNat {r : Realizes ea natCode f} {s : Realizes ea natCode g}
    [PolyTime r] [PolyTime s] : PolyTime (r.nlt s) := by unfold Realizes.nlt;infer_instance

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Normalization_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.CurrentKS.Realization.poly_matrixView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalization realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {β : Type*}

instance poly_selectFlagged (eb : β → Word) : PolyTime (selectFlagged eb) := by
  unfold selectFlagged
  infer_instance

end CurrentKS.Realization

namespace AlgorithmicThinTrees.Normalization.Stack
open CurrentKS CurrentKS.Realization CurrentKS.CleanRoutine KS.W23
open Matrix
instance poly_numColumns : PolyTime numColumns := by
  unfold numColumns
  apply poly_congr

instance poly_outer : PolyTime outer := by
  unfold outer
  infer_instance
instance poly_column : PolyTime column := by unfold column; apply poly_congr
instance poly_scale : PolyTime scale := by unfold scale; infer_instance

instance poly_updated : PolyTime updated := by unfold updated; apply poly_congr

instance poly_initial : PolyTime initial := by unfold initial; infer_instance

instance poly_unaryPow (k : ℕ) : PolyTime (unaryPow k) := by
  induction k with
  | zero => unfold unaryPow; apply poly_congr
  | succ k ih => unfold unaryPow; infer_instance

instance poly_multiplierProgram : PolyTime multiplierProgram := by
  unfold multiplierProgram; apply poly_sub

instance poly_fixedStep : PolyTime fixedStep := by unfold fixedStep; apply poly_changeOutput

instance poly_lengthProgram : PolyTime lengthProgram := by unfold lengthProgram; apply poly_then

end AlgorithmicThinTrees.Normalization.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Gram
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational gram. -/

section

namespace AlgorithmicThinTrees.RationalGram
open Matrix CurrentKS.RationalBits
variable {n : ℕ}

lemma trace_parts {N k t : ℕ} {M : Matrix (Fin N) (Fin N) ℚ}
    {p : Fin k → Fin N} {r : Fin t → Fin N} {S : Matrix (Fin t) (Fin t) ℚ}
    (h : KS.W07.PivotTrace M p r S) {b : ℕ} (hM : ∀ i j, Parts b (M i j)) :
    ∀ i j, Parts (KS.W30.inverseBitBound N b) (S i j) := by
  intro i j
  have hh := h.entry_parts_size_le b (fun i j => (hM i j).1) (fun i j => (hM i j).2) i j
  exact ⟨(Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hh.1),
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hh.2)⟩

lemma trace_factor_bounds {N : ℕ} (M : Matrix (Fin N) (Fin N) ℚ)
    (hPSD : (M.map (fun q : ℚ => (q:ℝ))).PosSemidef)
    {b : ℕ} (hM : ∀ i j, Parts b (M i j)) :
    ∀ {t k : ℕ} {p : Fin k → Fin N} {r : Fin t → Fin N}
      {S : Matrix (Fin t) (Fin t) ℚ}, KS.W07.PivotTrace M p r S →
      (factorColumns t S).length ≤ 3*t*(2*KS.W30.inverseBitBound N b+1) ∧
      ∀ v ∈ factorColumns t S, ∀ i, Parts (4*KS.W30.inverseBitBound N b+1) (v i) := by
  intro t
  induction t with
  | zero => intro k p r S h; simp [factorColumns]
  | succ t ih =>
    intro k p r S h
    let B := KS.W30.inverseBitBound N b
    have hp := h.state_posSemidef hPSD
    have hd : 0 ≤ S 0 0 := by
      have hh := hp.diag_nonneg (i:=0)
      simp only [Matrix.map_apply] at hh
      exact_mod_cast hh
    have hs : ∃k', ∃p' : Fin k' → Fin N,
        KS.W07.PivotTrace M p' (fun i => r i.succ) (KS.W17.schurTail S) := by
      by_cases hz : S 0 0=0
      · exact ⟨k,p,h.zero hz⟩
      · exact ⟨k+1,Fin.snoc p (r 0),h.positive (lt_of_le_of_ne hd (Ne.symm hz))⟩
    obtain ⟨k',p',hs⟩ := hs
    obtain ⟨hlen,hparts⟩ := ih hs
    have hS := trace_parts h hM
    have hb : Parts B (S 0 0)⁻¹ := (hS 0 0).inv
    have hlen' := scalarFactors_length hb
    constructor
    · simp only [factorColumns,List.length_append,List.length_map]
      change (scalarFactors (S 0 0)⁻¹).length+(factorColumns t (KS.W17.schurTail S)).length ≤
        3*(t+1)*(2*B+1)
      change (factorColumns t (KS.W17.schurTail S)).length ≤ 3*t*(2*B+1) at hlen
      nlinarith only [hlen,hlen']
    · intro v hv i
      simp only [factorColumns,List.mem_append,List.mem_map] at hv
      rcases hv with ⟨a,ha,rfl⟩|⟨u,hu,rfl⟩
      · have hq := (scalarFactors_parts hb ha).mul (hS i 0)
        change Parts (4*B+1) (a*S i 0)
        convert hq using 1
        all_goals try with_reducible_and_instances rfl
        omega
      · refine Fin.cases ?_ (fun j => hparts u hu j) i
        change Parts (4*B+1) 0
        simp [Parts,Nat.one_le_two_pow]

end AlgorithmicThinTrees.RationalGram
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_MatrixRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_column _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_fixedStep _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_initial _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_lengthProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_multiplierProgram _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_numColumns _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_outer _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_scale _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_unaryPow _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_updated _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binarySize _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_blockDiagonal _root_.OAI.CurrentKS.Realization.poly_blockScalar _root_.OAI.CurrentKS.Realization.poly_blockWith _root_.OAI.CurrentKS.Realization.poly_coordinateEntry _root_.OAI.CurrentKS.Realization.poly_coordinateIndexRealizes _root_.OAI.CurrentKS.Realization.poly_coordinates _root_.OAI.CurrentKS.Realization.poly_cuA _root_.OAI.CurrentKS.Realization.poly_cuH _root_.OAI.CurrentKS.Realization.poly_cuLast _root_.OAI.CurrentKS.Realization.poly_cuM _root_.OAI.CurrentKS.Realization.poly_cuMore _root_.OAI.CurrentKS.Realization.poly_cuN _root_.OAI.CurrentKS.Realization.poly_cuRest _root_.OAI.CurrentKS.Realization.poly_cuRho _root_.OAI.CurrentKS.Realization.poly_cuS _root_.OAI.CurrentKS.Realization.poly_cuScalars _root_.OAI.CurrentKS.Realization.poly_cuShift _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_curvatureView _root_.OAI.CurrentKS.Realization.poly_endpointCandidates _root_.OAI.CurrentKS.Realization.poly_endpointEntry _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_findValue _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_freezeScalar _root_.OAI.CurrentKS.Realization.poly_freezeVector _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_imEntry _root_.OAI.CurrentKS.Realization.poly_initialScale _root_.OAI.CurrentKS.Realization.poly_intCeil _root_.OAI.CurrentKS.Realization.poly_lowerBox _root_.OAI.CurrentKS.Realization.poly_matrixSub _root_.OAI.CurrentKS.Realization.poly_matrixVariable _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natLT _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nearest _root_.OAI.CurrentKS.Realization.poly_nearestMesh _root_.OAI.CurrentKS.Realization.poly_negateMatrix _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_optB _root_.OAI.CurrentKS.Realization.poly_optDelta _root_.OAI.CurrentKS.Realization.poly_optF _root_.OAI.CurrentKS.Realization.poly_optLevel _root_.OAI.CurrentKS.Realization.poly_optLevelPencil _root_.OAI.CurrentKS.Realization.poly_optRadius _root_.OAI.CurrentKS.Realization.poly_optRest _root_.OAI.CurrentKS.Realization.poly_optScalars _root_.OAI.CurrentKS.Realization.poly_optStateView _root_.OAI.CurrentKS.Realization.poly_optUpper _root_.OAI.CurrentKS.Realization.poly_optView _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_osK _root_.OAI.CurrentKS.Realization.poly_osP _root_.OAI.CurrentKS.Realization.poly_osY _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenBinary _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_ratDenSize _root_.OAI.CurrentKS.Realization.poly_ratFields _root_.OAI.CurrentKS.Realization.poly_ratNumBinary _root_.OAI.CurrentKS.Realization.poly_reEntry _root_.OAI.CurrentKS.Realization.poly_realDecode _root_.OAI.CurrentKS.Realization.poly_realDimension _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_replicateList _root_.OAI.CurrentKS.Realization.poly_roundMesh _root_.OAI.CurrentKS.Realization.poly_roundedUpdate _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_sandwich _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_scaleMatrix _root_.OAI.CurrentKS.Realization.poly_searchDim _root_.OAI.CurrentKS.Realization.poly_searchInit _root_.OAI.CurrentKS.Realization.poly_searchMesh _root_.OAI.CurrentKS.Realization.poly_searchParameters _root_.OAI.CurrentKS.Realization.poly_searchPencil _root_.OAI.CurrentKS.Realization.poly_searchStep _root_.OAI.CurrentKS.Realization.poly_searchView _root_.OAI.CurrentKS.Realization.poly_searchY _root_.OAI.CurrentKS.Realization.poly_selectFlagged _root_.OAI.CurrentKS.Realization.poly_singletonList _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_squareSum _root_.OAI.CurrentKS.Realization.poly_squareTabulate _root_.OAI.CurrentKS.Realization.poly_stateParameters _root_.OAI.CurrentKS.Realization.poly_statePencil _root_.OAI.CurrentKS.Realization.poly_stateView _root_.OAI.CurrentKS.Realization.poly_stateY _root_.OAI.CurrentKS.Realization.poly_tinyMatrix _root_.OAI.CurrentKS.Realization.poly_traceMatrix _root_.OAI.CurrentKS.Realization.poly_unframeNat _root_.OAI.CurrentKS.Realization.poly_updateVector _root_.OAI.CurrentKS.Realization.poly_upperBox _root_.OAI.CurrentKS.Realization.poly_valueDimension _root_.OAI.CurrentKS.Realization.poly_valueInnerRadius _root_.OAI.CurrentKS.Realization.poly_valueLipschitz _root_.OAI.CurrentKS.Realization.poly_valueObjective _root_.OAI.CurrentKS.Realization.poly_valueOuterRadius _root_.OAI.CurrentKS.Realization.poly_vdAtoms _root_.OAI.CurrentKS.Realization.poly_vdD _root_.OAI.CurrentKS.Realization.poly_vdEps _root_.OAI.CurrentKS.Realization.poly_vdParams _root_.OAI.CurrentKS.Realization.poly_vdRest _root_.OAI.CurrentKS.Realization.poly_vdTheta _root_.OAI.CurrentKS.Realization.poly_vdX _root_.OAI.CurrentKS.Realization.poly_veD _root_.OAI.CurrentKS.Realization.poly_veEps _root_.OAI.CurrentKS.Realization.poly_veEye _root_.OAI.CurrentKS.Realization.poly_veN _root_.OAI.CurrentKS.Realization.poly_veP _root_.OAI.CurrentKS.Realization.poly_veTime _root_.OAI.CurrentKS.Realization.poly_veVariable _root_.OAI.CurrentKS.Realization.poly_veY _root_.OAI.CurrentKS.Realization.poly_vectorDivide _root_.OAI.CurrentKS.Realization.poly_vectorNeg _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_vqData _root_.OAI.CurrentKS.Realization.poly_vqDelta _root_.OAI.CurrentKS.Realization.poly_vqView _root_.OAI.CurrentKS.Realization.poly_withLevel _root_.OAI.CurrentKS.Realization.poly_witnessStateView _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.poly_wordLength _root_.OAI.CurrentKS.Realization.poly_wordTail _root_.OAI.CurrentKS.Realization.poly_zeroRect _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.Normalization.Stack.poly_view _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Matrix realization. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}

lemma runsPoly_fold_of_poly {f : α×β → α}
    (r : Realizes (prodCode ea eb) ea f) [PolyTime r] (a : ι → α×List β)
    (ha : IsPoly L (fun i => (prodCode ea (listCode eb) (a i)).length))
    (hs : ∃q : NaturalPolynomial,∀i ys zs,(a i).2=ys++zs →
      (ea (ys.foldl (fun s x => f (s,x)) (a i).1)).length≤q.eval (L i)) :
    RunsPoly L r.fold a := by
  obtain ⟨p,hp⟩ := ha
  obtain ⟨q,hq⟩ := hs
  obtain ⟨t,ht⟩ := PolyTime.bound (r:=r)
  refine ⟨⟨p,hp⟩,⟨5*q+2*p+p*(3*p+10*q+t.comp (2*q+1+p)+12)+7,?_⟩⟩
  intro i
  let E := p.eval (L i)
  let S := q.eval (L i)
  have he : (listCode eb (a i).2).length≤E := (le_prodCode_right (a i)).trans (hp i)
  have hn := (list_length_le_code eb (a i).2).trans he
  have h0 := hq i [] (a i).2 rfl
  have hN := hq i (a i).2 [] (by simp)
  have hc : ∀s x,(ea s).length≤S → (eb x).length≤E → r.cost (s,x)≤t.eval (2*S+1+E) := by
    intro s x hs hx
    apply (ht (s,x)).trans (t.eval_mono ?_)
    rw [prodCode_length]
    dsimp only
    omega
  have hscan := fold_scan_bound (ea:=ea) (eb:=eb) (fun s x => f (s,x)) r.cost (a i).1
    (a i).2 S E (t.eval (2*S+1+E)) (hq i)
    (fun x hx => (mem_length_le_code (a i).2 hx).trans he) hc
  have hscan' := hscan.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hn) 1)
  change FoldRoutine.ticks ea eb (fun s x => f (s,x)) r.cost (a i).1 (a i).2≤_
  simp only [FoldRoutine.ticks]
  simp only [NaturalPolynomial.eval_add,NaturalPolynomial.eval_mul,
    NaturalPolynomial.eval_comp]
  change _≤5*S+2*E+E*(3*E+10*S+t.eval (2*S+1+E)+12)+7
  change (ea (a i).1).length≤S at h0
  change (ea ((a i).2.foldl (fun s x => f (s,x)) (a i).1)).length≤S at hN
  change (FramedMapRoutine.tape eb (a i).2).length≤E at he
  omega

lemma matrixCode_parts_bound {n m b : ℕ} (A : Matrix (Fin n) (Fin m) ℚ)
    (h : ∀i j,QParts b (A i j)) :
    (matrixCode (matrixData A)).length≤n*(2*(m*(2*(4*b+7)+1))+1) := by
  apply (listCode_length_bound (matrixData A) (m*(2*(4*b+7)+1)) ?_).trans_eq
    (by rw [show (matrixData A).length=n from List.length_ofFn])
  intro row hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  apply (listCode_length_bound (List.ofFn (A i)) (4*b+7) ?_).trans_eq
    (by rw [List.length_ofFn])
  intro q hq
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
  exact (h i j).length

lemma matrixObject_dim_le (a : MatrixObject) : a.1≤(matrixObjectCode a).length :=
  by simpa only [prodCode, matrixObjectCode, natCode,List.length_replicate] using
    (le_prodCode_left (ea:=natCode) (eb:=matrixCode) (a.1,matrixData a.2))

lemma matrixObject_parts (a : MatrixObject) :
    ∀i j,QParts (matrixObjectCode a).length (a.2 i j) := by
  intro i j
  apply (qparts_length _).mono
  exact ((mem_length_le_code (List.ofFn (a.2 i)) (List.mem_ofFn.mpr ⟨j,rfl⟩)).trans
    (mem_length_le_code (matrixData a.2) (List.mem_ofFn.mpr ⟨i,rfl⟩))).trans
      (le_prodCode_right (a.1,matrixData a.2))

lemma matrixObject_parts_bound (a : MatrixObject) {b N : ℕ}
    (hn : a.1≤N) (h : ∀i j,QParts b (a.2 i j)) :
    (matrixObjectCode a).length≤2*N+1+N*(2*(N*(2*(4*b+7)+1))+1) := by
  have hb := matrixCode_parts_bound a.2 h
  have hm := Nat.mul_le_mul hn (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right (2*(4*b+7)+1) hn)) 1)
  simp only [matrixObjectCode,prodCode_length,natCode,List.length_replicate]
  change 2*a.1+1+(matrixCode (matrixData a.2)).length≤_
  omega

instance poly_schurEntry : PolyTime schurEntry := by unfold schurEntry; apply poly_sub

instance poly_schur : PolyTime schur := by unfold schur; apply poly_changeOutput

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_SchurHistory
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Schur history. -/

section


namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

lemma SchurDesc.refl (a : MatrixObject) : SchurDesc a a :=
  ⟨0,(fun i => Fin.elim0 i),id,KS.W07.PivotTrace.initial⟩

lemma SchurDesc.dim {a b : MatrixObject} (h : SchurDesc a b) : b.1≤a.1 := by
  obtain ⟨k,p,r,h⟩ := h
  have hh := h.size_bound
  omega

lemma SchurDesc.schur {a b : MatrixObject} (h : SchurDesc a b)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) : SchurDesc a (schurData b) := by
  rcases b with ⟨d,B⟩
  cases d with
  | zero => exact h
  | succ d =>
    obtain ⟨k,p,r,h⟩ := h
    by_cases hz : B 0 0=0
    · exact ⟨k,p,(fun i => r i.succ),h.zero hz⟩
    · have hh := (h.state_posSemidef hA).diag_nonneg (i:=0)
      change (0 : ℝ) ≤ (B 0 0:ℝ) at hh
      have hq : 0 ≤ B 0 0 := by exact_mod_cast hh
      exact ⟨k+1,Fin.snoc p (r 0),(fun i => r i.succ),h.positive (lt_of_le_of_ne hq (Ne.symm hz))⟩

lemma SchurDesc.wire {a b : MatrixObject} (h : SchurDesc a b) :
    (matrixObjectCode b).length ≤
      2*a.1+1+a.1*(2*(a.1*(2*(4*KS.W30.inverseBitBound a.1 (matrixObjectCode a).length+7)+1))+1) := by
  have hn := h.dim
  obtain ⟨k,p,r,h⟩ := h
  exact matrixObject_parts_bound b hn (RationalGram.trace_parts h (matrixObject_parts a))

instance poly_schurNext : PolyTime schurNext := by unfold schurNext; infer_instance

lemma schurHistory_length (a : MatrixObject) : (schurHistoryData a).length=a.1 := by
  rcases a with ⟨d,A⟩
  induction d with
  | zero => simp [schurHistoryData]
  | succ d ih => simp [schurHistoryData,ih]

lemma schurNext_invariant (a : MatrixObject)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) (j : ℕ) :
    let s := schurNextData^[j] (a,[])
    SchurDesc a s.1 ∧ (∀b∈s.2,SchurDesc a b) ∧ s.2.length≤j := by
  induction j with
  | zero => exact ⟨SchurDesc.refl a,by simp,by simp⟩
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    dsimp only
    dsimp only at ih
    generalize he : schurNextData^[j] (a,[])=s at ih ⊢
    unfold schurNextData
    split_ifs with hz
    · exact ⟨ih.1,ih.2.1,by omega⟩
    · refine ⟨ih.1.schur hA,?_,?_⟩
      · simpa only [List.mem_cons,forall_eq_or_imp] using And.intro ih.1 ih.2.1
      · simp only [List.length_cons];omega

lemma schurHistory_mem (a : MatrixObject)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    ∀b∈schurHistoryData a, SchurDesc a b := by
  have h := (schurNext_invariant a hA a.1).2.1
  simpa only [schurHistory_iterate,List.append_nil] using h

lemma runsPoly_schurHistory {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i, ((a i).2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    RunsPoly L schurHistory a := by
  let dim := fun i => (a i).1
  let bits := fun i => (matrixObjectCode (a i)).length
  have hd : IsPoly L dim := ha.mono (fun i => matrixObject_dim_le (a i))
  have hi : IsPoly L (fun i => KS.W30.inverseBitBound (dim i) (bits i)) := by
    apply (((isPoly_const L 6).mul (ha.add (isPoly_const L 1))).mul
      ((hd.add (isPoly_const L 1)).pow 3)).mono
    exact fun i => KS.W30.inverseBitBound_le_polynomial _ _
  have hb := (((isPoly_const L 2).mul hd).add (isPoly_const L 1)).add
    (hd.mul (((isPoly_const L 2).mul (hd.mul (((isPoly_const L 2).mul
      (((isPoly_const L 4).mul hi).add (isPoly_const L 7))).add (isPoly_const L 1)))).add (isPoly_const L 1)))
  obtain ⟨p,hp⟩ := hb
  have hs : IsPoly (fun s : {s : ι×ℕ // s.2<(a s.1).1} => L s.val.1)
      (fun s => (schurStackCode (schurNextData^[s.val.2] (a s.val.1,[]))).length) := by
    have hpoly := (((isPoly_const L 2).mul (show IsPoly L (fun i => p.eval (L i)) from ⟨p,fun _ => le_rfl⟩)).add (isPoly_const L 1)).add
      (hd.mul (((isPoly_const L 2).mul (show IsPoly L (fun i => p.eval (L i)) from ⟨p,fun _ => le_rfl⟩)).add (isPoly_const L 1)))
    apply (hpoly.reindex (fun s : {s : ι×ℕ // s.2<(a s.1).1} => s.val.1)).mono
    intro s
    obtain ⟨hc,ho,hl⟩ := schurNext_invariant (a s.val.1) (hA s.val.1) s.val.2
    have hb : ∀b, SchurDesc (a s.val.1) b → (matrixObjectCode b).length≤p.eval (L s.val.1) :=
      fun b h => h.wire.trans (hp s.val.1)
    have hcur := hb _ hc
    have hlist := listCode_length_bound _ (p.eval (L s.val.1)) (fun b h => hb b (ho b h))
    have hlen : (schurNextData^[s.val.2] (a s.val.1,[])).2.length≤dim s.val.1 :=
      hl.trans s.property.le
    have hlist' := hlist.trans (Nat.mul_le_mul_right _ hlen)
    dsimp only [dim] at hlist'
    simp only [schurStackCode,prodCode_length]
    dsimp only [Function.comp_apply,dim]
    omega
  unfold schurHistory
  apply RunsPoly.congr
  apply RunsPoly.then_poly
  apply RunsPoly.then_with (RunsPoly.of_poly _ a ha)
  intro hw
  apply runsPoly_iterate _ _ hw
  obtain ⟨q,hq⟩ := (RunsPoly.of_poly schurNext _ hs).cost
  exact ⟨q,fun i j hj => hq ⟨(i,j),hj⟩⟩

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Encoding_GraphRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Graph realization. -/

section

namespace AlgorithmicThinTrees.GraphStack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.MetricTests.RationalStep
open scoped BigOperators

instance poly_numEdges : PolyTime numEdges := by unfold numEdges;apply poly_congr

instance poly_edgeLeft : PolyTime edgeLeft := by unfold edgeLeft;apply poly_congr
instance poly_edgeRight : PolyTime edgeRight := by unfold edgeRight;apply poly_congr

instance poly_constantMatrix : PolyTime constantMatrix := by unfold constantMatrix;infer_instance

instance poly_projection : PolyTime projection := by unfold projection;infer_instance

instance poly_response : PolyTime response := by unfold response;infer_instance

end AlgorithmicThinTrees.GraphStack

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix
open scoped BigOperators

instance poly_dimensionProgram : PolyTime dimensionProgram := by
  unfold dimensionProgram Realizes.nadd
  apply poly_then

instance poly_rawEntry : PolyTime rawEntry := by unfold rawEntry;infer_instance

instance poly_raw : PolyTime raw := by unfold raw;infer_instance

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_FiniteFamilies
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_response _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite families. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {α β : Type*} {ea : α → Word} {eb : β → Word}
variable {I J : α → Type*} {n m : α → ℕ}

instance poly_indexedFirst (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedFirst (ea:=ea) e) := by unfold indexedFirst;apply poly_reindex
instance poly_indexedIndex (e : (a : α) → I a ≃ Fin (n a)) :
    PolyTime (indexedIndex (ea:=ea) e) := by unfold indexedIndex;apply poly_reindex

instance poly_tabulateIndexed {e : (a : α) → I a ≃ Fin (n a)} {f : (Σ a,I a) → β}
    (r : Realizes (indexedCode ea e) eb f) (rn : Realizes ea natCode n)
    [PolyTime r] [PolyTime rn] : PolyTime (r.tabulateIndexed rn) := by
  unfold Realizes.tabulateIndexed
  refine @poly_tabulateFin _ _ _ _ _ _ _ _ ?_ ?_
  · apply poly_reindex
  · infer_instance

instance poly_indexedSumTest (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumTest e e' rn) := by unfold indexedSumTest;infer_instance

instance poly_indexedSumRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rn : Realizes ea natCode n) [PolyTime rn] :
    PolyTime (indexedSumRight e e' rn) := by unfold indexedSumRight;infer_instance

instance poly_splitProduct (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (splitProduct e e' rm) := by unfold splitProduct;infer_instance

instance poly_indexedProductLeft (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductLeft e e' rm) := by unfold indexedProductLeft;infer_instance

instance poly_indexedProductRight (e : (a : α) → I a ≃ Fin (n a))
    (e' : (a : α) → J a ≃ Fin (m a)) (rm : Realizes ea natCode m) [PolyTime rm] :
    PolyTime (indexedProductRight e e' rm) := by unfold indexedProductRight;apply poly_changeOutput

instance poly_not {P : α → Prop} [DecidablePred P]
    (r : Realizes ea boolCode (fun a => decide (P a))) [PolyTime r] : PolyTime r.not := by
  unfold Realizes.not;infer_instance

instance poly_and {P Q : α → Prop} [DecidablePred P] [DecidablePred Q]
    (r : Realizes ea boolCode (fun a => decide (P a)))
    (s : Realizes ea boolCode (fun a => decide (Q a))) [PolyTime r] [PolyTime s] : PolyTime (r.and s) := by
  unfold Realizes.and;infer_instance

instance poly_finEq {n : α → ℕ} {f g : (a : α) → Fin (n a)}
    (r : Realizes ea natCode (fun a => (f a).val))
    (s : Realizes ea natCode (fun a => (g a).val)) [PolyTime r] [PolyTime s] :
    PolyTime (r.finEq s) := by unfold Realizes.finEq;infer_instance
end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil parameters. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators

private instance poly_paramsGraph : PolyTime paramsGraph := by
  unfold paramsGraph
  apply poly_then

private instance poly_paramsN : PolyTime paramsN := by
  unfold paramsN
  refine @poly_then _ _ _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · unfold numVertices
    apply poly_then

private instance poly_paramsM : PolyTime paramsM := by
  unfold paramsM
  apply poly_then

instance poly_paramsField (k : ℕ) : PolyTime (paramsField k) := by unfold paramsField;apply poly_then
private instance poly_pointParams : PolyTime pointParams := by
  unfold pointParams
  apply poly_then

instance poly_pointParser : PolyTime pointParser := by
  have : PolyTime paramsDim := by unfold paramsDim; apply poly_then
  unfold pointParser
  apply poly_changeOutput

variable {α : Type*} {ea : α → Word} {p : α → Point}
instance poly_coordinate (rp : Realizes ea pointCode p)
    (i : (a : α) → Fin (dimension (p a).p.graph.n (p a).p.graph.m))
    (ri : Realizes ea natCode (fun a => (i a).val)) [PolyTime rp] [PolyTime ri] :
    PolyTime (coordinate rp i ri) := by unfold coordinate;apply poly_congr

instance poly_rawPoint : PolyTime rawPoint := by
  have : PolyTime pointN := by unfold pointN; apply poly_then
  have : PolyTime pointM := by unfold pointM; apply poly_then
  unfold rawPoint
  apply poly_changeOutput
end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Pencil_PointPrograms
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Point programs. -/

section

namespace CurrentKS.Realization
open CleanRoutine
variable {α β : Type*} {ea : α → Word} {eb : β → Word}
instance poly_cons {f : α → β} {g : α → List β}
    (r : Realizes ea eb f) (s : Realizes ea (listCode eb) g) [PolyTime r] [PolyTime s] :
    PolyTime (r.cons s) := by unfold Realizes.cons;infer_instance

instance poly_select3 {i : α → Fin 3} (ri : Realizes ea natCode (fun a => (i a).val))
    {f g h : α → ℚ} (r : Realizes ea ratCode f) (s : Realizes ea ratCode g)
    (t : Realizes ea ratCode h) [PolyTime ri] [PolyTime r] [PolyTime s] [PolyTime t] :
    PolyTime (select3 ri r s t) := by unfold select3;apply poly_congr

instance poly_select7 {i : α → Fin 7} (ri : Realizes ea natCode (fun a => (i a).val))
    {f₀ f₁ f₂ f₃ f₄ f₅ f₆ : α → ℚ}
    (r₀ : Realizes ea ratCode f₀) (r₁ : Realizes ea ratCode f₁) (r₂ : Realizes ea ratCode f₂)
    (r₃ : Realizes ea ratCode f₃) (r₄ : Realizes ea ratCode f₄) (r₅ : Realizes ea ratCode f₅)
    (r₆ : Realizes ea ratCode f₆) [PolyTime ri] [PolyTime r₀] [PolyTime r₁] [PolyTime r₂]
    [PolyTime r₃] [PolyTime r₄] [PolyTime r₅] [PolyTime r₆] :
    PolyTime (select7 ri r₀ r₁ r₂ r₃ r₄ r₅ r₆) := by unfold select7;apply poly_congr
end CurrentKS.Realization

namespace AlgorithmicThinTrees.MetricTests.RationalStep.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix StrongThinTree
open AlgorithmicThinTrees.GraphStack
open scoped BigOperators
variable {α : Type*} {ea : α → Word} {a : α → Point}

instance poly_storedU (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (storedU r e re) := by unfold storedU;apply poly_congr

instance poly_graphEdge (r : Realizes ea pointCode a)
    (e : (b : α) → Fin (a b).p.graph.m) (re : Realizes ea natCode (fun b => (e b).val))
    [PolyTime r] [PolyTime re] : PolyTime (graphEdge r e re) := by unfold graphEdge;apply poly_changeOutput

instance poly_tripleDistinct : PolyTime tripleDistinct := by
  have : PolyTime tripleI := by infer_instance
  have : PolyTime tripleJ := by infer_instance
  have : PolyTime tripleK := by infer_instance
  unfold tripleDistinct
  refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
  · infer_instance
  · refine @poly_and _ _ _ _ _ _ _ _ ?_ ?_
    · infer_instance
    · apply poly_not

end AlgorithmicThinTrees.MetricTests.RationalStep.Stack
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_Inverse
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational inverse. -/

section


namespace AlgorithmicThinTrees.RationalInverse
open Matrix Finset
variable {n : ℕ}

lemma posDef_of_cast (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosDef) : A.PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos
  · exact (isHermitian_iff_isSymm.mpr (KS.W07.rational_isSymm_of_cast_posSemidef hA.posSemidef))
  · intro x hx
    have hx' : (fun i => (x i:ℝ)) ≠ 0 := by
      intro he
      apply hx
      funext i
      have hh := congrFun he i
      change (x i:ℝ)=0 at hh
      change x i=0
      exact_mod_cast hh
    have hh := hA.dotProduct_mulVec_pos hx'
    simp only [star_trivial,dotProduct,mulVec,map_apply] at hh ⊢
    exact_mod_cast hh

lemma schur_posDef (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : A.PosDef) : (KS.W17.schurTail A).PosDef := by
  have hs : A.IsSymm := isHermitian_iff_isSymm.mp hA.isHermitian
  apply PosDef.of_dotProduct_mulVec_pos
  · exact isHermitian_iff_isSymm.mpr (KS.W17.schurTail_isSymm A hs)
  · intro x hx
    have hlift : KS.W17.schurWitnessLift A x ≠ 0 := by
      intro h
      apply hx
      funext i
      exact congrFun h i.succ
    simpa only [star_trivial,KS.W07.fin_schurWitnessLift_quadratic A hs hA.diag_pos.ne'] using
      hA.dotProduct_mulVec_pos hlift

lemma liftSolve_correct (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (B : Matrix (Fin n) (Fin n) ℚ) (b : Fin (n+1) → ℚ)
    (hp : A 0 0 ≠ 0) (hB : KS.W17.schurTail A*B=1) :
    A*ᵥliftSolve A B b=b := by
  let y := B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0))
  have hy : KS.W17.schurTail A*ᵥy=(fun i => b i.succ-A i.succ 0*(b 0/A 0 0)) := by
    rw [show y=B*ᵥ(fun i => b i.succ-A i.succ 0*(b 0/A 0 0)) from rfl,
      Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]
  ext i
  rw [mulVec,dotProduct,Fin.sum_univ_succ]
  change A i 0*((b 0-(fun j => A 0 j.succ) ⬝ᵥ y)/A 0 0)+
    ∑j, A i j.succ*y j=b i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [mul_div_cancel₀ _ hp]
    simp only [dotProduct]
    ring
  · have he := congrFun hy i
    change (∑j, (A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0)*y j)=
      b i.succ-A i.succ 0*(b 0/A 0 0) at he
    have he' : (∑j, A i.succ j.succ*y j)-
        A i.succ 0*(A 0 0)⁻¹*((fun j => A 0 j.succ) ⬝ᵥ y)=
      b i.succ-A i.succ 0*(b 0/A 0 0) := by
      have hsum : (∑j, (A i.succ j.succ-A i.succ 0*A 0 j.succ/A 0 0)*y j)=
          (∑j, A i.succ j.succ*y j)-
          A i.succ 0*(A 0 0)⁻¹*((fun j => A 0 j.succ) ⬝ᵥ y) := by
        simp only [dotProduct,mul_sum,←sum_sub_distrib]
        apply sum_congr rfl
        intro j hj
        ring
      rwa [hsum] at he
    simp only [div_eq_mul_inv]
    linear_combination he'

lemma inverse_mul_correct : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℚ),
    A.PosDef → A*inverse n A=1 := by
  intro n
  induction n with
  | zero => intro A hA;ext i;exact Fin.elim0 i
  | succ n ih =>
    intro A hA
    have hB := ih (KS.W17.schurTail A) (schur_posDef A hA)
    ext i j
    have hh := congrFun (liftSolve_correct A (inverse n (KS.W17.schurTail A))
      (Pi.single j 1) hA.diag_pos.ne' hB) i
    simpa only [inverse,Matrix.mul_apply,Matrix.mulVec,dotProduct,Pi.single_apply,
      one_apply,eq_comm] using! hh

lemma inverse_eq (A : Matrix (Fin n) (Fin n) ℚ) (hA : A.PosDef) : inverse n A=A⁻¹ := by
  exact (inv_eq_right_inv (inverse_mul_correct n A hA)).symm

lemma inverse_eq_of_cast (A : Matrix (Fin n) (Fin n) ℚ)
    (hA : (A.map (fun q : ℚ => (q:ℝ))).PosDef) : inverse n A=A⁻¹ :=
  inverse_eq A (posDef_of_cast A hA)

end AlgorithmicThinTrees.RationalInverse
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_RationalMatrix_InverseRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_constantMatrix _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeLeft _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_edgeRight _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_numEdges _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_projection _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_response _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_coordinate _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_dimensionProgram _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_graphEdge _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsField _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParser _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_raw _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawEntry _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_rawPoint _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_storedU _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_tripleDistinct _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNeqOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeBoolNltOfNat _root_.OAI.CurrentKS.Realization.instPolyTimeNatNadd _root_.OAI.CurrentKS.Realization.instPolyTimeNatNdiv _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmod _root_.OAI.CurrentKS.Realization.instPolyTimeNatNmul _root_.OAI.CurrentKS.Realization.instPolyTimeNatNsub _root_.OAI.CurrentKS.Realization.poly_activeIndices _root_.OAI.CurrentKS.Realization.poly_and _root_.OAI.CurrentKS.Realization.poly_binaryDiv _root_.OAI.CurrentKS.Realization.poly_binaryMod _root_.OAI.CurrentKS.Realization.poly_binaryModUnary _root_.OAI.CurrentKS.Realization.poly_binaryToRat _root_.OAI.CurrentKS.Realization.poly_cons _root_.OAI.CurrentKS.Realization.poly_curvatureCandidates _root_.OAI.CurrentKS.Realization.poly_extendEntry _root_.OAI.CurrentKS.Realization.poly_extendVector _root_.OAI.CurrentKS.Realization.poly_fArgs _root_.OAI.CurrentKS.Realization.poly_fAtoms _root_.OAI.CurrentKS.Realization.poly_fBase _root_.OAI.CurrentKS.Realization.poly_fD _root_.OAI.CurrentKS.Realization.poly_fIndices _root_.OAI.CurrentKS.Realization.poly_fLam _root_.OAI.CurrentKS.Realization.poly_fN _root_.OAI.CurrentKS.Realization.poly_fNu _root_.OAI.CurrentKS.Realization.poly_fRest _root_.OAI.CurrentKS.Realization.poly_fScalars _root_.OAI.CurrentKS.Realization.poly_fSchedule _root_.OAI.CurrentKS.Realization.poly_fState _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faP _root_.OAI.CurrentKS.Realization.poly_facePointView _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_faceView _root_.OAI.CurrentKS.Realization.poly_fdI _root_.OAI.CurrentKS.Realization.poly_fdJ _root_.OAI.CurrentKS.Realization.poly_fdP _root_.OAI.CurrentKS.Realization.poly_fdS _root_.OAI.CurrentKS.Realization.poly_fiI _root_.OAI.CurrentKS.Realization.poly_fiP _root_.OAI.CurrentKS.Realization.poly_finEq _root_.OAI.CurrentKS.Realization.poly_fpExtend _root_.OAI.CurrentKS.Realization.poly_fpP _root_.OAI.CurrentKS.Realization.poly_fpPotential _root_.OAI.CurrentKS.Realization.poly_fpY _root_.OAI.CurrentKS.Realization.poly_gather _root_.OAI.CurrentKS.Realization.poly_indexedFirst _root_.OAI.CurrentKS.Realization.poly_indexedIndex _root_.OAI.CurrentKS.Realization.poly_indexedProductLeft _root_.OAI.CurrentKS.Realization.poly_indexedProductRight _root_.OAI.CurrentKS.Realization.poly_indexedSumRight _root_.OAI.CurrentKS.Realization.poly_indexedSumTest _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_movementBudget _root_.OAI.CurrentKS.Realization.poly_natDiv _root_.OAI.CurrentKS.Realization.poly_natDivBinary _root_.OAI.CurrentKS.Realization.poly_natMod _root_.OAI.CurrentKS.Realization.poly_natSub _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_not _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_parameterField _root_.OAI.CurrentKS.Realization.poly_parameters _root_.OAI.CurrentKS.Realization.poly_parameters_singleton _root_.OAI.CurrentKS.Realization.poly_potentialView _root_.OAI.CurrentKS.Realization.poly_ppArgs _root_.OAI.CurrentKS.Realization.poly_ppAtoms _root_.OAI.CurrentKS.Realization.poly_ppD _root_.OAI.CurrentKS.Realization.poly_ppError _root_.OAI.CurrentKS.Realization.poly_ppLam _root_.OAI.CurrentKS.Realization.poly_ppN _root_.OAI.CurrentKS.Realization.poly_ppNu _root_.OAI.CurrentKS.Realization.poly_ppRest _root_.OAI.CurrentKS.Realization.poly_ppRootTolerance _root_.OAI.CurrentKS.Realization.poly_ppScalars _root_.OAI.CurrentKS.Realization.poly_ppX _root_.OAI.CurrentKS.Realization.poly_ratDenRat _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_saBudget _root_.OAI.CurrentKS.Realization.poly_saCoarse _root_.OAI.CurrentKS.Realization.poly_saCurve2 _root_.OAI.CurrentKS.Realization.poly_saCurve3 _root_.OAI.CurrentKS.Realization.poly_saD _root_.OAI.CurrentKS.Realization.poly_saEpsilon _root_.OAI.CurrentKS.Realization.poly_saLam _root_.OAI.CurrentKS.Realization.poly_saMesh _root_.OAI.CurrentKS.Realization.poly_saN _root_.OAI.CurrentKS.Realization.poly_saNu _root_.OAI.CurrentKS.Realization.poly_saRest _root_.OAI.CurrentKS.Realization.poly_saScalars _root_.OAI.CurrentKS.Realization.poly_saSigma _root_.OAI.CurrentKS.Realization.poly_saStencil _root_.OAI.CurrentKS.Realization.poly_saStep _root_.OAI.CurrentKS.Realization.poly_saThreshold _root_.OAI.CurrentKS.Realization.poly_scalarFactorProgram _root_.OAI.CurrentKS.Realization.poly_scalarProductBinary _root_.OAI.CurrentKS.Realization.poly_select3 _root_.OAI.CurrentKS.Realization.poly_select7 _root_.OAI.CurrentKS.Realization.poly_splitProduct _root_.OAI.CurrentKS.Realization.poly_squareScan _root_.OAI.CurrentKS.Realization.poly_tabulateIndexed _root_.OAI.CurrentKS.Realization.poly_vectorSub _root_.OAI.CurrentKS.Realization.poly_wordCons _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.CurrentKS.Realization.size_natPred _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GraphStack.poly_view _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsGraph _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsM _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsN _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_paramsView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointParams _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_pointView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inverse realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix
open AlgorithmicThinTrees

instance poly_solveRhs : PolyTime solveRhs := by unfold solveRhs;infer_instance

instance poly_solveTopRow : PolyTime solveTopRow := by unfold solveTopRow;infer_instance

instance poly_liftColumn : PolyTime liftColumn := by
  unfold liftColumn
  apply poly_then

instance poly_inverseLift : PolyTime inverseLift := by
  unfold inverseLift
  apply poly_then

lemma inverse_take_history (a : MatrixObject) (k : ℕ) :
    (schurHistoryData a |>.take k).foldl (fun B A => inverseLiftData (B,A)) []=[] ∨
    ∃b∈schurHistoryData a,
      (schurHistoryData a |>.take k).foldl (fun B A => inverseLiftData (B,A)) []=
        matrixData (RationalInverse.inverse b.1 b.2) := by
  rcases a with ⟨n,A⟩
  induction n generalizing k with
  | zero => simp [schurHistoryData]
  | succ n ih =>
    by_cases hk : k ≤ n
    · have he : (schurHistoryData ⟨n+1,A⟩).take k=
          (schurHistoryData ⟨n,KS.W17.schurTail A⟩).take k := by
        rw [schurHistoryData, List.take_append_of_le_length]
        simpa only [schurHistory_length] using hk
      rw [he]
      rcases ih k (KS.W17.schurTail A) with h|⟨b,hb,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,by simp only [schurHistoryData,List.mem_append,List.mem_singleton]; exact Or.inl hb,he⟩
    · rw [List.take_of_length_le (by rw [schurHistory_length]; change n+1 ≤ k; omega),inverse_fold_correct]
      exact Or.inr ⟨⟨n+1,A⟩,by simp [schurHistoryData],rfl⟩

lemma pivotTrace_posDef {N k t : ℕ} {A : Matrix (Fin N) (Fin N) ℚ}
    {p : Fin k → Fin N} {r : Fin t → Fin N} {B : Matrix (Fin t) (Fin t) ℚ}
    (h : KS.W07.PivotTrace A p r B) (hA : A.PosDef) : B.PosDef := by
  induction h with
  | initial => exact hA
  | zero _ _ ih => exact RationalInverse.schur_posDef _ ih
  | positive _ _ ih => exact RationalInverse.schur_posDef _ ih

lemma SchurDesc.posDef {a b : MatrixObject} (h : SchurDesc a b) (hA : a.2.PosDef) : b.2.PosDef := by
  obtain ⟨k,p,r,h⟩ := h
  exact pivotTrace_posDef h hA

lemma matrixInverse_parts {n b : ℕ} (A : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀i j,QParts b (A i j)) (hp : A.PosDef) :
    ∀i j,QParts (KS.W30.inverseBitBound n b) (RationalInverse.inverse n A i j) := by
  intro i j
  rw [RationalInverse.inverse_eq A hp]
  have hh := KS.W30.rational_inverse_parts_size_le A b (fun i j => (h i j).1)
    (fun i j => (h i j).2) (isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hp.isUnit)) i j
  exact ⟨(Nat.size_le.mp hh.1).le,(Nat.size_le.mp hh.2).le⟩

lemma SchurDesc.inverse_wire {a b : MatrixObject} (h : SchurDesc a b)
    (hA : a.2.PosDef) :
    (matrixCode (matrixData (RationalInverse.inverse b.1 b.2))).length ≤
      a.1*(2*(a.1*(2*(4*(32*((matrixObjectCode a).length+1)^7)+7)+1))+1) := by
  have hn := h.dim
  have hp := h.posDef hA
  obtain ⟨k,p,r,h⟩ := h
  have he := matrixInverse_parts b.2 (RationalGram.trace_parts h (matrixObject_parts a)) hp
  have hm := KS.W30.inverseBitBound_mono_dim (KS.W30.inverseBitBound a.1 (matrixObjectCode a).length) hn
  have hm' := hm.trans (KS.W30.inverseBitBound_twice_le_input_polynomial (matrixObject_dim_le a) le_rfl)
  have hb := matrixCode_parts_bound (RationalInverse.inverse b.1 b.2) (fun i j => (he i j).mono hm')
  exact hb.trans (Nat.mul_le_mul hn (Nat.add_le_add_right
    (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ hn)) 1))

lemma runsPoly_rationalInverse {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L rationalInverseProgram a := by
  have hh := runsPoly_schurHistory a ha (fun i => (hA i).posSemidef)
  have hh' := (RunsPoly.of_poly (constant matrixObjectCode matrixCode []) a ha).both hh
  have hd : IsPoly L (fun i => (a i).1) := ha.mono (fun i => matrixObject_dim_le (a i))
  have hb := hd.mul (((isPoly_const L 2).mul (hd.mul (((isPoly_const L 2).mul
    (((isPoly_const L 4).mul ((isPoly_const L 32).mul ((ha.add (isPoly_const L 1)).pow 7))).add
      (isPoly_const L 7))).add (isPoly_const L 1)))).add (isPoly_const L 1))
  obtain ⟨p,hp⟩ := hb
  have hfold := runsPoly_fold_of_poly inverseLift (fun i => ([],schurHistoryData (a i)))
    hh'.output (show ∃p : NaturalPolynomial, _ from ⟨p,by
      intro i ys zs he
      have hy : ys=(schurHistoryData (a i)).take ys.length := by
        dsimp only at he
        rw [he,List.take_left]
      rw [hy]
      rcases inverse_take_history (a i) ys.length with hz|⟨b,hb,he⟩
      · rw [hz]; exact Nat.zero_le _
      · rw [he]
        exact ((schurHistory_mem (a i) (hA i).posSemidef b hb).inverse_wire
          (RationalInverse.posDef_of_cast _ (hA i))).trans (hp i)⟩)
  unfold rationalInverseProgram
  apply RunsPoly.changeOutput
  exact (RunsPoly.of_poly matrixDim a ha).both (hh'.then hfold)

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramWhitening
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram whitening. -/

section

namespace AlgorithmicThinTrees.GramWhitening
open Matrix Finset
open scoped MatrixOrder
variable {n d m : ℕ}

lemma cast_inverse (P : Matrix (Fin n) (Fin n) ℚ) :
    (P⁻¹).map (fun q : ℚ => (q:ℝ)) = (P.map (fun q : ℚ => (q:ℝ)))⁻¹ := by
  have hadj : P.adjugate.map (fun q : ℚ => (q:ℝ)) =
      (P.map (fun q : ℚ => (q:ℝ))).adjugate := (Rat.castHom ℝ).map_adjugate P
  rw [Matrix.inv_def,Matrix.inv_def,Ring.inverse_eq_inv,Ring.inverse_eq_inv]
  ext i j
  simp only [map_apply,Matrix.smul_apply,smul_eq_mul,Rat.cast_mul,Rat.cast_inv]
  rw [←Rat.cast_det]
  have hh := congrFun (congrFun hadj i) j
  exact congrArg ((P.det:ℝ)⁻¹ * ·) hh

end AlgorithmicThinTrees.GramWhitening
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_GramRealization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_fUniformDrop _root_.OAI.CurrentKS.Realization.poly_faceStart _root_.OAI.CurrentKS.Realization.poly_mgDen _root_.OAI.CurrentKS.Realization.poly_mgM _root_.OAI.CurrentKS.Realization.poly_mgN _root_.OAI.CurrentKS.Realization.poly_mgRest _root_.OAI.CurrentKS.Realization.poly_mgShift _root_.OAI.CurrentKS.Realization.poly_mgView _root_.OAI.CurrentKS.Realization.poly_minList _root_.OAI.CurrentKS.Realization.poly_nonzeroIndices _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView _root_.OAI.CurrentKS.Realization.poly_packFace _root_.OAI.CurrentKS.Realization.poly_recordCoordinate _root_.OAI.CurrentKS.Realization.poly_recordCoordinates _root_.OAI.CurrentKS.Realization.poly_recordEntry _root_.OAI.CurrentKS.Realization.poly_recordTrace _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.CurrentKS.Realization.size_minDatum _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_formsView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_frameView _root_.OAI.AlgorithmicThinTrees.Signing.Stack.poly_pairView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gram realization. -/

section

namespace CurrentKS.Realization
open CleanRoutine KS.W23 Matrix AlgorithmicThinTrees

instance poly_firstColumn : PolyTime firstColumn := by unfold firstColumn;infer_instance

instance poly_gramLift : PolyTime gramLift := by
  unfold gramLift
  apply poly_congr

lemma gram_take_history (a : MatrixObject) (k : ℕ) :
    (schurHistoryData a |>.take k).foldl (fun B A => gramLiftData (B,A)) []=[] ∨
    ∃b∈schurHistoryData a,
      (schurHistoryData a |>.take k).foldl (fun B A => gramLiftData (B,A)) []=
        (RationalGram.factorColumns b.1 b.2).map List.ofFn := by
  rcases a with ⟨n,A⟩
  induction n generalizing k with
  | zero => simp [schurHistoryData]
  | succ n ih =>
    by_cases hk : k ≤ n
    · have he : (schurHistoryData ⟨n+1,A⟩).take k=
          (schurHistoryData ⟨n,KS.W17.schurTail A⟩).take k := by
        rw [schurHistoryData,List.take_append_of_le_length]
        simpa only [schurHistory_length] using hk
      rw [he]
      rcases ih k (KS.W17.schurTail A) with h|⟨b,hb,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨b,by simp only [schurHistoryData,List.mem_append,List.mem_singleton]; exact Or.inl hb,he⟩
    · rw [List.take_of_length_le (by rw [schurHistory_length]; change n+1 ≤ k; omega),gram_fold_correct]
      exact Or.inr ⟨⟨n+1,A⟩,by simp [schurHistoryData],rfl⟩

lemma SchurDesc.gram_wire {a b : MatrixObject} (h : SchurDesc a b)
    (hA : (a.2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    (matrixCode ((RationalGram.factorColumns b.1 b.2).map List.ofFn)).length ≤
      (3*a.1*(2*KS.W30.inverseBitBound a.1 (matrixObjectCode a).length+1))*
        (2*(a.1*(2*(4*(4*KS.W30.inverseBitBound a.1 (matrixObjectCode a).length+1)+7)+1))+1) := by
  have hn := h.dim
  obtain ⟨k,p,r,h⟩ := h
  obtain ⟨hl,hv⟩ := RationalGram.trace_factor_bounds a.2 hA (matrixObject_parts a) h
  let B := KS.W30.inverseBitBound a.1 (matrixObjectCode a).length
  have hw : ∀v∈RationalGram.factorColumns b.1 b.2,
      (vectorCode (List.ofFn v)).length≤a.1*(2*(4*(4*B+1)+7)+1) := by
    intro v h
    apply (listCode_length_bound (List.ofFn v) (4*(4*B+1)+7) ?_).trans
      (by rw [List.length_ofFn]; exact Nat.mul_le_mul_right _ hn)
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact (show QParts (4*B+1) (v i) from hv v h i).length
  apply (listCode_length_bound _ (a.1*(2*(4*(4*B+1)+7)+1)) ?_).trans ?_
  · intro row hr
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hr
    exact hw v hv
  · rw [List.length_map]
    apply Nat.mul_le_mul_right _
    exact hl.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hn))

lemma runsPoly_gramColumns {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosSemidef) :
    RunsPoly L gramColumnsProgram a := by
  have hh := runsPoly_schurHistory a ha hA
  have hh' := (RunsPoly.of_poly (constant matrixObjectCode matrixCode []) a ha).both hh
  have hd : IsPoly L (fun i => (a i).1) := ha.mono (fun i => matrixObject_dim_le (a i))
  have hi : IsPoly L (fun i => KS.W30.inverseBitBound (a i).1 (matrixObjectCode (a i)).length) :=
    ((((isPoly_const L 6).mul (ha.add (isPoly_const L 1))).mul
      ((hd.add (isPoly_const L 1)).pow 3))).mono
        (fun i => KS.W30.inverseBitBound_le_polynomial _ _)
  have hb := (((isPoly_const L 3).mul hd).mul (((isPoly_const L 2).mul hi).add (isPoly_const L 1))).mul
    (((isPoly_const L 2).mul (hd.mul (((isPoly_const L 2).mul
      (((isPoly_const L 4).mul (((isPoly_const L 4).mul hi).add (isPoly_const L 1))).add
        (isPoly_const L 7))).add (isPoly_const L 1)))).add (isPoly_const L 1))
  obtain ⟨p,hp⟩ := hb
  have hfold := runsPoly_fold_of_poly gramLift (fun i => ([],schurHistoryData (a i)))
    hh'.output (show ∃p : NaturalPolynomial, _ from ⟨p,by
      intro i ys zs he
      have hy : ys=(schurHistoryData (a i)).take ys.length := by
        dsimp only at he
        rw [he,List.take_left]
      rw [hy]
      rcases gram_take_history (a i) ys.length with hz|⟨b,hb,he⟩
      · rw [hz]; exact Nat.zero_le _
      · rw [he]
        exact ((schurHistory_mem (a i) (hA i) b hb).gram_wire (hA i)).trans (hp i)⟩)
  unfold gramColumnsProgram
  exact (hh'.then hfold).congr _

end CurrentKS.Realization
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_RationalSigning
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Realization.poly_originalCountRealizes _root_.OAI.CurrentKS.Realization.poly_originalD _root_.OAI.CurrentKS.Realization.poly_originalFaceRealizes _root_.OAI.CurrentKS.Realization.poly_originalIndex _root_.OAI.CurrentKS.Realization.poly_originalIndices _root_.OAI.CurrentKS.Realization.poly_originalN _root_.OAI.CurrentKS.Realization.poly_originalNormalizedMatrix _root_.OAI.CurrentKS.Realization.poly_originalOrientation _root_.OAI.CurrentKS.Realization.poly_originalRecord _root_.OAI.CurrentKS.Realization.poly_originalRecords _root_.OAI.CurrentKS.Realization.poly_originalScale _root_.OAI.CurrentKS.Realization.poly_originalTrace _root_.OAI.CurrentKS.Realization.poly_originalTraces _root_.OAI.CurrentKS.Realization.poly_originalView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rational signing. -/

section

namespace AlgorithmicThinTrees.RationalSigning
open Matrix Finset CurrentKS
open RealMatrixBridge
open scoped MatrixOrder ComplexOrder
variable {d m : ℕ}

lemma input_matrix (v : Fin m → Fin d → ℚ) (e : Fin m) :
    (input v).matrix e=complexMatrix (outer v e) := by
  change (fun i j => CurrentKS.toComplex (entry (v e i*v e j),entry 0)) =
    complexMatrix (outer v e)
  ext i j
  apply Complex.ext <;>
    simp [CurrentKS.toComplex,entry_value,outer,realVec,complexMatrix,vecMulVec_apply]

lemma complex_outer (u : Fin d → ℝ) :
    complexMatrix (vecMulVec u u)=vecMulVec (fun i => (u i:ℂ)) (star (fun i => (u i:ℂ))) := by
  ext i j
  simp [complexMatrix,vecMulVec_apply]

lemma input_admissible (v : Fin m → Fin d → ℚ) : CurrentKS.Admissible (input v) := by
  intro e
  change Fin m at e
  rw [input_matrix,outer,complex_outer]
  exact ⟨(posSemidef_vecMulVec_self_star _).isHermitian,rank_vecMulVec_le _ _⟩

end AlgorithmicThinTrees.RationalSigning
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Signing_Realization
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.InputStack.poly_binaryTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_explicitTail _root_.OAI.AlgorithmicThinTrees.InputStack.poly_formatTest _root_.OAI.AlgorithmicThinTrees.InputStack.poly_goodFields _root_.OAI.CurrentKS.Realization.poly_wordHead _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_loopView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_reachView _root_.OAI.AlgorithmicThinTrees.GreedyTree.Stack.poly_subgraphView _root_.OAI.AlgorithmicThinTrees.Iteration.Stack.poly_stateView _root_.OAI.AlgorithmicThinTrees.GraphicHalf.Stack.poly_problemView
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signing realization. -/

section

namespace AlgorithmicThinTrees.Signing.Stack
open CurrentKS.Realization CurrentKS.CleanRoutine KS.W23 Matrix

private instance poly_frameDim : PolyTime frameDim := by
  unfold frameDim
  apply poly_then

private instance poly_frameRows : PolyTime frameRows := by
  unfold frameRows
  apply poly_then

instance poly_complexField : PolyTime complexField := by unfold complexField;infer_instance

instance poly_outerFields : PolyTime outerFields := by unfold outerFields;infer_instance

instance poly_signerInput : PolyTime signerInput := by
  unfold signerInput
  apply poly_changeOutput

lemma runsPoly_signs {ι : Type*} {L : ι → ℕ} (a : ι → Frame)
    (ha : IsPoly L (fun i => (frameCode (a i)).length)) : RunsPoly L signs a := by
  have hi := RunsPoly.of_poly signerInput a ha
  exact hi.then (runsPoly_originalSigningFramed _ hi.output
    (fun i => RationalSigning.input_admissible (a i).v))

lemma runsPoly_factorRows {ι : Type*} {L : ι → ℕ} (a : ι → MatrixObject)
    (ha : IsPoly L (fun i => (matrixObjectCode (a i)).length))
    (hA : ∀i,((a i).2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L factorRows a := by
  have hi := runsPoly_rationalInverse a ha hA
  unfold factorRows
  apply RunsPoly.congr
  apply hi.then
  apply runsPoly_gramColumns _ hi.output
  intro i
  rw [RationalInverse.inverse_eq_of_cast _ (hA i),GramWhitening.cast_inverse]
  exact (hA i).inv.posSemidef

lemma runsPoly_whiten {ι : Type*} {L : ι → ℕ} (a : ι → FormFrame)
    (ha : IsPoly L (fun i => (formCode (a i)).length))
    (hA : ∀i,((a i).form.2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L whiten a := by
  have : PolyTime formMatrix := by
    unfold formMatrix
    apply poly_then
  have : PolyTime formRows := by
    unfold formRows
    apply poly_then
  have hf := RunsPoly.of_poly formMatrix a ha
  have hr := hf.then (runsPoly_factorRows _ hf.output hA)
  have hc := (hr.both (RunsPoly.of_poly formRows a ha)).then_poly matVec.mapCtx
  unfold whiten
  apply RunsPoly.changeOutput
  exact (hr.then_poly (lengthList vectorCode)).both hc

instance poly_stack : PolyTime stack := by
  have : PolyTime pairLeft := by unfold pairLeft; apply poly_then
  have : PolyTime pairRight := by unfold pairRight; apply poly_then
  unfold stack
  apply poly_changeOutput

lemma runsPoly_simultaneousSigns_oai {ι : Type*} {L : ι → ℕ} (a : ι → FormPair)
    (ha : IsPoly L (fun i => (formsCode (a i)).length))
    (hA : ∀i,((a i).a.2.map (fun q : ℚ => (q:ℝ))).PosDef)
    (hB : ∀i,((a i).b.2.map (fun q : ℚ => (q:ℝ))).PosDef) :
    RunsPoly L simultaneousSigns a := by
  have : PolyTime formsLeft := by
    unfold formsLeft
    apply poly_then
  have : PolyTime formsRight := by
    unfold formsRight
    apply poly_then
  have hu := RunsPoly.of_poly formsLeft a ha
  have hv := RunsPoly.of_poly formsRight a ha
  have hw : RunsPoly L whitenPair a := by
    unfold whitenPair
    apply RunsPoly.changeOutput
    exact (hu.then (runsPoly_whiten _ hu.output hA)).both
      (hv.then (runsPoly_whiten _ hv.output hB))
  have hs := hw.then_poly stack
  exact hw.then ((RunsPoly.of_poly stack _ hw.output).then (runsPoly_signs _ hs.output))

end AlgorithmicThinTrees.Signing.Stack
end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns_oai.{u_1} := @OAI.AlgorithmicThinTrees.Signing.Stack.runsPoly_simultaneousSigns_oai.{u_1}
