-- Prove2me | solution 1 for OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T18:39:29.33436+00:00
-- url     : https://prove2.me/submissions/a92ee6db-a5cd-408f-b16b-aed3f46dc17d

import Mathlib
import Definitions.Def_CoordinateSweeps
import Definitions.Def_OAIQ56Cs000

section
-- module Solutions.OAIQ56_CS.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Grid
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.columnChoicesFintype _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.rowChoicesFintype _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps

/- A probability law on a finite sample space, with real-valued masses. -/

theorem monotone_prefix_average (f : ℕ → ℝ) {u m : ℕ} (hu : u ≤ m)
    (hf : ∀ i < m, ∀ j < m, i ≤ j → f i ≤ f j) :
    (m : ℝ) * (∑ i ∈ Finset.range u, f i) ≤
      (u : ℝ) * (∑ i ∈ Finset.range m, f i) := by
  have h : (∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f i) ≤
      ∑ i ∈ Finset.range u, ∑ j ∈ Finset.Ico u m, f j := by
    apply Finset.sum_le_sum
    intro i hi
    apply Finset.sum_le_sum
    intro j hj
    have hi' := Finset.mem_range.mp hi
    have hj' := Finset.mem_Ico.mp hj
    exact hf i (lt_of_lt_of_le hi' hu) j hj'.2 (le_trans (le_of_lt hi') hj'.1)
  simp only [Finset.sum_const, Nat.card_Ico, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum, Nat.cast_sub hu] at h
  have hs := Finset.sum_range_add_sum_Ico f hu
  nlinarith

theorem sum_corrections (m u : ℕ) (hu : u ≤ m) :
    (∑ j ∈ Finset.range u, (Real.log m - Real.log (m-j : ℕ))) =
       (u : ℝ) * Real.log m - Real.log (m.descFactorial u : ℝ) := by
  induction u with
  | zero => simp
  | succ u ih =>
    have hum : u ≤ m := by omega
    rw [Finset.sum_range_succ, ih hum, Nat.descFactorial_succ, Nat.cast_mul,
      Real.log_mul (by exact_mod_cast (show m-u ≠ 0 by omega))
        (by exact_mod_cast (Nat.descFactorial_pos.mpr hum).ne')]
    push_cast
    ring

theorem lineCost_eq (m u : ℕ) (hm : 0 < m) (hu : u ≤ m) :
    lineCost m u = ∑ j ∈ Finset.range u, (Real.log m - Real.log (m-j : ℕ)) := by
  rw [lineCost, Real.log_div (by positivity)
    (by exact_mod_cast (Nat.descFactorial_pos.mpr hu).ne'), Real.log_pow,
    sum_corrections m u hu]

theorem lineCost_nonneg (m u : ℕ) (hm : 0 < m) (hu : u ≤ m) :
    0 ≤ lineCost m u := by
  rw [lineCost_eq m u hm hu]
  apply Finset.sum_nonneg
  intro j hj
  have hj' : j < m := (Finset.mem_range.mp hj).trans_le hu
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · exact_mod_cast (show 0 < m-j by omega)
  · exact_mod_cast (Nat.sub_le m j)

theorem full_lineCost_le (m : ℕ) (hm : 0 < m) : lineCost m m ≤ m := by
  have hs := Stirling.le_log_factorial_stirling (Nat.ne_of_gt hm)
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hp : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1
  rw [lineCost_eq m m hm le_rfl, sum_corrections m m le_rfl, Nat.descFactorial_self]
  linarith

theorem lineCost_le (m u : ℕ) (hm : 0 < m) (hu : u ≤ m) : lineCost m u ≤ u := by
  have hs := monotone_prefix_average (fun j => Real.log m - Real.log (m-j : ℕ)) hu
    (by
      intro i hi j hj hij
      have hlog : Real.log (m-j : ℕ) ≤ Real.log (m-i : ℕ) :=
        Real.log_le_log (by exact_mod_cast (show 0 < m-j by omega))
          (by exact_mod_cast (Nat.sub_le_sub_left hij m))
      linarith)
  rw [← lineCost_eq m u hm hu, ← lineCost_eq m m hm le_rfl] at hs
  have hall := full_lineCost_le m hm
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  nlinarith

/- Binary positions with their actual bit-coordinate labels. -/

namespace Grid

namespace Holes

variable {G : Grid} {h : ℕ}

theorem lineCount_le (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    H.lineCount j L ≤ 2 ^ G.bits j := by
  have hb : H.lineCount j L ≤ Fintype.card (Cube (G.bits j)) := by
    apply Finset.card_le_card_of_injOn (fun i => H.path i j.castSucc j)
    · intro _ _
      exact Finset.mem_univ _
    · intro i hi i' hi' he
      apply H.disjoint j.castSucc
      funext k
      by_cases hk : k = j
      · subst k
        exact he
      · have h1 := (Finset.mem_filter.mp hi).2
        have h2 := (Finset.mem_filter.mp hi').2
        exact (congrFun h1 ⟨k, hk⟩).trans (congrFun h2 ⟨k, hk⟩).symm
  simpa [Cube] using hb

theorem sum_lineCount (H : G.Holes h) (j : Fin G.b) :
    ∑ L : G.Line j, H.lineCount j L = h := by
  unfold lineCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem cost_nonneg (H : G.Holes h) : 0 ≤ H.cost := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro L _
  exact lineCost_nonneg _ _ (by positivity) (H.lineCount_le j L)

theorem cost_le (H : G.Holes h) : H.cost ≤ (G.b : ℝ) * h := by
  calc
    H.cost ≤ ∑ j, ∑ L : G.Line j, (H.lineCount j L : ℝ) := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro L _
      exact lineCost_le _ _ (by positivity) (H.lineCount_le j L)
    _ = (G.b : ℝ) * h := by
      simp only [← Nat.cast_sum, H.sum_lineCount]
      simp

/- Permutations of the free input sites, presented as permutations fixing the
prescribed inputs. This is the symmetric group on exactly s-h sites. -/

end Holes

/- Joint mass of all independent stage-line choices. -/

end Grid

namespace FiniteLaw

variable {Ω : Type*} [Fintype Ω]

theorem mass_le_one (μ : FiniteLaw Ω) (x : Ω) : μ x ≤ 1 := by
  rw [← μ.sum_mass]
  exact Finset.single_le_sum (fun y _ => μ.nonneg y) (Finset.mem_univ x)

/- A uniform, finite-alphabet perturbation interval, depending on the line
size only. This proves the source's half-to-two measure comparison. -/
theorem mix_uniform_between [Nonempty Ω] (ν : FiniteLaw Ω) {z : ℝ}
    (hz : 0 ≤ z) (hzhalf : z ≤ 1/2) (hzcard : z ≤ (Fintype.card Ω : ℝ)⁻¹)
    (x : Ω) :
    (1/2 : ℝ) * uniform Ω x ≤ (uniform Ω).mix ν z hz (by linarith) x ∧
      (uniform Ω).mix ν z hz (by linarith) x ≤ 2 * uniform Ω x := by
  have hn := ν.nonneg x
  have hle := ν.mass_le_one x
  have hU : 0 ≤ uniform Ω x := (uniform Ω).nonneg x
  change (1/2 : ℝ) * uniform Ω x ≤ (1-z) * uniform Ω x + z * ν x ∧
    (1-z) * uniform Ω x + z * ν x ≤ 2 * uniform Ω x
  constructor
  · nlinarith [mul_nonneg hz hn, mul_nonneg (sub_nonneg.mpr hzhalf) hU]
  · change z ≤ uniform Ω x at hzcard
    nlinarith [mul_nonneg hz hU, mul_le_mul_of_nonneg_left hle hz]

variable [DecidableEq Ω]

theorem assignments_nonneg {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (x y : Fin h ↪ Ω) : 0 ≤ μ.assignments x y := by
  apply Finset.sum_nonneg
  intro g _
  split_ifs
  · exact μ.nonneg g
  · rfl

theorem sum_assignments {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (x : Fin h ↪ Ω) : ∑ y, μ.assignments x y = 1 := by
  unfold assignments
  rw [Finset.sum_comm]
  simp

theorem uniform_assignments_same {h : ℕ} (x y z : Fin h ↪ Ω) :
    (uniform (Equiv.Perm Ω)).assignments x y =
      (uniform (Equiv.Perm Ω)).assignments x z := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair y z y.injective z.injective
  have hz : y.trans σ.toEmbedding = z := by
    ext i
    exact hσ i
  unfold assignments
  rw [← Equiv.sum_comp (Equiv.mulLeft σ)
    (fun g : Equiv.Perm Ω => if x.trans g.toEmbedding = z then
      uniform (Equiv.Perm Ω) g else 0)]
  apply Finset.sum_congr rfl
  intro g _
  have he : x.trans (σ * g).toEmbedding = z ↔ x.trans g.toEmbedding = y := by
    rw [← hz]
    constructor
    · intro he
      ext i
      exact σ.injective (congrArg (fun f : Fin h ↪ Ω => f i) he)
    · intro he
      ext i
      change σ (g (x i)) = σ (y i)
      exact congrArg σ (congrArg (fun f : Fin h ↪ Ω => f i) he)
  simp only [Equiv.coe_mulLeft, he, uniform_apply]

theorem uniform_assignments {h : ℕ} (x y : Fin h ↪ Ω) :
    (uniform (Equiv.Perm Ω)).assignments x y =
      ((Fintype.card Ω).descFactorial h : ℝ)⁻¹ := by
  let : Nonempty (Fin h ↪ Ω) := ⟨y⟩
  have hh : (∑ z : Fin h ↪ Ω, (uniform (Equiv.Perm Ω)).assignments x y) = 1 := by
    convert sum_assignments (uniform (Equiv.Perm Ω)) x using 1
    all_goals try with_reducible_and_instances rfl
    apply Finset.sum_congr rfl
    intro z _
    exact uniform_assignments_same x y z
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_embedding_eq, Fintype.card_fin] at hh
  have hm : ((Fintype.card Ω).descFactorial h : ℝ) ≠ 0 := by
    intro hm
    rw [hm, zero_mul] at hh
    norm_num at hh
  exact ((mul_eq_one_iff_inv_eq₀ hm).mp hh).symm

theorem uniform_assignments_pos {h : ℕ} (x y : Fin h ↪ Ω) :
    0 < (uniform (Equiv.Perm Ω)).assignments x y := by
  rw [uniform_assignments]
  apply inv_pos.mpr
  exact_mod_cast Nat.descFactorial_pos.mpr (by simpa using Fintype.card_le_of_embedding x)

theorem assignments_le {h : ℕ} (μ ν : FiniteLaw (Equiv.Perm Ω)) (C : ℝ)
    (hb : ∀ g, μ g ≤ C * ν g) (x y : Fin h ↪ Ω) :
    μ.assignments x y ≤ C * ν.assignments x y := by
  unfold assignments
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  split_ifs
  · exact hb g
  · simp

theorem le_assignments {h : ℕ} (μ ν : FiniteLaw (Equiv.Perm Ω)) (C : ℝ)
    (hb : ∀ g, C * ν g ≤ μ g) (x y : Fin h ↪ Ω) :
    C * ν.assignments x y ≤ μ.assignments x y := by
  unfold assignments
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro g _
  split_ifs
  · exact hb g
  · simp

/- The exact factor four in the line-conditioning argument, with all
line assignments represented by actual injections, not abstract events. -/

end FiniteLaw

namespace Grid.Holes
variable {G : Grid} {h : ℕ}

theorem probability_prod (H : G.Holes h) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.probability z = ∏ j, ∏ L, ∑ σ : {σ // H.LineCompatible j L σ},
      lineLaw (G.bits j) z hz hz' σ.val := by
  unfold probability
  rw [← Equiv.sum_comp H.compatibleEquiv.symm]
  change (∑ σ : (∀ j L, {σ // H.LineCompatible j L σ}),
    ∏ j, ∏ L, lineLaw (G.bits j) z hz hz' (σ j L).val) = _
  rw [← Fintype.prod_sum (fun j : Fin G.b =>
    fun σ : (∀ L, {σ // H.LineCompatible j L σ}) =>
      ∏ L, lineLaw (G.bits j) z hz hz' (σ L).val)]
  apply Finset.prod_congr rfl
  intro j _
  exact (Fintype.prod_sum (fun L => fun σ : {σ // H.LineCompatible j L σ} =>
    lineLaw (G.bits j) z hz hz' σ.val)).symm

theorem lineCompatible_iff_assignments (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (σ : Equiv.Perm (Cube (G.bits j))) :
    H.LineCompatible j L σ ↔ (H.lineInput j L).trans σ.toEmbedding = H.lineOutput j L := by
  constructor
  · intro hs
    apply Function.Embedding.ext
    intro i
    exact hs (H.lineCards j L i)
  · intro hs i
    obtain ⟨k,rfl⟩ := (H.lineCards j L).surjective i
    exact congrArg (fun f : Fin (H.lineCount j L) ↪ Cube (G.bits j) => f k) hs

theorem sum_subtype_eq_sum_ite_of_iff {Ω : Type*} [Fintype Ω]
    {p q : Ω → Prop} [Fintype {a // p a}] [DecidablePred q]
    (h : ∀ a, p a ↔ q a) (f : Ω → ℝ) :
    (∑ a : {a // p a}, f a.val) = ∑ a, if q a then f a else 0 := by
  classical
  rw [← Finset.sum_subtype (Finset.univ.filter p) (by simp)]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  simp only [h a]

theorem lineProbability_eq (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    (∑ σ : {σ // H.LineCompatible j L σ}, μ σ.val) =
      μ.assignments (H.lineInput j L) (H.lineOutput j L) := by
  exact sum_subtype_eq_sum_ite_of_iff (H.lineCompatible_iff_assignments j L) μ.mass

theorem probability_eq_assignments (H : G.Holes h) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.probability z = ∏ j, ∏ L,
      (lineLaw (G.bits j) z hz hz').assignments (H.lineInput j L) (H.lineOutput j L) := by
  rw [H.probability_prod hz hz']
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro L _
  exact H.lineProbability_eq j L (lineLaw (G.bits j) z hz hz')

/- Under uniform line randomization each prescribed injection pays exactly
one falling-factorial denominator. -/
theorem probability_zero (H : G.Holes h) :
    H.probability 0 = ∏ j, ∏ L,
      (((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ)⁻¹) := by
  rw [H.probability_eq_assignments (le_refl 0) zero_le_one]
  apply Finset.prod_congr rfl
  intro j _
  apply Finset.prod_congr rfl
  intro L _
  have he : lineLaw (G.bits j) 0 (le_refl 0) zero_le_one = FiniteLaw.uniform _ := by
    ext σ
    simp [lineLaw, FiniteLaw.mix]
  rw [he]
  have hu := FiniteLaw.uniform_assignments (H.lineInput j L) (H.lineOutput j L)
  have hc : Fintype.card (Cube (G.bits j)) = 2 ^ G.bits j := by simp [Cube]
  rw [hc] at hu
  exact hu

end Grid.Holes
end CoordinateSweeps

end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Matrix_TensorMoment
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
theorem norm_entry_le_matrix_norm {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin D) : ‖A i j‖ ≤ ‖A‖ := by
  let v : EuclideanSpace ℂ (Fin D) := EuclideanSpace.single j 1
  have hv : ‖v‖ = 1 := by simp [v]
  have h := A.l2_opNorm_mulVec v
  have hi := PiLp.norm_apply_le ((EuclideanSpace.equiv (Fin D) ℂ).symm (A.mulVec v)) i
  have he : ((EuclideanSpace.equiv (Fin D) ℂ).symm (A.mulVec v)) i = A i j := by
    simp [v]
  rw [he] at hi
  rw [hv, mul_one] at h
  exact hi.trans h

theorem norm_trace_le {D : ℕ} (A : Matrix (Fin D) (Fin D) ℂ) :
    ‖Matrix.trace A‖ ≤ D * ‖A‖ := by
  calc
    ‖Matrix.trace A‖ ≤ ∑ i, ‖A i i‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Fin D, ‖A‖ := Finset.sum_le_sum (fun i _ => norm_entry_le_matrix_norm A i i)
    _ = D * ‖A‖ := by simp

theorem trace_moment_le {D : ℕ} [NeZero D] (A : Matrix (Fin D) (Fin D) ℂ) (q : ℕ) :
    (Matrix.trace ((A.conjTranspose * A)^q)).re ≤ D * ‖A‖^(2*q) := by
  calc
    _ ≤ ‖Matrix.trace ((A.conjTranspose * A)^q)‖ := Complex.re_le_norm _
    _ ≤ D * ‖(A.conjTranspose * A)^q‖ := norm_trace_le _
    _ ≤ D * ‖A.conjTranspose * A‖^q :=
      mul_le_mul_of_nonneg_left (norm_pow_le _ _) (Nat.cast_nonneg _)
    _ = D * ‖A‖^(2*q) := by rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, ← pow_mul]

theorem matrix_unitary_norm_le {D : ℕ} [NeZero D] (A : Matrix (Fin D) (Fin D) ℂ)
    (hA : A.conjTranspose * A = 1) : ‖A‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self A
  rw [hA] at h
  have h1 : ‖(1 : Matrix (Fin D) (Fin D) ℂ)‖ ≤ 1 := le_of_eq (norm_one)
  nlinarith [norm_nonneg A]

end CoordinateSweeps
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Unitary_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

theorem commuting_scalar (A : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ)
    (hA : ∀ g, A*ρ.matrix g=ρ.matrix g*A) : ∃ c : ℂ, A=c • (1 : Matrix _ _ ℂ) := by
  let F : Representation.IntertwiningMap ρ.asRepresentation ρ.asRepresentation :=
    { toLinearMap := Matrix.toLinAlgEquiv' A
      isIntertwining' := by
        intro g
        change Matrix.toLinAlgEquiv' A * Matrix.toLinAlgEquiv' (ρ.matrix g)=
          Matrix.toLinAlgEquiv' (ρ.matrix g) * Matrix.toLinAlgEquiv' A
        rw [← map_mul,← map_mul,hA g] }
  obtain ⟨c,hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ.asRepresentation) |>.2 F
  refine ⟨c,?_⟩
  apply Matrix.toLinAlgEquiv'.injective
  have hh := congrArg Representation.IntertwiningMap.toLinearMap hc
  change c • (1 : Module.End ℂ (Fin ρ.dimension → ℂ))=Matrix.toLinAlgEquiv' A at hh
  simpa using hh.symm

variable [Fintype Γ]

/- Character normalization in exactly the unnormalized trace convention. -/

omit [Fintype Γ] in
lemma matrix_inv (g : Γ) : ρ.matrix g⁻¹=(ρ.matrix g).conjTranspose := by
  calc
    ρ.matrix g⁻¹=1*ρ.matrix g⁻¹ := (one_mul _).symm
    _ = ((ρ.matrix g).conjTranspose*ρ.matrix g)*ρ.matrix g⁻¹ := by rw [ρ.unitary g]
    _ = (ρ.matrix g).conjTranspose := by rw [mul_assoc,← map_mul,mul_inv_cancel,map_one,mul_one]

/- Coefficients of the central isotypic projector, in unnormalized trace
convention. They are derived from an actual irrep, not supplied as character
data satisfying unproved orthogonality equations. -/

end UnitaryIrrep
end CoordinateSweeps

/- Multiplicity in a unitary matrix representation is controlled by the
commutant dimension, with exact (unnormalized) character conventions. -/
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Conditioning
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

noncomputable section
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

namespace Grid.Holes

variable {G : Grid} {h : ℕ}

/- Average of the remaining random bijection, conditioned on the entire paths,
not only endpoints. The reference affects only unitary identifications. -/

theorem conditionalAverage_eq_sum (H : G.Holes h) (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ρ =
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        ((G.choiceWeight z ω.val / H.probability z : ℝ) : ℂ) •
          ρ.matrix (H.residual hf ω) := by
  simp only [conditionalAverage, Finset.smul_sum, smul_smul, div_eq_mul_inv,
    Complex.ofReal_mul, Complex.ofReal_inv, mul_comm]

end Grid.Holes

/- Source constants a=1/100, c0=e0=a/100. -/

end CoordinateSweeps

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Graphs_Coverage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I]

/- Oriented edges crossing a two-color cut. -/
theorem exists_crossing_cut (R : I → I → Prop)
    (hsym : ∀ ⦃left right⦄, R left right → R right left) (hirr : ∀ vertex, ¬ R vertex vertex) :
    ∃ c : I → Bool, ∀ i, (∃ j, R i j) → ∃ j, R i j ∧ c i ≠ c j := by
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image
    (Finset.univ : Finset (I → Bool)) (fun c => (cutEdges R c).card) Finset.univ_nonempty
  refine ⟨c, ?_⟩
  intro i hi
  by_contra hh
  have hn : ∀ j, R i j → c i = c j := by
    intro j hij
    by_contra hne
    exact hh ⟨j,hij,hne⟩
  let c' := Function.update c i (!(c i))
  have hsub : cutEdges R c ⊆ cutEdges R c' := by
    intro p hp
    obtain ⟨hpR,hpne⟩ := (mem_cutEdges R c p.1 p.2).mp hp
    have hpi : p.1 ≠ i := by
      intro he; subst he
      exact hpne (hn _ hpR)
    have hpj : p.2 ≠ i := by
      intro he
      have heq := hn p.1 (hsym (he ▸ hpR))
      exact hpne (he ▸ heq.symm)
    apply (mem_cutEdges R c' p.1 p.2).mpr
    exact ⟨hpR, by simpa [c', Function.update_of_ne hpi, Function.update_of_ne hpj] using hpne⟩
  obtain ⟨j,hij⟩ := hi
  have hji : j ≠ i := by intro he; subst j; exact hirr i hij
  have hnew : (i,j) ∈ cutEdges R c' := by
    rw [mem_cutEdges]
    refine ⟨hij, ?_⟩
    simp only [c', Function.update_self, Function.update_of_ne hji]
    rw [← hn j hij]
    cases c i <;> decide
  have hold : (i,j) ∉ cutEdges R c := by simp [hn j hij]
  have hlt : (cutEdges R c).card < (cutEdges R c').card :=
    Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, by
      intro he; rw [he] at hold; exact hold hnew⟩)
  exact (not_lt_of_ge (hc c' (Finset.mem_univ _))) hlt

/- Particles incident to a particle-sharing edge or a fixed hole. -/
theorem exists_star_forest (R : I → I → Prop) (T : I → H → Prop)
    (hsym : ∀ ⦃left right⦄, R left right → R right left) (hirr : ∀ vertex, ¬ R vertex vertex) :
    ∃ A : Finset I, A ⊆ covered R T ∧ (covered R T).card ≤ 2*A.card ∧
      ∀ i ∈ A, (∃ j, j ∉ A ∧ R i j) ∨ (∃ l, T i l) := by
  obtain ⟨c,hc⟩ := exists_crossing_cut R hsym hirr
  let A := (covered R T).filter (fun i => c i = false)
  let B := (covered R T).filter (fun i => c i = true)
  have hAB : (covered R T).card = A.card + B.card := by
    have hpart := Finset.card_filter_add_card_filter_not (s := covered R T)
      (p := fun i => c i = false)
    have he : B = (covered R T).filter (fun i => ¬ c i = false) := by
      ext i
      simp only [B, Finset.mem_filter]
      cases c i <;> simp
    rw [he]
    exact hpart.symm
  have hA : ∀ i ∈ A, (∃ j, j ∉ A ∧ R i j) ∨ (∃ l, T i l) := by
    intro i hi
    obtain ⟨hcov,hci⟩ := Finset.mem_filter.mp hi
    rcases (mem_covered R T i).mp hcov with h | h
    · obtain ⟨j,hij,hne⟩ := hc i h
      left
      refine ⟨j,?_,hij⟩
      intro hj
      have hcj := (Finset.mem_filter.mp hj).2
      exact hne (hci.trans hcj.symm)
    · exact Or.inr h
  have hB : ∀ i ∈ B, (∃ j, j ∉ B ∧ R i j) ∨ (∃ l, T i l) := by
    intro i hi
    obtain ⟨hcov,hci⟩ := Finset.mem_filter.mp hi
    rcases (mem_covered R T i).mp hcov with h | h
    · obtain ⟨j,hij,hne⟩ := hc i h
      left
      refine ⟨j,?_,hij⟩
      intro hj
      have hcj := (Finset.mem_filter.mp hj).2
      exact hne (hci.trans hcj.symm)
    · exact Or.inr h
  by_cases hle : A.card ≤ B.card
  · exact ⟨B, Finset.filter_subset _ _, by omega, hB⟩
  · exact ⟨A, Finset.filter_subset _ _, by omega, hA⟩

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/- Product mass of independent particle data. -/

omit [Fintype X] in
theorem productMass_glue (A : Finset I) (w : X → ℝ)
    (x : A → X) (y : {i : I // i ∉ A} → X) :
    productMass w (glue A x y) = (∏ i, w (x i)) * ∏ j, w (y j) := by
  unfold productMass
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i => i ∈ A)]
  simp only [glue_mem, glue_not_mem]
  congr!

/- Reused elementary finite independence identity, inline. -/
theorem sum_prod_ite_all {J : Type*} [Fintype J] [DecidableEq J]
    {Y : J → Type*} [∀ j, Fintype (Y j)]
    (w : ∀ j, Y j → ℝ) (P : ∀ j, Y j → Prop) :
    (∑ x : ∀ j, Y j, if ∀ j, P j (x j) then ∏ j, w j (x j) else 0) =
      ∏ j, ∑ y, if P j y then w j y else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ j, P j (x j)
  · simp [hx]
  · obtain ⟨j,hj⟩ := not_forall.mp hx
    rw [ite_eq_right hx]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hj]

/- Conditional on all roots, different star tails involve independent data.
This is a factorization of the actual finite sum, not an independence axiom. -/
theorem probability_star_factorization (A : Finset I) (w : X → ℝ)
    (P : ({i : I // i ∉ A} → X) → A → X → Prop) :
    probability w (fun x : I → X => ∀ i : A, P (fun j => x j) i (x i)) =
      ∑ y : {i : I // i ∉ A} → X,
        (∏ j, w (y j)) * ∏ i : A, ∑ t : X, if P y i t then w t else 0 := by
  unfold probability
  let e := Equiv.piEquivPiSubtypeProd (fun i => i ∈ A) (fun _ => X)
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hg : ∀ x : A → X,
      (if ∀ i : A, P (fun j => e.symm (x,y) j) i (e.symm (x,y) i)
        then productMass w (e.symm (x,y)) else 0) =
      (∏ j, w (y j)) * (if ∀ i : A, P y i (x i) then ∏ i, w (x i) else 0) := by
    intro x
    change (if ∀ i : A, P (fun j => glue A x y j) i (glue A x y i)
      then productMass w (glue A x y) else 0) = _
    simp only [glue_mem, glue_not_mem, productMass_glue]
    split_ifs <;> ring
  calc
    _ = ∑ x : A → X, (∏ j, w (y j)) *
        (if ∀ i : A, P y i (x i) then ∏ i, w (x i) else 0) := by
      apply Finset.sum_congr rfl
      intro x _
      convert hg x using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    _ = (∏ j, w (y j)) * (∑ x : A → X,
        if ∀ i : A, P y i (x i) then ∏ i, w (x i) else 0) := by rw [Finset.mul_sum]
    _ = _ := by
      congr 1
      exact sum_prod_ite_all (fun (_ : A) t => w t) (P y)

/- The source's leaf elimination bound for the star witnesses selected above. -/
theorem probability_star_le (A : Finset I) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) (ω : ℝ) (hω : 0 ≤ ω)
    (P : ({i : I // i ∉ A} → X) → A → X → Prop)
    (hP : ∀ y i, (∑ t : X, if P y i t then w t else 0) ≤ ω) :
    probability w (fun x : I → X => ∀ i : A, P (fun j => x j) i (x i)) ≤ ω^A.card := by
  rw [probability_star_factorization]
  have hprod : ∀ y : {i : I // i ∉ A} → X,
      (∏ i : A, ∑ t : X, if P y i t then w t else 0) ≤ ω^A.card := by
    intro y
    calc
      _ ≤ ∏ _i : A, ω := by
        apply Finset.prod_le_prod
        · intro i _; exact Finset.sum_nonneg (fun t _ => by split_ifs; exact hw t; exact le_rfl)
        · intro i _; exact hP y i
      _ = _ := by simp
  calc
    _ ≤ ∑ y : {i : I // i ∉ A} → X, (∏ j, w (y j)) * ω^A.card := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hprod y) (Finset.prod_nonneg (fun j _ => hw _))
    _ ≤ 1 * ω^A.card := by
      rw [← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hω _)
      rw [← Fintype.prod_sum]
      simp [hs]
    _ = ω^A.card := one_mul _

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I]

/- A finite directed star system. Distinct tails are indexed by the subtype A;
the parent lies outside A or is a hole. -/
theorem exists_star_system (R : I → I → Prop) (T : I → H → Prop)
    (hsym : ∀ ⦃left right⦄, R left right → R right left) (hirr : ∀ vertex, ¬ R vertex vertex) (j : ℕ)
    (hj : j ≤ ((covered R T).card + 1)/2) :
    ∃ A : Finset I, A.card = j ∧ ∃ p : A → I ⊕ H, starSystem R T A p := by
  obtain ⟨B,_,hB,hpar⟩ := exists_star_forest R T hsym hirr
  have hjB : j ≤ B.card := by omega
  obtain ⟨A,hAB,hAc⟩ := Finset.exists_subset_card_eq hjB
  have hp : ∀ i : A, ∃ r : I ⊕ H, match r with
      | .inl l => l ∉ A ∧ R i l
      | .inr l => T i l := by
    intro i
    rcases hpar i (hAB i.property) with ⟨l,hl,hR⟩ | ⟨l,hT⟩
    · exact ⟨.inl l, fun hm => hl (hAB hm), hR⟩
    · exact ⟨.inr l, hT⟩
  choose p hp using hp
  exact ⟨A,hAc,p,hp⟩

variable {X : Type*} [Fintype X]

/- The sharing event of one directed system under the full independent data.
Forbidden parent choices simply give an empty event. -/

omit [Fintype I] [Fintype X] in
theorem starEvent_iff_root (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H) (x : I → X) :
    starEvent S holes A p x ↔
      ∀ i : A, rootPredicate S holes A p (fun j => x j) i (x i) := by
  unfold starEvent starSystem rootPredicate
  apply forall_congr'
  intro i
  cases p i with
  | inl j => by_cases hj : j ∉ A <;> simp [hj]
  | inr l => rfl

/- For every particular system of j distinct tails toward non-tail parents,
the sharing probability is at most ω^j, with no layer independence premise. -/
theorem probability_starEvent_le (S : X → X → Prop) (holes : H → X)
    (A : Finset I) (p : A → I ⊕ H) (w : X → ℝ)
    (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω) :
    probability w (starEvent S holes A p) ≤ ω^A.card := by
  have he : starEvent S holes A p =
      (fun x : I → X => ∀ i : A, rootPredicate S holes A p (fun j => x j) i (x i)) := by
    funext x
    exact propext (starEvent_iff_root S holes A p x)
  rw [he]
  apply probability_star_le A w hw hs ω hω
  intro y i
  unfold rootPredicate
  cases hp : p i with
  | inl j =>
    by_cases hj : j ∉ A
    · simpa only [dite_eq_left hj] using hS (y ⟨j,hj⟩)
    · simpa [hj] using hω
  | inr l => exact hS (holes l)

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

omit [DecidableEq I] [Fintype X] in
theorem productMass_nonneg (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (x : I → X) :
    0 ≤ productMass w x := Finset.prod_nonneg (fun i _ => hw (x i))

theorem probability_mono (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    {P Q : (I → X) → Prop} (hPQ : ∀ x, P x → Q x) :
    probability w P ≤ probability w Q := by
  apply Finset.sum_le_sum
  intro x _
  by_cases hp : P x
  · simp only [ite_eq_left hp, ite_eq_left (hPQ x hp)]
    exact le_rfl
  · simp only [ite_eq_right hp]
    split_ifs
    · exact productMass_nonneg w hw x
    · exact le_rfl

theorem probability_exists_le {J : Type*} [Fintype J]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (P : J → (I → X) → Prop) :
    probability w (fun x => ∃ j, P j x) ≤ ∑ j, probability w (P j) := by
  unfold probability
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hpj : ∀ j, 0 ≤ (if P j x then productMass w x else 0) := by
    intro j; split_ifs; exact productMass_nonneg w hw x; exact le_rfl
  by_cases he : ∃ j, P j x
  · obtain ⟨j,hj⟩ := he
    rw [ite_eq_left ⟨j,hj⟩]
    have hh := Finset.single_le_sum (fun j _ => hpj j) (Finset.mem_univ j)
    simpa only [ite_eq_left hj] using hh
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun j _ => hpj j)

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H : Type*} [Fintype I] [DecidableEq I] [Fintype H]

/- Data encoding exactly j distinct tails and one arbitrary parent per tail.
The sub-event enforces the star/root restrictions. -/

theorem card_witness_le (j : ℕ) :
    Fintype.card (Witness I H j) ≤
      2^Fintype.card I * (Fintype.card I + Fintype.card H)^j := by
  have hc : ∀ A : {A : Finset I // A.card = j},
      Fintype.card (A.val → I ⊕ H) = (Fintype.card I + Fintype.card H)^j := by
    intro A
    simp [A.property]
  have hA : Fintype.card {A : Finset I // A.card = j} ≤ 2^Fintype.card I := by
    simpa using Fintype.card_le_of_injective
      (fun A : {A : Finset I // A.card = j} => A.val) Subtype.val_injective
  calc
    _ = Fintype.card {A : Finset I // A.card = j} *
        (Fintype.card I + Fintype.card H)^j := by
      rw [Fintype.card_sigma]
      simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hA

variable {X : Type*} [Fintype X]

/- Covered particles for the actual symmetric sharing relation on path data. -/

omit [Fintype H] [Fintype X] in
theorem sharingCoverage_witness (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (x : I → X) (n : ℕ)
    (hn : n ≤ (sharingCoverage S holes x).card) :
    ∃ W : Witness I H ((n+1)/2), starEvent S holes W.1.val W.2 x := by
  let R : I → I → Prop := fun i j => i ≠ j ∧ S (x i) (x j)
  let T : I → H → Prop := fun i l => S (x i) (holes l)
  have hsym : ∀ ⦃left right⦄, R left right → R right left := fun i j h => ⟨h.1.symm, hSsym h.2⟩
  have hirr : ∀ vertex, ¬ R vertex vertex := fun i h => h.1 rfl
  have hc : n ≤ (covered R T).card := hn
  obtain ⟨A,hAc,p,hp⟩ := exists_star_system R T hsym hirr ((n+1)/2) (by omega)
  refine ⟨⟨⟨A,hAc⟩,p⟩,?_⟩
  intro i
  have hi := hp i
  cases hpi : p i with
  | inl j =>
    simp only [hpi] at hi ⊢
    exact ⟨hi.1,hi.2.2⟩
  | inr l =>
    simpa only [hpi] using hi

/- Source coverage bound with the slightly stronger integer exponent ceil(n/2).
There is no independence assumption between different path layers. -/
theorem probability_coverage_le_nat (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω) (n : ℕ) :
    probability w (fun x : I → X => n ≤ (sharingCoverage S holes x).card) ≤
      (2 : ℝ)^Fintype.card I *
        (((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω)^((n+1)/2) := by
  let j := (n+1)/2
  let P : Witness I H j → (I → X) → Prop :=
    fun W => starEvent S holes W.1.val W.2
  calc
    _ ≤ probability w (fun x : I → X => ∃ W : Witness I H j, P W x) :=
      probability_mono w hw (fun x hx => sharingCoverage_witness S hSsym holes x n hx)
    _ ≤ ∑ W : Witness I H j, probability w (P W) := probability_exists_le w hw P
    _ ≤ ∑ _W : Witness I H j, ω^j := by
      apply Finset.sum_le_sum
      intro W _
      simpa only [W.1.property] using
        probability_starEvent_le S holes W.1.val W.2 w hw hs ω hω hS
    _ = (Fintype.card (Witness I H j) : ℝ) * ω^j := by simp
    _ ≤ (2 : ℝ)^Fintype.card I *
        (((Fintype.card I + Fintype.card H : ℕ) : ℝ)^j) * ω^j := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hω _)
      exact_mod_cast (card_witness_le (I := I) (H := H) j)
    _ = _ := by rw [mul_assoc, ← mul_pow]

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H X : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype X]

/- The literal source's coverage estimate (04:eq9), including zero sharing
rate and zero requested coverage, with the real exponent n/2. -/
theorem probability_coverage_le (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω)
    (hsmall : ((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω ≤ 1) (n : ℕ) :
    probability w (fun x : I → X => n ≤ (sharingCoverage S holes x).card) ≤
      (2 : ℝ)^Fintype.card I *
        ((((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω) ^ ((n : ℝ)/2)) := by
  have hn : n ≤ 2*((n+1)/2) := by omega
  have hn' : (n : ℝ) ≤ 2 * (((n+1)/2 : ℕ) : ℝ) := by exact_mod_cast hn
  have hr :
      ((((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω) ^ ((n+1)/2 : ℕ)) ≤
      ((((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω) ^ ((n : ℝ)/2)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge' (by positivity) hsmall (by positivity) (by linarith)
  exact (probability_coverage_le_nat S hSsym holes w hw hs ω hω hS n).trans
    (mul_le_mul_of_nonneg_left hr (by positivity))

end CoordinateSweeps.Coverage
end
end
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps.Coverage
variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X]

/- Independent occupancy of a fixed measurable subset. The set is fixed
BEFORE taking probability, exactly as required in source04:eq12. -/
theorem probability_many_hits_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (P : X → Prop) (p : ℝ) (hp : 0 ≤ p)
    (hP : (∑ x, if P x then w x else 0) ≤ p) (n : ℕ) :
    probability w (fun x : I → X => n ≤ (Finset.univ.filter (fun i => P (x i))).card) ≤
      (2 : ℝ)^Fintype.card I * p^n := by
  let W := {A : Finset I // A.card = n}
  have hcover (x : I → X) (hx : n ≤ (Finset.univ.filter (fun i => P (x i))).card) :
      ∃ A : W, ∀ i : A.val, P (x i) := by
    obtain ⟨A,hA,hAc⟩ := Finset.exists_subset_card_eq hx
    exact ⟨⟨A,hAc⟩, fun i => (Finset.mem_filter.mp (hA i.property)).2⟩
  have hprob (A : W) : probability w (fun x : I → X => ∀ i : A.val, P (x i)) ≤ p^n := by
    simpa only [A.property] using probability_star_le A.val w hw hs p hp
      (fun _ _ x => P x) (fun _ _ => hP)
  calc
    _ ≤ probability w (fun x : I → X => ∃ A : W, ∀ i : A.val, P (x i)) :=
      probability_mono w hw hcover
    _ ≤ ∑ A : W, probability w (fun x : I → X => ∀ i : A.val, P (x i)) :=
      probability_exists_le w hw _
    _ ≤ ∑ _A : W, p^n := Finset.sum_le_sum (fun A _ => hprob A)
    _ = (Fintype.card W : ℝ)*p^n := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp _)
      exact_mod_cast (Fintype.card_subtype_le (fun A : Finset I => A.card = n)).trans_eq
        (Fintype.card_finset (α := I))

theorem probability_many_hits_le_rpow (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (P : X → Prop) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hP : (∑ x, if P x then w x else 0) ≤ p) (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X => u ≤ ((Finset.univ.filter (fun i => P (x i))).card : ℝ)) ≤
      (2 : ℝ)^Fintype.card I * p^u := by
  have he := probability_many_hits_le (I := I) w hw hs P p hp hP ⌈u⌉₊
  have hconv : (fun x : I → X => u ≤ ((Finset.univ.filter (fun i => P (x i))).card : ℝ)) =
      (fun x => ⌈u⌉₊ ≤ (Finset.univ.filter (fun i => P (x i))).card) := by
    funext x
    exact propext Nat.ceil_le.symm
  rw [hconv]
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_ge' hp hp1 hu (Nat.le_ceil u)

/- Canonical padded enumeration encodes a subset of size at most r in r
optional entries. This supplies the source's (number-of-lines+1)^r union count. -/

theorem mem_iff_encodeSmallSet {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ)
    (S : {S : Finset L // S.card ≤ r}) (a : L) :
    a ∈ S.val ↔ ∃ i, encodeSmallSet r S i = some a := by
  constructor
  · intro ha
    let e := Fintype.equivFinOfCardEq (Fintype.card_coe S.val)
    let j := e ⟨a,ha⟩
    let i : Fin r := ⟨j.val, lt_of_lt_of_le j.isLt S.property⟩
    refine ⟨i, ?_⟩
    simp only [encodeSmallSet, i, dite_eq_left j.isLt]
    change some ((e.symm j).val) = some a
    simp [j]
  · rintro ⟨i,hi⟩
    unfold encodeSmallSet at hi
    split_ifs at hi with hlt
    · have he := Option.some.inj hi
      rw [← he]
      exact ((Fintype.equivFinOfCardEq (Fintype.card_coe S.val)).symm ⟨i.val,hlt⟩).property

theorem encodeSmallSet_injective {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ) :
    Function.Injective (encodeSmallSet (L := L) r) := by
  intro S T he
  apply Subtype.ext
  ext a
  rw [mem_iff_encodeSmallSet, mem_iff_encodeSmallSet]
  simp only [he]

theorem card_smallSets_le {L : Type*} [Fintype L] [DecidableEq L] (r : ℕ) :
    Fintype.card {S : Finset L // S.card ≤ r} ≤ (Fintype.card L+1)^r := by
  have he := Fintype.card_le_of_injective _ (encodeSmallSet_injective (L := L) r)
  simpa using he

/- Uniform union bound over small sets of lines, without conditioning on a
set chosen from the particle array. -/
theorem probability_smallSet_hits_le {L : Type*} [Fintype L] [DecidableEq L]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1) (line : X → L)
    (r : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hprob : ∀ S : Finset L, S.card ≤ r → (∑ x, if line x ∈ S then w x else 0) ≤ p)
    (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X => ∃ S : Finset L, S.card ≤ r ∧
      u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S)).card : ℝ)) ≤
      ((Fintype.card L+1 : ℕ) : ℝ)^r * (2 : ℝ)^Fintype.card I * p^u := by
  let W := {S : Finset L // S.card ≤ r}
  have he (x : I → X) :
      (∃ S : Finset L, S.card ≤ r ∧ u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S)).card : ℝ)) ↔
      ∃ S : W, u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S.val)).card : ℝ) := by
    constructor
    · rintro ⟨S,hS,hc⟩; exact ⟨⟨S,hS⟩,hc⟩
    · rintro ⟨S,hc⟩; exact ⟨S.val,S.property,hc⟩
  simp only [he]
  calc
    _ ≤ ∑ S : W, probability w (fun x : I → X =>
          u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S.val)).card : ℝ)) :=
      probability_exists_le w hw _
    _ ≤ ∑ _S : W, (2 : ℝ)^Fintype.card I*p^u := by
      apply Finset.sum_le_sum
      intro S _
      convert probability_many_hits_le_rpow (I := I) w hw hs (fun x => line x ∈ S.val) p hp hp1
        (by convert hprob S.val S.property using 1; congr!) u hu using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    _ = (Fintype.card W : ℝ)*((2 : ℝ)^Fintype.card I*p^u) := by simp
    _ ≤ _ := by
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast card_smallSets_le (L := L) r

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I X L : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype L] [DecidableEq L]

omit [Fintype L] in
theorem sum_lineSet (w : X → ℝ) (line : X → L) (S : Finset L) :
    (∑ x, if line x ∈ S then w x else 0) =
      ∑ l ∈ S, ∑ x, if line x = l then w x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp

omit [Fintype L] in
theorem probability_lineSet_le (w : X → ℝ) (line : X → L) (S : Finset L)
    (δ : ℝ) (hδ : ∀ l, (∑ x, if line x = l then w x else 0) ≤ δ) :
    (∑ x, if line x ∈ S then w x else 0) ≤ (S.card : ℝ)*δ := by
  rw [sum_lineSet]
  calc
    _ ≤ ∑ _l ∈ S, δ := Finset.sum_le_sum (fun l _ => hδ l)
    _ = _ := by simp

omit [DecidableEq L] in
theorem heavySet_card_mul_le (t : L → ℕ) (v : ℝ) :
    ((heavySet t v).card : ℝ)*v ≤ ∑ l, (t l : ℝ) := by
  calc
    _ = ∑ _l ∈ heavySet t v, v := by simp
    _ ≤ ∑ l ∈ heavySet t v, (t l : ℝ) := by
      apply Finset.sum_le_sum
      intro l hl
      exact (Finset.mem_filter.mp hl).2.le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.cast_nonneg _)

omit [DecidableEq L] in
theorem heavySet_card_le_floor (t : L → ℕ) {v : ℝ} (hv : 0 < v) :
    (heavySet t v).card ≤ ⌊(∑ l, (t l : ℝ))/v⌋₊ := by
  apply Nat.le_floor
  apply (le_div_iff₀ hv).mpr
  exact heavySet_card_mul_le t v

omit [DecidableEq I] [Fintype X] in
theorem sum_occupancy (line : X → L) (x : I → X) :
    ∑ l, occupancy line x l = Fintype.card I := by
  unfold occupancy
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/- Heavy line sets are small by deterministic occupancy counting. -/
omit [DecidableEq I] [Fintype X] in
theorem heavy_occupancy_card_le (line : X → L) (x : I → X) {v : ℝ} (hv : 0 < v) :
    (heavySet (occupancy line x) v).card ≤ ⌊(Fintype.card I : ℝ)/v⌋₊ := by
  have hh := heavySet_card_le_floor (occupancy line x) hv
  simpa only [← Nat.cast_sum, sum_occupancy] using hh

/- Probability of many particles in particle-heavy lines. The random line
set is controlled by a union over ALL small deterministic sets. -/
theorem probability_heavy_occupancy_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : ∑ x, w x = 1) (line : X → L) {v : ℝ} (hv : 0 < v)
    (p δ : ℝ) (hδ : 0 ≤ δ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hline : ∀ l, (∑ x, if line x = l then w x else 0) ≤ δ)
    (hrp : (⌊(Fintype.card I : ℝ)/v⌋₊ : ℝ)*δ ≤ p)
    (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X =>
      u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ heavySet (occupancy line x) v)).card : ℝ)) ≤
      ((Fintype.card L+1 : ℕ) : ℝ)^⌊(Fintype.card I : ℝ)/v⌋₊ *
        (2 : ℝ)^Fintype.card I * p^u := by
  apply le_trans (probability_mono w hw (Q := fun x : I → X =>
    ∃ S : Finset L, S.card ≤ ⌊(Fintype.card I : ℝ)/v⌋₊ ∧
      u ≤ ((Finset.univ.filter (fun i => line (x i) ∈ S)).card : ℝ)) (fun x hx =>
    ⟨heavySet (occupancy line x) v, heavy_occupancy_card_le line x hv, hx⟩))
  apply probability_smallSet_hits_le w hw hs line _ p hp hp1 _ u hu
  intro S hS
  have hle := probability_lineSet_le w line S δ hline
  apply hle.trans
  apply le_trans _ hrp
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hS) hδ

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Coverage
variable {I H X : Type*} [Fintype I] [DecidableEq I] [Fintype H] [Fintype X]

theorem probability_or_le (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (P Q : (I → X) → Prop) :
    probability w (fun x => P x ∨ Q x) ≤ probability w P + probability w Q := by
  simp only [probability, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x _
  have hx := productMass_nonneg w hw x
  split_ifs <;> simp_all

theorem probability_coverage_le_real (S : X → X → Prop)
    (hSsym : ∀ ⦃left right⦄, S left right → S right left)
    (holes : H → X) (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (hs : ∑ x, w x = 1)
    (ω : ℝ) (hω : 0 ≤ ω)
    (hS : ∀ y, (∑ t : X, if S t y then w t else 0) ≤ ω)
    (hsmall : ((Fintype.card I + Fintype.card H : ℕ) : ℝ) * ω ≤ 1)
    (u : ℝ) (hu : 0 ≤ u) :
    probability w (fun x : I → X => u ≤ ((sharingCoverage S holes x).card : ℝ)) ≤
      (2 : ℝ)^Fintype.card I *
      ((((Fintype.card I + Fintype.card H : ℕ) : ℝ)*ω)^(u/2)) := by
  have hc : (fun x : I → X => u ≤ ((sharingCoverage S holes x).card : ℝ)) =
      (fun x => ⌈u⌉₊ ≤ (sharingCoverage S holes x).card) := by
    funext x
    exact propext Nat.ceil_le.symm
  rw [hc]
  apply (probability_coverage_le S hSsym holes w hw hs ω hω hS hsmall ⌈u⌉₊).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact Real.rpow_le_rpow_of_exponent_ge' (by positivity) hsmall (by positivity)
    (div_le_div_of_nonneg_right (Nat.le_ceil u) (by norm_num))
end CoordinateSweeps.Coverage

end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Kernel
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All definitions are finite and use the source's ordinary probability and trace
normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! The alternating placement kernel from 04-sparse:eq7.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/
namespace CoordinateSweeps
namespace Grid

variable (G : Grid)

/- The unique auxiliary trajectory joining two slots. -/

namespace Holes
variable {G} {h k : ℕ}

/- Exact one-line probability after the hole assignments are prescribed. -/

theorem lineCompatible_of_empty (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (he : ∀ i, ¬ H.OnLine j L i) (σ : Equiv.Perm (Cube (G.bits j))) :
    H.LineCompatible j L σ := by
  intro i
  exact (he i.val i.property).elim

theorem localExtraProbability_no_paths (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (he : ∀ i, ¬ H.OnLine j L i)
    (ha : ∀ i ∈ A, G.pathLine (x i) (y i) j ≠ L) :
    H.localExtraProbability x y A j L μ = 1 := by
  have hr : ∀ σ, G.extraLineEvent x y A j L σ := by
    intro σ i hi hL
    exact (ha i hi hL).elim
  simp [localExtraProbability, H.lineCompatible_of_empty j L he, hr, μ.sum_mass]

theorem extraLineEvent_insert {G : Grid} {k : ℕ} (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (j : Fin G.b) (L : G.Line j)
    (σ : Equiv.Perm (Cube (G.bits j))) :
    G.extraLineEvent x y (insert i A) j L σ ↔
      ((G.pathLine (x i) (y i) j = L → σ (x i j) = y i j) ∧
        G.extraLineEvent x y A j L σ) := by
  simp [extraLineEvent]

/- The source's one-card marginal property, stated for a line law. This is
proved for both U and the actual binary law below, not a main-proof assumption. -/

theorem extraLineEvent_insert_off {G : Grid} {k : ℕ} (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (j : Fin G.b) (L : G.Line j)
    (hne : G.pathLine (x i) (y i) j ≠ L)
    (σ : Equiv.Perm (Cube (G.bits j))) :
    G.extraLineEvent x y (insert i A) j L σ ↔ G.extraLineEvent x y A j L σ := by
  rw [extraLineEvent_insert]
  simp [hne]

theorem localExtraProbability_insert_off (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hne : G.pathLine (x i) (y i) j ≠ L) :
    H.localExtraProbability x y (insert i A) j L μ =
      H.localExtraProbability x y A j L μ := by
  simp only [localExtraProbability, extraLineEvent_insert_off x y A i j L hne]

theorem localExtraProbability_isolated_insert (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (hi : i ∉ A)
    (his : H.LineIsolated x y i) (j : Fin G.b)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (hμ : OneCardUniform μ) :
    H.localExtraProbability x y (insert i A) j (G.pathLine (x i) (y i) j) μ =
      (2^G.bits j : ℝ)⁻¹ := by
  have he : ∀ σ, H.LineCompatible j (G.pathLine (x i) (y i) j) σ :=
    H.lineCompatible_of_empty j _ (his.1 j)
  have ha : ∀ σ, G.extraLineEvent x y A j (G.pathLine (x i) (y i) j) σ := by
    intro σ a ha hL
    exact (his.2 j a (by intro he; subst a; exact hi ha) hL).elim
  simp only [localExtraProbability, he, true_and, extraLineEvent_insert, ha,
    and_true, true_implies, ite_true, μ.sum_mass, div_one]
  exact hμ (x i j) (y i j)

theorem stageExtraProbability_isolated_insert (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (hi : i ∉ A)
    (his : H.LineIsolated x y i) (j : Fin G.b)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (hμ : OneCardUniform μ) :
    (∏ L : G.Line j, H.localExtraProbability x y (insert i A) j L μ) =
      (2^G.bits j : ℝ)⁻¹ * ∏ L : G.Line j, H.localExtraProbability x y A j L μ := by
  let L₀ := G.pathLine (x i) (y i) j
  have hs := H.localExtraProbability_isolated_insert x y A i hi his j μ hμ
  have he : H.localExtraProbability x y A j L₀ μ = 1 := by
    apply H.localExtraProbability_no_paths x y A j L₀ μ (his.1 j)
    intro a ha
    exact his.2 j a (by intro he; subst a; exact hi ha)
  have hprod : (∏ L ∈ Finset.univ.erase L₀, H.localExtraProbability x y (insert i A) j L μ) =
      ∏ L ∈ Finset.univ.erase L₀, H.localExtraProbability x y A j L μ := by
    apply Finset.prod_congr rfl
    intro L hL
    exact H.localExtraProbability_insert_off x y A i j L μ
      (Ne.symm (Finset.mem_erase.mp hL).1)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ L₀),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ L₀), hs, he, one_mul, hprod]

theorem extraProbability_isolated_insert (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (i : Fin k) (hi : i ∉ A)
    (his : H.LineIsolated x y i)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hμ : ∀ j, OneCardUniform (μ j)) :
    H.extraProbability x y (insert i A) μ =
      (G.size : ℝ)⁻¹ * H.extraProbability x y A μ := by
  unfold extraProbability
  simp_rw [H.stageExtraProbability_isolated_insert x y A i hi his _ _ (hμ _)]
  rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  congr 1
  simp [size, Nat.cast_prod, Nat.cast_pow]

/- Elementary pairing identity for the alternating sum. -/
lemma alternating_cancel {ι : Type*} [DecidableEq ι] (s : Finset ι) (i : ι) (hi : i ∈ s)
    (P : Finset ι → ℝ)
    (hP : ∀ A ⊆ s.erase i, P (insert i A) = P A) :
    ∑ A ∈ s.powerset, (-1 : ℝ) ^ A.card * P A = 0 := by
  have hs : s = insert i (s.erase i) := (Finset.insert_erase hi).symm
  rw [hs, Finset.sum_powerset_insert (Finset.notMem_erase i s)]
  have hh : (∑ A ∈ (s.erase i).powerset, (-1 : ℝ) ^ (insert i A).card * P (insert i A)) =
      -(∑ A ∈ (s.erase i).powerset, (-1 : ℝ) ^ A.card * P A) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro A hA
    have hsub : A ⊆ s.erase i := Finset.mem_powerset.mp hA
    have hni : i ∉ A := fun hh => Finset.notMem_erase i s (hsub hh)
    rw [Finset.card_insert_of_notMem hni, hP A hsub, pow_succ]
    ring
  rw [hh]
  ring

/- Isolated-path cancellation for the actual product conditional kernel.
There is no independence assumption between auxiliary particle factors. -/
theorem placementKernel_eq_zero_of_isolated (H : G.Holes h) (x y : Fin k → G.Slot)
    (i : Fin k) (his : H.LineIsolated x y i)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hμ : ∀ j, OneCardUniform (μ j)) : H.placementKernel x y μ = 0 := by
  have hsize : (G.size : ℝ) ≠ 0 := by
    apply ne_of_gt
    exact_mod_cast (Finset.prod_pos (fun j _ => pow_pos (by decide : 0 < (2:ℕ)) _))
  have hc := alternating_cancel (Finset.univ : Finset (Fin k)) i (Finset.mem_univ _)
    (fun A => (G.size : ℝ)^A.card * H.extraProbability x y A μ) (by
      intro A hA
      have hi : i ∉ A := fun hi => Finset.notMem_erase i _ (hA hi)
      rw [Finset.card_insert_of_notMem hi, pow_succ,
        H.extraProbability_isolated_insert x y A i hi his μ hμ]
      field_simp)
  have he : (∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
      (-1 : ℝ)^(k-A.card) * (G.size : ℝ)^A.card * H.extraProbability x y A μ) =
      (-1 : ℝ)^k * ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℝ)^A.card * ((G.size : ℝ)^A.card * H.extraProbability x y A μ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro A hA
    have hAk : A.card ≤ k := by simpa using Finset.card_le_univ A
    have hp : (-1 : ℝ)^(k-A.card) = (-1 : ℝ)^k * (-1 : ℝ)^A.card := by
      have h := pow_add (-1 : ℝ) (k-A.card) A.card
      rw [Nat.sub_add_cancel hAk] at h
      have hsq : (-1 : ℝ)^A.card * (-1 : ℝ)^A.card = 1 := by
        rw [← mul_pow]
        norm_num
      rw [h, mul_assoc, hsq, mul_one]
    rw [hp]
    ring
  rw [placementKernel, he, hc, mul_zero, mul_zero]

end Holes
end Grid
end CoordinateSweeps

namespace CoordinateSweeps.Grid
variable (G : Grid)

theorem sweep_eq_iff_line_assignments (ω : G.Choices) (x y : G.Slot) :
    G.sweep ω x = y ↔
      ∀ j, ω j (G.pathLine x y j) (x j) = y j := by
  constructor
  · intro hxy j
    have hs := congrArg (fun p : Equiv.Perm G.Slot => p x j)
      (G.boundary_succ ω j.isLt)
    change G.boundary ω (j.val+1) x j = G.stage ω j (G.boundary ω j x) j at hs
    rw [show G.boundary ω (j.val+1) x = G.pathBetween x y j.succ by
      simpa [hxy] using G.boundary_eq_pathBetween ω x j.succ,
      show G.boundary ω j.val x = G.pathBetween x y j.castSucc by
      simpa [hxy] using G.boundary_eq_pathBetween ω x j.castSucc] at hs
    change (ω j (fun k => G.pathBetween x y j.castSucc k)) (x j) = y j
    simpa only [G.stage_apply_same, G.pathBetween_input, G.pathBetween_output] using hs.symm
  · intro hxy
    have hb : ∀ t (ht : t ≤ G.b),
        G.boundary ω t x = G.pathBetween x y ⟨t,by omega⟩ := by
      intro t
      induction t with
      | zero => intro ht; simp
      | succ t ih =>
        intro ht
        have htb : t < G.b := by omega
        rw [G.boundary_succ ω htb]
        change G.stage ω ⟨t,htb⟩ (G.boundary ω t x) = _
        rw [ih (by omega)]
        funext k
        by_cases hkt : k = ⟨t,htb⟩
        · subst k
          have hi := hxy ⟨t,htb⟩
          change ω ⟨t,htb⟩ (fun k => G.pathBetween x y ⟨t,by omega⟩ k) (x ⟨t,htb⟩) = y ⟨t,htb⟩ at hi
          simpa only [stage_apply_same, pathBetween, Fin.val_mk, lt_self_iff_false,
            ite_false, Nat.lt_succ_self, ite_true] using hi
        · rw [G.stage_apply_ne ω _ k hkt]
          exact (G.pathBetween_step x y ⟨t,htb⟩ k hkt).symm
    have hh := hb G.b le_rfl
    change G.sweep ω x = G.pathBetween x y (Fin.last G.b) at hh
    rw [G.pathBetween_last] at hh
    exact hh

theorem endpointEvent_iff_lines {k : ℕ} (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (ω : G.Choices) :
    G.endpointEvent x y A ω ↔ ∀ j L, G.extraLineEvent x y A j L (ω j L) := by
  constructor
  · intro he j L i hi hL
    have h := (G.sweep_eq_iff_line_assignments ω (x i) (y i)).mp (he i hi) j
    simpa [hL] using h
  · intro he i hi
    apply (G.sweep_eq_iff_line_assignments ω (x i) (y i)).mpr
    intro j
    exact he j (G.pathLine (x i) (y i) j) i hi rfl

end CoordinateSweeps.Grid

namespace CoordinateSweeps

/- Finite independence, keeping an arbitrary local constraint at every factor. -/
theorem sum_prod_ite_all {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)]
    (w : ∀ i, X i → ℝ) (P : ∀ i, X i → Prop) :
    (∑ x : ∀ i, X i, if ∀ i, P i (x i) then ∏ i, w i (x i) else 0) =
      ∏ i, ∑ y, if P i y then w i y else 0 := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : ∀ i, P i (x i)
  · simp [hx]
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    rw [ite_eq_right hx]
    symm
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hi]

namespace Grid
variable (G : Grid)

theorem sum_productLineMass_event
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (P : ∀ j : Fin G.b, G.Line j → Equiv.Perm (Cube (G.bits j)) → Prop) :
    (∑ ω, if ∀ j L, P j L (ω j L) then G.productLineMass μ ω else 0) =
      ∏ j, ∏ L, ∑ σ, if P j L σ then μ j σ else 0 := by
  unfold productLineMass
  calc
    _ = ∏ j, ∑ ω : G.Line j → Equiv.Perm (Cube (G.bits j)),
        if ∀ L, P j L (ω L) then ∏ L, μ j (ω L) else 0 := by
      convert sum_prod_ite_all
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∏ L, μ j (ω L))
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∀ L, P j L (ω L)) using 1 <;>
        congr!
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      convert sum_prod_ite_all (fun _ σ => μ j σ) (P j) using 1
      all_goals try with_reducible_and_instances rfl

namespace Holes
variable {G} {h k : ℕ}

/- Conditional probability of an endpoint specification, from the original
independent line sample space; the full trajectories of the holes are retained. -/
theorem extraProbability_eq_conditionalEndpoint (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k))
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    H.extraProbability x y A μ = H.conditionalEndpointProbability x y A μ := by
  have he : ∀ ω : G.Choices,
      H.Compatible ω ∧ G.endpointEvent x y A ω ↔
        ∀ j L, H.LineCompatible j L (ω j L) ∧ G.extraLineEvent x y A j L (ω j L) := by
    intro ω
    rw [H.compatible_iff_lines, G.endpointEvent_iff_lines]
    constructor
    · intro h j L
      exact ⟨h.1 j L, h.2 j L⟩
    · intro h
      exact ⟨fun j L => (h j L).1, fun j L => (h j L).2⟩
  unfold conditionalEndpointProbability
  simp only [he]
  simp only [H.compatible_iff_lines]
  have hn : (∑ ω : G.Choices,
      if ∀ j L, H.LineCompatible j L (ω j L) ∧ G.extraLineEvent x y A j L (ω j L)
      then G.productLineMass μ ω else 0) =
      ∏ j, ∏ L, ∑ σ, if H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ
        then μ j σ else 0 := by
    convert G.sum_productLineMass_event μ (fun j L σ =>
      H.LineCompatible j L σ ∧ G.extraLineEvent x y A j L σ) using 1 <;>
      congr!
  have hd : (∑ ω : G.Choices, if ∀ j L, H.LineCompatible j L (ω j L)
      then G.productLineMass μ ω else 0) =
      ∏ j, ∏ L, ∑ σ, if H.LineCompatible j L σ then μ j σ else 0 := by
    convert G.sum_productLineMass_event μ H.LineCompatible using 1
    all_goals try with_reducible_and_instances rfl
  rw [hn, hd]
  simp only [extraProbability, localExtraProbability, Finset.prod_div_distrib]

/- At the source law, the denominator in the direct event formula is exactly
the source normalizer (with all prescribed paths, not just endpoints). -/
theorem lineMass_hole_normalizer (H : G.Holes h) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z ≤ 1) :
    (∑ ω, if H.Compatible ω then
      G.productLineMass (fun j => lineLaw (G.bits j) z hz hz') ω else 0) =
      H.probability z := by
  symm
  exact sum_subtype_eq_sum_ite_of_iff (fun _ => Iff.rfl) (G.choiceWeight z)

end Holes
end Grid
end CoordinateSweeps

namespace CoordinateSweeps

theorem binaryBoundary_succ {d : ℕ} (bits : BinaryChoices d) {t : ℕ} (ht : t < d) :
    binaryBoundary bits (t+1) = binaryLayer ⟨t,ht⟩ (bits ⟨t,ht⟩) * binaryBoundary bits t := by
  unfold binaryBoundary
  rw [List.take_succ_eq_append_getElem (by simpa using ht)]
  simp [List.reverse_append]

theorem binaryLayer_apply_ne {d : ℕ} (j k : Fin d) (hne : k ≠ j)
    (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) (x : Cube d) :
    binaryLayer j bits x k = x k := by
  simp [binaryLayer, pairSwitch, Equiv.funSplitAt_apply, Equiv.funSplitAt_symm_apply, hne]

theorem binaryBoundary_before {d : ℕ} (bits : BinaryChoices d) (x : Cube d) (k : Fin d)
    (t : ℕ) (ht : t ≤ k.val) : binaryBoundary bits t x k = x k := by
  induction t with
  | zero => simp
  | succ t ih =>
    have htb : t < d := by omega
    rw [binaryBoundary_succ bits htb]
    change binaryLayer ⟨t,htb⟩ (bits ⟨t,htb⟩) (binaryBoundary bits t x) k = _
    rw [binaryLayer_apply_ne _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem binaryBoundary_stable {d : ℕ} (bits : BinaryChoices d) (x : Cube d) (k : Fin d)
    (u v : ℕ) (hku : k.val < u) (huv : u ≤ v) (hvd : v ≤ d) :
    binaryBoundary bits v x k = binaryBoundary bits u x k := by
  induction v, huv using Nat.le_induction with
  | base => rfl
  | succ v huv ih =>
    have hvd' : v < d := by omega
    rw [binaryBoundary_succ bits hvd']
    change binaryLayer ⟨v,hvd'⟩ (bits ⟨v,hvd'⟩) (binaryBoundary bits v x) k = _
    rw [binaryLayer_apply_ne _ k (by intro he; have := congrArg Fin.val he; dsimp at this; omega)]
    exact ih (by omega)

theorem binaryBoundary_eq_path {d : ℕ} (bits : BinaryChoices d) (x : Cube d)
    (t : ℕ) (ht : t ≤ d) :
    binaryBoundary bits t x = binaryPath x (binarySweep d bits x) t := by
  funext k
  unfold binaryPath
  split_ifs with hkt
  · simpa using (binaryBoundary_stable bits x k t d hkt ht le_rfl).symm
  · exact binaryBoundary_before bits x k t (by omega)

theorem binarySweep_eq_iff_coins {d : ℕ} (bits : BinaryChoices d) (x y : Cube d) :
    binarySweep d bits x = y ↔
      ∀ j, bits j (binaryPathLine x y j) = Bool.xor (x j) (y j) := by
  have hxor : ∀ a b c : Bool, Bool.xor a b = c ↔ b = Bool.xor a c := by decide
  constructor
  · intro hxy j
    have hs := congrArg (fun p : Equiv.Perm (Cube d) => p x j)
      (binaryBoundary_succ bits j.isLt)
    change binaryBoundary bits (j.val+1) x j =
      binaryLayer j (bits j) (binaryBoundary bits j.val x) j at hs
    rw [binaryBoundary_eq_path bits x (j.val+1) (by omega),
      binaryBoundary_eq_path bits x j.val (by omega), hxy,
      binaryLayer_apply_same] at hs
    have hh : Bool.xor (x j) (bits j (binaryPathLine x y j)) = y j := by
      change Bool.xor (x j) (bits j (fun k => if k.val.val < j.val then y k else x k)) = y j
      simpa only [binaryPath, Nat.lt_succ_self, ite_true, lt_self_iff_false, ite_false] using hs.symm
    exact (hxor _ _ _).mp hh
  · intro hxy
    have hb : ∀ t (ht : t ≤ d), binaryBoundary bits t x = binaryPath x y t := by
      intro t
      induction t with
      | zero => intro ht; simp
      | succ t ih =>
        intro ht
        have htd : t < d := by omega
        rw [binaryBoundary_succ bits htd]
        change binaryLayer ⟨t,htd⟩ (bits ⟨t,htd⟩) (binaryBoundary bits t x) = _
        rw [ih (by omega)]
        funext k
        by_cases hkt : k = ⟨t,htd⟩
        · subst k
          rw [binaryLayer_apply_same]
          have hi := (hxor _ _ _).mpr (hxy ⟨t,htd⟩)
          change Bool.xor (x ⟨t,htd⟩) (bits ⟨t,htd⟩ (fun k => if k.val.val < t then y k else x k)) = y ⟨t,htd⟩ at hi
          simpa only [binaryPath, Nat.lt_succ_self, ite_true, lt_self_iff_false, ite_false] using hi
        · rw [binaryLayer_apply_ne _ k hkt]
          have hne : k.val ≠ t := fun he => hkt (Fin.ext he)
          simp only [binaryPath]
          have he : k.val < t+1 ↔ k.val < t := by omega
          simp [he]
    simpa using hb d le_rfl

end CoordinateSweeps

namespace CoordinateSweeps
namespace FiniteLaw

/- Independent uniform choices coincide with the uniform law on a finite
product, including dependent factors. -/
theorem uniform_pi {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Nonempty (X i)] :
    uniform (∀ i, X i) = independent (fun i => uniform (X i)) := by
  ext x
  change (Fintype.card (∀ i, X i) : ℝ)⁻¹ = ∏ i, (Fintype.card (X i) : ℝ)⁻¹
  simp [Fintype.card_pi, Nat.cast_prod, Finset.prod_inv_distrib]

/- One specified coordinate of a uniform random function is uniform. -/
theorem uniform_eval {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [Nonempty B] (a : A) (b : B) :
    (∑ f : A → B, if f a = b then uniform (A → B) f else 0) =
      (Fintype.card B : ℝ)⁻¹ := by
  let e := Equiv.funSplitAt a B
  rw [← Equiv.sum_comp e.symm]
  have hc : Fintype.card (A → B) = Fintype.card B * Fintype.card ({j : A // j ≠ a} → B) := by
    simpa using Fintype.card_congr e
  simp only [uniform_apply, Fintype.sum_prod_type, e, Equiv.funSplitAt_symm_apply]
  rw [hc, Nat.cast_mul]
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hA : (Fintype.card ({j : A // j ≠ a} → B) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp
  simp

/- Exact pushforward probability identity. -/
theorem map_event {A B : Type*} [Fintype A] [Fintype B]
    (μ : FiniteLaw A) (f : A → B) (P : B → Prop) :
    (∑ b, if P b then μ.map f b else 0) = ∑ a, if P (f a) then μ a else 0 := by
  simp only [map_apply]
  have hi : ∀ b, (if P b then ∑ a, if f a = b then μ a else 0 else 0) =
      ∑ a, if P b then (if f a = b then μ a else 0) else 0 := by
    intro b; by_cases hb : P b <;> simp [hb]
  simp only [hi]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have h : ∀ b, (if P b then (if f a = b then μ a else 0) else 0) =
      if f a = b then (if P (f a) then μ a else 0) else 0 := by
    intro b
    by_cases hb : f a = b
    · subst b; simp
    · simp [hb]
  simp only [h, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

end FiniteLaw

/- The actual fair-switch binary sweep sends every given slot uniformly.
In particular this is not imported as a hypothesis on the line law. -/
theorem binaryLaw_one_card (d : ℕ) (x y : Cube d) :
    (∑ σ, if σ x = y then binaryLaw d σ else 0) = (2^d : ℝ)⁻¹ := by
  unfold binaryLaw
  have hm := FiniteLaw.map_event (FiniteLaw.uniform (BinaryChoices d)) (binarySweep d) (fun σ => σ x = y)
  have he : (∑ σ, if σ x = y then
      (FiniteLaw.uniform (BinaryChoices d)).map (binarySweep d) σ else 0) =
      ∑ bits : BinaryChoices d, if binarySweep d bits x = y then
        FiniteLaw.uniform (BinaryChoices d) bits else 0 := by
    convert hm using 1 <;> congr!
  rw [he, FiniteLaw.uniform_pi]
  simp only [binarySweep_eq_iff_coins]
  change (∑ bits : BinaryChoices d,
    if ∀ j, bits j (binaryPathLine x y j) = Bool.xor (x j) (y j) then
      ∏ j, FiniteLaw.uniform (({k : Fin d // k ≠ j} → Bool) → Bool) (bits j) else 0) = _
  have hs := sum_prod_ite_all
    (fun j (b : ({k : Fin d // k ≠ j} → Bool) → Bool) => FiniteLaw.uniform _ b)
    (fun j (b : ({k : Fin d // k ≠ j} → Bool) → Bool) =>
      b (binaryPathLine x y j) = Bool.xor (x j) (y j))
  calc
    _ = ∏ j : Fin d, ∑ b : ({k : Fin d // k ≠ j} → Bool) → Bool,
        if b (binaryPathLine x y j) = Bool.xor (x j) (y j) then FiniteLaw.uniform _ b else 0 := by
      convert hs using 1 <;> congr!
    _ = ∏ _j : Fin d, (2 : ℝ)⁻¹ := by
      apply Finset.prod_congr rfl
      intro j _
      have hu := FiniteLaw.uniform_eval (binaryPathLine x y j) (Bool.xor (x j) (y j))
      convert hu using 1 <;> congr!
    _ = _ := by simp [← inv_pow]

end CoordinateSweeps

namespace CoordinateSweeps

/- The uniform permutation law has the same exact one-card marginal. -/
theorem uniformLaw_one_card (d : ℕ) (x y : Cube d) :
    (∑ σ : Equiv.Perm (Cube d), if σ x = y then FiniteLaw.uniform _ σ else 0) =
      (2^d : ℝ)⁻¹ := by
  let ex : Fin 1 ↪ Cube d := ⟨fun _ => x, fun _ _ _ => Subsingleton.elim _ _⟩
  let ey : Fin 1 ↪ Cube d := ⟨fun _ => y, fun _ _ _ => Subsingleton.elim _ _⟩
  have hu := FiniteLaw.uniform_assignments ex ey
  have hp : ∀ σ : Equiv.Perm (Cube d), ex.trans σ.toEmbedding = ey ↔ σ x = y := by
    intro σ
    constructor
    · intro he
      have hh := congrArg (fun e : Fin 1 ↪ Cube d => e 0) he
      exact hh
    · intro he
      apply Function.Embedding.ext
      intro i
      exact he
  simp only [FiniteLaw.assignments, hp] at hu
  have hc : Fintype.card (Cube d) = 2^d := by simp [Cube]
  simp only [hc, Nat.descFactorial_one, Nat.cast_pow, Nat.cast_ofNat] at hu
  convert hu using 1
  all_goals try with_reducible_and_instances rfl

/- No auxiliary marginal hypothesis remains: this is the manuscript's real
line law, including either endpoint value of the mixture parameter. -/
theorem lineLaw_one_card (d : ℕ) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    Grid.Holes.OneCardUniform (lineLaw d z hz hz') := by
  intro x y
  change (∑ σ, if σ x = y then
    (1-z) * FiniteLaw.uniform _ σ + z * binaryLaw d σ else 0) = _
  have hi : ∀ σ : Equiv.Perm (Cube d),
      (if σ x = y then (1-z) * FiniteLaw.uniform _ σ + z * binaryLaw d σ else 0) =
      (1-z) * (if σ x = y then FiniteLaw.uniform _ σ else 0) +
        z * (if σ x = y then binaryLaw d σ else 0) := by
    intro σ; by_cases h : σ x = y <;> simp [h]
  simp only [hi, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hu : (∑ σ : Equiv.Perm (Cube d), if σ x = y then FiniteLaw.uniform _ σ else 0) =
      (2^d : ℝ)⁻¹ := uniformLaw_one_card d x y
  have hb : (∑ σ : Equiv.Perm (Cube d), if σ x = y then binaryLaw d σ else 0) =
      (2^d : ℝ)⁻¹ := binaryLaw_one_card d x y
  rw [hu, hb]
  ring

/- Isolated-path cancellation, now for the literal conditioned sweep law. -/
theorem Grid.Holes.placementKernel_lineLaw_eq_zero_of_isolated
    {G : Grid} {h k : ℕ} (H : G.Holes h) (x y : Fin k → G.Slot)
    (i : Fin k) (his : H.LineIsolated x y i)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.placementKernel x y (fun j => lineLaw (G.bits j) z hz hz') = 0 := by
  exact H.placementKernel_eq_zero_of_isolated x y i his _
    (fun j => lineLaw_one_card (G.bits j) z hz hz')

end CoordinateSweeps

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid
variable (G : Grid)

theorem sum_pathBetween (t : Fin (G.b+1)) (f : G.Slot → ℝ) :
    (∑ p : G.Slot × G.Slot, f (G.pathBetween p.1 p.2 t)) =
      (G.size : ℝ) * ∑ x : G.Slot, f x := by
  calc
    _ = ∑ p : G.Slot × G.Slot, f p.1 := by
      exact Equiv.sum_comp (G.spliceEquiv t) (fun p => f p.1)
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_const, Finset.card_univ, G.card_slot, nsmul_eq_mul]
      rw [Finset.mul_sum]

/- A uniform slot chooses each stage-line with probability m_j/s. -/
theorem sum_slot_line (j : Fin G.b) (L : G.Line j) (c : ℝ) :
    (∑ x : G.Slot, if (fun k : {k : Fin G.b // k ≠ j} => x k) = L then c else 0) =
      (2^G.bits j : ℝ) * c := by
  let e := Equiv.piSplitAt j (fun k => Cube (G.bits k))
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have he : ∀ u : Cube (G.bits j), ∀ v : G.Line j,
      (fun k : {k : Fin G.b // k ≠ j} => e.symm (u,v) k) = v := by
    intro u v
    funext k
    simp [e, Equiv.piSplitAt_symm_apply, k.property]
  simp only [he, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [Cube]

/- Uniform product weight on the full pair of endpoints, with replacement. -/

theorem endpointWeight_nonneg (p : G.Slot × G.Slot) : 0 ≤ G.endpointWeight p :=
  (FiniteLaw.uniform _).nonneg p

theorem endpointWeight_total : ∑ p, G.endpointWeight p = 1 := FiniteLaw.sum_mass _

/- A single fixed vertex-sharing event has exact probability 1/s. -/
theorem probability_path_vertex (t : Fin (G.b+1)) (v : G.Slot) :
    (∑ p : G.Slot × G.Slot, if G.pathBetween p.1 p.2 t = v then G.endpointWeight p else 0) =
      (G.size : ℝ)⁻¹ := by
  have hs := G.sum_pathBetween t (fun x => if x = v then
    (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0)
  have hn : (G.size : ℝ) ≠ 0 := by
    exact_mod_cast (show G.size ≠ 0 by rw [← G.card_slot]; exact Fintype.card_ne_zero)
  calc
    _ = (G.size : ℝ) * ∑ x : G.Slot, if x = v then
        (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0 := by
      convert hs using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    _ = _ := by
      simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Fintype.card_prod, G.card_slot,
        Nat.cast_mul]
      field_simp

/- A single stage-line-sharing event has exact probability m_j/s. -/
theorem probability_path_line (j : Fin G.b) (L : G.Line j) :
    (∑ p : G.Slot × G.Slot, if G.pathLine p.1 p.2 j = L then G.endpointWeight p else 0) =
      (2^G.bits j : ℝ) / G.size := by
  have hs := G.sum_pathBetween j.castSucc (fun x =>
    if (fun k : {k : Fin G.b // k ≠ j} => x k) = L then
      (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0)
  have hn : (G.size : ℝ) ≠ 0 := by
    exact_mod_cast (show G.size ≠ 0 by rw [← G.card_slot]; exact Fintype.card_ne_zero)
  calc
    _ = (G.size : ℝ) * ∑ x : G.Slot,
        if (fun k : {k : Fin G.b // k ≠ j} => x k) = L then
          (Fintype.card (G.Slot × G.Slot) : ℝ)⁻¹ else 0 := by
      convert hs using 1
      all_goals try with_reducible_and_instances rfl
      congr!
    _ = _ := by
      rw [G.sum_slot_line]
      simp only [Fintype.card_prod, G.card_slot, Nat.cast_mul]
      field_simp

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Coverage

/- The union bound on a single finite random datum. -/
theorem sum_ite_exists_le {X J : Type*} [Fintype X] [Fintype J]
    (w : X → ℝ) (hw : ∀ x, 0 ≤ w x) (P : J → X → Prop) :
    (∑ x, if ∃ j, P j x then w x else 0) ≤ ∑ j, ∑ x, if P j x then w x else 0 := by
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  have hpj : ∀ j, 0 ≤ (if P j x then w x else 0) := by
    intro j; split_ifs; exact hw x; exact le_rfl
  by_cases he : ∃ j, P j x
  · obtain ⟨j,hj⟩ := he
    rw [ite_eq_left ⟨j,hj⟩]
    have hh := Finset.single_le_sum (fun j _ => hpj j) (Finset.mem_univ j)
    simpa only [ite_eq_left hj] using hh
  · rw [ite_eq_right he]
    exact Finset.sum_nonneg (fun j _ => hpj j)

end CoordinateSweeps.Coverage

namespace CoordinateSweeps.Grid
variable (G : Grid)

/- Sharing means using the same decorated line at the same stage. -/

theorem lineShares_symm : ∀ ⦃left right⦄, G.lineShares left right → G.lineShares right left := by
  rintro p q ⟨j,hj⟩
  exact ⟨j,hj.symm⟩

theorem vertexShares_symm : ∀ ⦃left right⦄, G.vertexShares left right → G.vertexShares right left := by
  rintro p q ⟨j,hj⟩
  exact ⟨j,hj.symm⟩

theorem lineSharingRate_nonneg : 0 ≤ G.lineSharingRate := by
  apply Finset.sum_nonneg
  intro j _
  positivity

theorem vertexSharingRate_nonneg : 0 ≤ G.vertexSharingRate := by
  unfold vertexSharingRate
  positivity

theorem probability_lineShares_le (q : G.Slot × G.Slot) :
    (∑ p, if G.lineShares p q then G.endpointWeight p else 0) ≤ G.lineSharingRate := by
  have hu := Coverage.sum_ite_exists_le G.endpointWeight G.endpointWeight_nonneg
    (fun j : Fin G.b => fun p : G.Slot × G.Slot =>
      G.pathLine p.1 p.2 j = G.pathLine q.1 q.2 j)
  calc
    _ ≤ ∑ j : Fin G.b, ∑ p : G.Slot × G.Slot,
        if G.pathLine p.1 p.2 j = G.pathLine q.1 q.2 j then G.endpointWeight p else 0 := by
      convert hu using 1 <;> congr!
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      exact G.probability_path_line j (G.pathLine q.1 q.2 j)

theorem probability_vertexShares_le (q : G.Slot × G.Slot) :
    (∑ p, if G.vertexShares p q then G.endpointWeight p else 0) ≤ G.vertexSharingRate := by
  have hu := Coverage.sum_ite_exists_le G.endpointWeight G.endpointWeight_nonneg
    (fun j : Fin (G.b+1) => fun p : G.Slot × G.Slot =>
      G.pathBetween p.1 p.2 j = G.pathBetween q.1 q.2 j)
  calc
    _ ≤ ∑ j : Fin (G.b+1), ∑ p : G.Slot × G.Slot,
        if G.pathBetween p.1 p.2 j = G.pathBetween q.1 q.2 j then G.endpointWeight p else 0 := by
      convert hu using 1 <;> congr!
    _ = ∑ _j : Fin (G.b+1), (G.size : ℝ)⁻¹ := by
      apply Finset.sum_congr rfl
      intro j _
      exact G.probability_path_vertex j (G.pathBetween q.1 q.2 j)
    _ = _ := by simp [vertexSharingRate, div_eq_mul_inv]

namespace Holes
variable {G} {h k : ℕ}

/- Keep the actual prescribed hole paths, recording their endpoints. -/
theorem path_eq_pathBetween (H : G.Holes h) (hH : H.Feasible)
    (i : Fin h) (t : Fin (G.b+1)) :
    H.path i t = G.pathBetween (H.endpointData i).1 (H.endpointData i).2 t := by
  obtain ⟨ω,hω⟩ := hH
  have hb := G.boundary_eq_pathBetween ω (H.path i 0) t
  have hl := hω i (Fin.last G.b)
  change G.sweep ω (H.path i 0) = H.path i (Fin.last G.b) at hl
  rw [hω i t, hl] at hb
  exact hb

/- A card not covered by any line-sharing has exactly the isolation property
needed for the alternating probability kernel. -/
theorem lineIsolated_of_not_covered (H : G.Holes h) (hH : H.Feasible)
    (x : Fin k → G.Slot × G.Slot) (i : Fin k)
    (hi : i ∉ Coverage.sharingCoverage G.lineShares H.endpointData x) :
    H.LineIsolated (fun a => (x a).1) (fun a => (x a).2) i := by
  have h0 : ¬ ((∃ a : Fin k, i ≠ a ∧ G.lineShares (x i) (x a)) ∨
      ∃ a : Fin h, G.lineShares (x i) (H.endpointData a)) := by
    simpa only [Coverage.sharingCoverage, Coverage.mem_covered] using hi
  constructor
  · intro j a ha
    apply h0
    right
    refine ⟨a,j,?_⟩
    change (fun k : {k : Fin G.b // k ≠ j} => H.path a j.castSucc k) = G.pathLine (x i).1 (x i).2 j at ha
    rw [H.path_eq_pathBetween hH a j.castSucc] at ha
    exact ha.symm
  · intro j a hai ha
    apply h0
    left
    exact ⟨a,hai.symm,j,ha.symm⟩

/- Nonzero Q entries require coverage of every auxiliary particle, for the
literal real line mixture and full feasible path conditioning. -/
theorem placementKernel_ne_zero_coverage (H : G.Holes h) (hH : H.Feasible)
    (x : Fin k → G.Slot × G.Slot) (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hQ : H.placementKernel (fun a => (x a).1) (fun a => (x a).2)
      (fun j => lineLaw (G.bits j) z hz hz') ≠ 0) :
    (Coverage.sharingCoverage G.lineShares H.endpointData x).card = k := by
  have hall : Coverage.sharingCoverage G.lineShares H.endpointData x = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro i
    by_contra hi
    exact hQ (H.placementKernel_lineLaw_eq_zero_of_isolated _ _ i
      (H.lineIsolated_of_not_covered hH x i hi) z hz hz')
  simp [hall]

/- The exact full-array probability bound needed to estimate the counting
Hilbert--Schmidt norm in the many-coordinate sparse case. -/
theorem probability_nonzero_placementKernel_le (H : G.Holes h) (hH : H.Feasible)
    (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hsmall : ((k+h : ℕ) : ℝ) * G.lineSharingRate ≤ 1) :
    Coverage.probability G.endpointWeight (fun x : Fin k → G.Slot × G.Slot =>
      H.placementKernel (fun a => (x a).1) (fun a => (x a).2)
        (fun j => lineLaw (G.bits j) z hz hz') ≠ 0) ≤
      (2 : ℝ)^k * (((k+h : ℕ) : ℝ) * G.lineSharingRate)^((k : ℝ)/2) := by
  have ht := Coverage.probability_coverage_le (I := Fin k) G.lineShares G.lineShares_symm H.endpointData
    G.endpointWeight G.endpointWeight_nonneg G.endpointWeight_total
    G.lineSharingRate G.lineSharingRate_nonneg G.probability_lineShares_le
    (by simpa using hsmall) k
  calc
    _ ≤ Coverage.probability G.endpointWeight (fun x : Fin k → G.Slot × G.Slot =>
        k ≤ (Coverage.sharingCoverage G.lineShares H.endpointData x).card) :=
      Coverage.probability_mono G.endpointWeight G.endpointWeight_nonneg
        (fun x hx => (H.placementKernel_ne_zero_coverage hH x z hz hz' hx).ge)
    _ ≤ _ := by simpa using ht

end Holes
end CoordinateSweeps.Grid

end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Transition
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeColumnLocalChoices _root_.OAI.CoordinateSweeps.Grid.Holes.instFintypeRowLocalChoices _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CoordinateSweeps
namespace Grid.Holes
variable {G : Grid} {h : ℕ}

theorem log_size (G : Grid) : Real.log (G.size : ℝ) =
    ∑ j, Real.log ((2 ^ G.bits j : ℕ) : ℝ) := by
  rw [size,Nat.cast_prod,Real.log_prod]
  intro j _
  positivity

theorem log_probability_zero (H : G.Holes h) :
    Real.log (H.probability 0) = H.cost - (h : ℝ) * Real.log (G.size : ℝ) := by
  have hp (j : Fin G.b) (L : G.Line j) :
      (((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr (H.lineCount_le j L)).ne'
  have hline (j : Fin G.b) (L : G.Line j) :
      Real.log (((2 ^ G.bits j : ℕ) : ℝ)^H.lineCount j L /
        ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ)) =
      (H.lineCount j L : ℝ) * Real.log ((2 ^ G.bits j : ℕ) : ℝ) -
        Real.log ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ) := by
    rw [Real.log_div (by positivity) (hp j L),Real.log_pow]
  have hs (j : Fin G.b) : ∑ L : G.Line j, (H.lineCount j L : ℝ) = h := by
    exact_mod_cast H.sum_lineCount j
  rw [H.probability_zero, Real.log_prod (by
    intro j _
    exact Finset.prod_ne_zero_iff.mpr (fun L _ => inv_ne_zero (hp j L)))]
  have hsum (j : Fin G.b) :
      Real.log (∏ L : G.Line j, (((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ)⁻¹)) =
        ∑ L : G.Line j, -Real.log ((2 ^ G.bits j).descFactorial (H.lineCount j L) : ℝ) := by
    rw [Real.log_prod (fun L _ => inv_ne_zero (hp j L))]
    simp only [Real.log_inv]
  simp_rw [hsum]
  unfold cost
  simp_rw [hline,Finset.sum_sub_distrib,← Finset.sum_mul,hs]
  simp only [Finset.sum_neg_distrib]
  rw [← Finset.mul_sum,log_size]
  ring

theorem probability_zero_pos (H : G.Holes h) : 0 < H.probability 0 := by
  rw [H.probability_zero]
  apply Finset.prod_pos
  intro j _
  apply Finset.prod_pos
  intro L _
  apply inv_pos.mpr
  exact_mod_cast Nat.descFactorial_pos.mpr (H.lineCount_le j L)

theorem probability_zero_eq_exp (H : G.Holes h) :
    H.probability 0 = Real.exp (H.cost - (h : ℝ)*Real.log (G.size : ℝ)) := by
  rw [← H.log_probability_zero,Real.exp_log H.probability_zero_pos]

/- Augmented holes retain the ordered first h trajectories exactly. -/

theorem lineCount_add {t : ℕ} (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) (j : Fin G.b) (L : G.Line j) :
    J.lineCount j L = H.lineCount j L + J.extraCount j L := by
  unfold Extends at he
  unfold lineCount extraCount OnLine
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Fin.sum_univ_add]
  congr 1 <;> apply Finset.sum_congr rfl
  · intro i _
    simp only [he i j.castSucc]
  · intro i _
    split_ifs <;> rfl

theorem sum_extraCount {t : ℕ} (J : G.Holes (h+t)) (j : Fin G.b) :
    ∑ L : G.Line j, J.extraCount j L = t := by
  unfold extraCount
  simp only [Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  have hh (i : Fin t) : (∑ L : G.Line j, if J.OnLine j L (Fin.natAdd h i) then 1 else 0) = 1 := by
    let L₀ : G.Line j := fun k => J.path (Fin.natAdd h i) j.castSucc k
    rw [Finset.sum_eq_single L₀]
    · exact ite_eq_left rfl
    · intro L _ hL
      apply ite_eq_right
      intro he
      exact hL he.symm
    · simp
  simp_rw [hh]
  simp

theorem no_extra_iff {t : ℕ} (J : G.Holes (h+t)) (j : Fin G.b) (L : G.Line j) :
    J.extraCount j L = 0 ↔ ∀ i : Fin t, ¬ J.OnLine j L (Fin.natAdd h i) := by
  simp [extraCount,Finset.card_eq_zero]

theorem lineCompatible_eq_of_no_extra {t : ℕ} (J : G.Holes (h+t))
    (H : G.Holes h) (he : J.Extends H) (j : Fin G.b) (L : G.Line j)
    (hno : J.extraCount j L = 0) (σ : Equiv.Perm (Cube (G.bits j))) :
    J.LineCompatible j L σ ↔ H.LineCompatible j L σ := by
  unfold Extends at he
  have hn := (J.no_extra_iff j L).mp hno
  constructor
  · intro hj i
    have hi : J.OnLine j L (Fin.castAdd t i.val) := by
      change (fun k : {k : Fin G.b // k ≠ j} => J.path (Fin.castAdd t i.val) j.castSucc k) = L
      simpa only [OnLine,he i.val j.castSucc] using i.property
    have hh := hj ⟨Fin.castAdd t i.val,hi⟩
    simpa only [he] using hh
  · intro hh i
    have hcases : (∃ k : Fin h, i.val = Fin.castAdd t k) ∨
        (∃ k : Fin t, i.val = Fin.natAdd h k) :=
      Fin.addCases (fun k : Fin h => Or.inl ⟨k,rfl⟩)
        (fun k : Fin t => Or.inr ⟨k,rfl⟩) i.val
    rcases hcases with ⟨k,hk⟩ | ⟨k,hk⟩
    · have hi : H.OnLine j L k := by
        have hi := i.property
        rw [hk] at hi
        simpa only [OnLine,he] using hi
      have hv := hh ⟨k,hi⟩
      simpa only [hk,he] using hv
    · exact False.elim (hn k (hk ▸ i.property))

end Grid.Holes

namespace FiniteLaw
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem assignments_pos_of_comparison {h : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (hlo : ∀ g, (1/2 : ℝ)*uniform (Equiv.Perm Ω) g ≤ μ g)
    (x y : Fin h ↪ Ω) : 0 < μ.assignments x y := by
  have hp := uniform_assignments_pos x y
  exact lt_of_lt_of_le (by positivity) (le_assignments μ (uniform _) (1/2) hlo x y)

theorem assignments_ratio_comparison {h h' : ℕ} (μ : FiniteLaw (Equiv.Perm Ω))
    (hlo : ∀ g, (1/2 : ℝ)*uniform (Equiv.Perm Ω) g ≤ μ g)
    (hhi : ∀ g, μ g ≤ 2*uniform (Equiv.Perm Ω) g)
    (x y : Fin h ↪ Ω) (x' y' : Fin h' ↪ Ω) :
    μ.assignments x' y' / μ.assignments x y ≤
      4 * ((uniform (Equiv.Perm Ω)).assignments x' y' /
        (uniform (Equiv.Perm Ω)).assignments x y) := by
  have hp := uniform_assignments_pos x y
  calc
    _ ≤ (2*(uniform (Equiv.Perm Ω)).assignments x' y') /
        ((1/2)*(uniform (Equiv.Perm Ω)).assignments x y) :=
      div_le_div₀ (mul_nonneg (by norm_num) ((uniform _).assignments_nonneg x' y'))
        (assignments_le μ (uniform _) 2 hhi x' y') (by positivity)
        (le_assignments μ (uniform _) (1/2) hlo x y)
    _ = _ := by ring
end FiniteLaw

namespace Grid.Holes
variable {G : Grid} {h t : ℕ}

theorem lineProb_nonneg (H : G.Holes h) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) : 0 ≤ H.lineProb j L μ :=
  μ.assignments_nonneg _ _

theorem uniform_lineProb_pos (H : G.Holes h) (j : Fin G.b) (L : G.Line j) :
    0 < H.lineProb j L (FiniteLaw.uniform _) := FiniteLaw.uniform_assignments_pos _ _

theorem lineProb_eq_of_no_extra (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) (j : Fin G.b) (L : G.Line j) (hno : J.extraCount j L = 0)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    J.lineProb j L μ = H.lineProb j L μ := by
  unfold lineProb
  rw [← J.lineProbability_eq,← H.lineProbability_eq]
  let e : {σ // J.LineCompatible j L σ} ≃ {σ // H.LineCompatible j L σ} :=
    Equiv.subtypeEquivRight (J.lineCompatible_eq_of_no_extra H he j L hno)
  exact Equiv.sum_comp e (fun σ => μ σ.val)

theorem sum_usedLine_le (J : G.Holes (h+t)) :
    (∑ j, ∑ L : G.Line j, J.usedLine j L) ≤ t*G.b := by
  calc
    _ ≤ ∑ j, ∑ L : G.Line j, J.extraCount j L := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro L _
      unfold usedLine
      split_ifs <;> omega
    _ = t*G.b := by simp [J.sum_extraCount,Nat.mul_comm]

theorem lineProb_ratio_le (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) (j : Fin G.b) (L : G.Line j)
    (μ : FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (hlo : ∀ g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ μ g)
    (hhi : ∀ g, μ g ≤ 2*FiniteLaw.uniform _ g) :
    J.lineProb j L μ / H.lineProb j L μ ≤
      (4 : ℝ) ^ J.usedLine j L *
        (J.lineProb j L (FiniteLaw.uniform _) / H.lineProb j L (FiniteLaw.uniform _)) := by
  by_cases hno : J.extraCount j L = 0
  · rw [J.lineProb_eq_of_no_extra H he j L hno μ,
      J.lineProb_eq_of_no_extra H he j L hno (FiniteLaw.uniform _)]
    have hp : 0 < H.lineProb j L μ := μ.assignments_pos_of_comparison hlo _ _
    have hu := H.uniform_lineProb_pos j L
    simp [usedLine,hno,hp.ne',hu.ne']
  · simpa only [lineProb,usedLine,ite_eq_right hno,pow_one] using
      μ.assignments_ratio_comparison hlo hhi (H.lineInput j L) (H.lineOutput j L)
        (J.lineInput j L) (J.lineOutput j L)

theorem probability_prod_lineProb (H : G.Holes h) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.probability z = ∏ j, ∏ L : G.Line j, H.lineProb j L (lineLaw (G.bits j) z hz hz') :=
  H.probability_eq_assignments hz hz'

theorem probability_zero_prod_lineProb (H : G.Holes h) :
    H.probability 0 = ∏ j, ∏ L : G.Line j, H.lineProb j L (FiniteLaw.uniform _) := by
  rw [H.probability_prod_lineProb (le_refl 0) zero_le_one]
  congr 1
  funext j
  congr 1
  funext L
  congr 1
  ext σ
  simp [lineLaw,FiniteLaw.mix]

/- Only a line visited by a new path may spend the factor four. Thus the
factor count is at most t*b, not the total number of stage-lines. -/
theorem probability_ratio_comparison (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    J.probability z / H.probability z ≤
      (4 : ℝ)^(t*G.b) * (J.probability 0 / H.probability 0) := by
  let μ (j : Fin G.b) := lineLaw (G.bits j) z hz hz'
  have heq : J.probability z / H.probability z =
      ∏ j, ∏ L : G.Line j, J.lineProb j L (μ j) / H.lineProb j L (μ j) := by
    rw [J.probability_prod_lineProb hz hz',H.probability_prod_lineProb hz hz',
      ← Finset.prod_div_distrib]
    simp_rw [← Finset.prod_div_distrib]
    rfl
  rw [heq]
  calc
    _ ≤ ∏ j, ∏ L : G.Line j, (4 : ℝ)^J.usedLine j L *
        (J.lineProb j L (FiniteLaw.uniform _) / H.lineProb j L (FiniteLaw.uniform _)) := by
      apply Finset.prod_le_prod
      · intro j _
        exact Finset.prod_nonneg (fun L _ => div_nonneg (J.lineProb_nonneg j L _) (H.lineProb_nonneg j L _))
      · intro j _
        apply Finset.prod_le_prod
        · intro L _; exact div_nonneg (J.lineProb_nonneg j L _) (H.lineProb_nonneg j L _)
        · intro L _; exact J.lineProb_ratio_le H he j L (μ j) (hlo j) (hhi j)
    _ = (4 : ℝ)^(∑ j, ∑ L : G.Line j, J.usedLine j L) *
        (J.probability 0 / H.probability 0) := by
      simp_rw [Finset.prod_mul_distrib,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum]
      rw [← J.probability_zero_prod_lineProb,← H.probability_zero_prod_lineProb]
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num) J.sum_usedLine_le)
      (div_nonneg J.probability_zero_pos.le H.probability_zero_pos.le)

/- Source 03-paths (4), in the exactly equal exponential notation. The ratio
is the conditional probability of the complete augmented paths. -/
theorem conditional_transition_bound (J : G.Holes (h+t)) (H : G.Holes h)
    (he : J.Extends H) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    J.probability z / H.probability z ≤
      Real.exp (-(t : ℝ)*Real.log (G.size : ℝ) + J.cost-H.cost + Real.log 4*(t : ℝ)*G.b) := by
  apply (J.probability_ratio_comparison H he hz hz' hlo hhi).trans_eq
  rw [J.probability_zero_eq_exp,H.probability_zero_eq_exp,← Real.exp_sub]
  have h4 : (4 : ℝ)^(t*G.b) = Real.exp (Real.log 4 * (t : ℝ)*G.b) := by
    rw [show Real.log 4 * (t : ℝ)*G.b = (t*G.b : ℕ)*Real.log 4 by push_cast; ring,
      Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<4)]
  rw [h4,← Real.exp_add]
  congr 1
  push_cast
  ring
end Grid.Holes

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k t : ℕ}

/- An injection into the actual available input slots. -/

theorem augment_extends (H : G.Holes h) (u v : Fin t → G.Slot) (hu : H.ValidInput u)
    (ω : G.Choices) (hω : H.Compatible ω) (hv : ∀ i, G.sweep ω (u i) = v i) :
    (H.augment u v hu ω hω hv).Extends H := by
  intro i s; simp

/- Exact equivalence of conditioning events, including all stage boundaries. -/

end CoordinateSweeps.Grid.Holes

/- Multiplicity in a unitary matrix representation is controlled by the
commutant dimension, with exact (unnormalized) character conventions. -/

end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Attachment
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! New work: the actual alternating placement kernel from 04-sparse:eq7.
The preceding definitions/proofs are reused verbatim from the pinned support.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Reused exact conditional transition/potential support from pinned root-02. -/

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

theorem extraProbability_nonneg (H : G.Holes h) (x y : Fin k → G.Slot)
    (A : Finset (Fin k)) (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    0 ≤ H.extraProbability x y A μ := by
  apply Finset.prod_nonneg
  intro j _
  apply Finset.prod_nonneg
  intro L _
  apply div_nonneg <;> apply Finset.sum_nonneg <;> intro σ _ <;>
    split_ifs <;> first | exact (μ j).nonneg σ | exact le_rfl

/- Faithful finite-event application of the transition comparison: the selected
extra paths are appended to the holes only when their joint event is possible. -/
theorem scaled_extraProbability_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    (G.size : ℝ)^A.card * H.extraProbability x y A (fun j => lineLaw (G.bits j) z hz hz') ≤
      Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b) := by
  classical
  rw [H.extraProbability_eq_conditionalEndpoint]
  by_cases he : ∃ ω, H.Compatible ω ∧ G.endpointEvent x y A ω
  · obtain ⟨ω,hω,he⟩ := he
    let u := fun i => x (selected A i)
    let v := fun i => y (selected A i)
    have hv : ∀ i, G.sweep ω (u i) = v i := (endpointEvent_iff_selected x y A ω).mp he
    let J := H.augment u v (H.validInput_selected x hx A) ω hω hv
    have heq : H.conditionalEndpointProbability x y A (fun j => lineLaw (G.bits j) z hz hz') =
        J.probability z / H.probability z := by
      unfold conditionalEndpointProbability
      rw [H.lineMass_hole_normalizer hz hz']
      congr 1
      rw [← J.lineMass_hole_normalizer hz hz']
      apply Finset.sum_congr rfl
      intro ν _
      have hj : J.Compatible ν ↔ H.Compatible ν ∧ G.endpointEvent x y A ν := by
        dsimp [J]
        rw [H.augment_compatible_iff, endpointEvent_iff_selected]
      simp only [hj]
    rw [heq]
    have ht := J.conditional_transition_bound H
      (H.augment_extends u v (H.validInput_selected x hx A) ω hω hv) hz hz' hlo hhi
    have hs : (0 : ℝ) < G.size := by
      unfold Grid.size
      positivity
    have hpow : (G.size : ℝ)^A.card = Real.exp ((A.card : ℝ)*Real.log G.size) := by
      rw [Real.exp_nat_mul, Real.exp_log hs]
    calc
      _ ≤ (G.size : ℝ)^A.card *
          Real.exp (-(A.card : ℝ)*Real.log G.size + J.cost-H.cost +
            Real.log 4*(A.card : ℝ)*G.b) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = Real.exp (J.cost-H.cost + Real.log 4*(A.card : ℝ)*G.b) := by
        rw [hpow, ← Real.exp_add]
        congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hAk : (A.card : ℝ) ≤ k := by exact_mod_cast (show A.card ≤ k by simpa using Finset.card_le_univ A)
        have hc := J.cost_le
        have hn := H.cost_nonneg
        have hb : (0 : ℝ) ≤ G.b := by positivity
        have hl : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
        have hbk := mul_le_mul_of_nonneg_left hAk hb
        have hlk := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hAk hl) hb
        push_cast at hc
        nlinarith
  · have hn : ∀ ω, ¬ (H.Compatible ω ∧ G.endpointEvent x y A ω) := by
      simpa only [not_exists] using he
    simp only [conditionalEndpointProbability, ite_eq_right (hn _), Finset.sum_const_zero,
      zero_div, mul_zero]
    exact (Real.exp_pos _).le

/- Source 04:eq8, with an explicit absolute constant in place of O(·).
Only valid input placements are needed; impossible output events contribute zero. -/
theorem scaled_placementKernel_abs_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    |(G.size : ℝ)^k * H.placementKernel x y (fun j => lineLaw (G.bits j) z hz hz')| ≤
      (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b) := by
  classical
  have hs : (G.size : ℝ) ≠ 0 := by
    unfold Grid.size
    positivity
  rw [placementKernel, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]
  calc
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        |(-1 : ℝ)^(k-A.card) * (G.size : ℝ)^A.card *
          H.extraProbability x y A (fun j => lineLaw (G.bits j) z hz hz')| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        (G.size : ℝ)^A.card * H.extraProbability x y A (fun j => lineLaw (G.bits j) z hz hz') := by
      apply Finset.sum_congr rfl
      intro A _
      rw [abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_nonneg (by positivity : 0 ≤ (G.size : ℝ)^A.card),
        abs_of_nonneg (H.extraProbability_nonneg _ _ _ _)]
    _ ≤ ∑ A ∈ (Finset.univ : Finset (Fin k)).powerset,
        Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b) := by
      apply Finset.sum_le_sum
      intro A _
      exact H.scaled_extraProbability_le x y hx A hz hz' hlo hhi
    _ = _ := by simp

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

theorem endpoint_productMass (p : Fin k → G.Slot × G.Slot) :
    Coverage.productMass G.endpointWeight p = (G.size : ℝ)⁻¹^(2*k) := by
  simp [Coverage.productMass, Grid.endpointWeight, FiniteLaw.uniform,
    Fintype.card_prod, G.card_slot, mul_pow, pow_mul, mul_comm, pow_two]

/- Rewriting the counting norm using independent full-grid endpoints never
conditions the auxiliary trajectories on being valid placements. -/
theorem placementHSsq_eq_full (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    H.placementHSsq (k := k) μ =
      ∑ p : Fin k → G.Slot × G.Slot,
        Coverage.productMass G.endpointWeight p *
          if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
            ((G.size : ℝ)^k * H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2
          else 0 := by
  classical
  have hs : (G.size : ℝ) ≠ 0 := by unfold Grid.size; positivity
  have hterm (p : Fin k → G.Slot × G.Slot) :
      (if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
          (H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2 else 0) =
        Coverage.productMass G.endpointWeight p *
          if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
            ((G.size : ℝ)^k * H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2
          else 0 := by
    rw [endpoint_productMass]
    split_ifs
    · have hid : (G.size : ℝ)⁻¹^(2*k) * ((G.size : ℝ)^k)^2 = 1 := by
        rw [← pow_mul, Nat.mul_comm k 2, ← mul_pow, inv_mul_cancel₀ hs, one_pow]
      rw [mul_pow, ← mul_assoc, hid, one_mul]
    · simp
  let e : (Fin k → G.Slot × G.Slot) ≃ ((Fin k → G.Slot) × (Fin k → G.Slot)) :=
    ⟨fun p => (fun i => (p i).1, fun i => (p i).2),
      fun p i => (p.1 i, p.2 i), fun _ => rfl, fun _ => rfl⟩
  calc
    _ = ∑ p : (Fin k → G.Slot) × (Fin k → G.Slot),
        if H.ValidInput p.1 ∧ H.ValidOutput p.2 then (H.placementKernel p.1 p.2 μ)^2 else 0 := by
      rw [Fintype.sum_prod_type]; rfl
    _ = ∑ p : Fin k → G.Slot × G.Slot,
        if H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2) then
          (H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ)^2 else 0 :=
      (Equiv.sum_comp e (fun p =>
        if H.ValidInput p.1 ∧ H.ValidOutput p.2 then (H.placementKernel p.1 p.2 μ)^2 else 0)).symm
    _ = _ := Finset.sum_congr rfl (fun p _ => hterm p)

/- Source 04:eqs8--9 combined, with an explicit counting HS estimate.
This is the direct, unweakened many-coordinate sparse-kernel estimate. -/
theorem placementHSsq_le (H : G.Holes h) (hH : H.Feasible)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2 : ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g)
    (hsmall : ((k+h : ℕ) : ℝ)*G.lineSharingRate ≤ 1) :
    H.placementHSsq (k := k) (fun j => lineLaw (G.bits j) z hz hz') ≤
      ((2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b))^2 *
        ((2 : ℝ)^k * (((k+h : ℕ) : ℝ)*G.lineSharingRate)^((k : ℝ)/2)) := by
  classical
  let μ := fun j => lineLaw (G.bits j) z hz hz'
  let M := (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k) + Real.log 4*k*G.b)
  have hM : 0 ≤ M := by positivity
  rw [H.placementHSsq_eq_full]
  calc
    _ ≤ ∑ p : Fin k → G.Slot × G.Slot,
        Coverage.productMass G.endpointWeight p *
          if H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ ≠ 0 then M^2 else 0 := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _
        (Coverage.productMass_nonneg G.endpointWeight G.endpointWeight_nonneg p)
      by_cases he : H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ = 0
      · simp only [μ] at he
        simp [μ, he]
      · rw [ite_eq_left he]
        split_ifs with hp
        · have h := H.scaled_placementKernel_abs_le (fun i => (p i).1) (fun i => (p i).2) hp.1 hz hz' hlo hhi
          have hh := (sq_le_sq₀ (abs_nonneg _) hM).mpr h
          simpa only [sq_abs] using hh
        · positivity
    _ = M^2 * Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
        H.placementKernel (fun i => (p i).1) (fun i => (p i).2) μ ≠ 0) := by
      rw [Coverage.probability, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (H.probability_nonzero_placementKernel_le hH z hz hz' hsmall) (sq_nonneg M)

end CoordinateSweeps.Grid.Holes

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Moments_LineExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]

/- The moment functional of independent line variables, defined algebraically
so only the finitely many moments actually used need be integrable. -/

omit [DecidableEq L] in
theorem tensorMoment_sum (m : L → ℕ → ℝ) (p : MvPolynomial L ℝ) :
    tensorMoment m p = ∑ d ∈ p.support, p.coeff d * ∏ l, m l (d l) := by
  conv_lhs => rw [p.as_sum]
  simp only [map_sum, tensorMoment_monomial]

/- Multiplicativity is asserted ONLY across disjoint sets of line variables. -/
omit [DecidableEq L] in
theorem tensorMoment_mul_disjoint (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (p q : MvPolynomial L ℝ) (hd : Disjoint p.vars q.vars) :
    tensorMoment m (p*q) = tensorMoment m p * tensorMoment m q := by
  conv_lhs => rw [p.as_sum, q.as_sum]
  simp only [Finset.sum_mul, Finset.mul_sum, map_sum, monomial_mul_monomial, tensorMoment_monomial]
  rw [tensorMoment_sum, tensorMoment_sum, Finset.sum_mul, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd'
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he'
  have heq : ∀ l, m l ((d+e) l) = m l (d l) * m l (e l) := by
    intro l
    by_cases hdl : d l = 0
    · simp [hdl, hm]
    · have hdp : l ∈ p.vars := p.support_subset_vars_of_mem_support hd'
        (Finsupp.mem_support_iff.mpr hdl)
      have hnot : l ∉ q.vars := fun he => Finset.disjoint_left.mp hd hdp he
      have hel := MvPolynomial.mem_support_notMem_vars_zero he' hnot
      simp [hel, hm]
  simp only [heq, Finset.prod_mul_distrib]
  ring

/- One-variable powers really have just the specified one-line moment. -/
omit [DecidableEq L] in
theorem tensorMoment_X_pow (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1) (l : L) (n : ℕ) :
    tensorMoment m (X l ^ n) = m l n := by
  rw [X_pow_eq_monomial, tensorMoment_monomial, one_mul]
  rw [Finset.prod_eq_single l]
  · simp
  · intro a _ ha
    simp [ha, hm]
  · simp

/- Factorization of arbitrary polynomials, one for each distinct line. -/
theorem tensorMoment_prod_separated (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (S : Finset L) (p : L → MvPolynomial L ℝ) (hp : ∀ l ∈ S, (p l).vars ⊆ {l}) :
    tensorMoment m (∏ l ∈ S, p l) = ∏ l ∈ S, tensorMoment m (p l) := by
  induction S using Finset.induction_on with
  | empty => simp [tensorMoment_one m hm]
  | @insert l S hl ih =>
    rw [Finset.prod_insert hl, tensorMoment_mul_disjoint m hm,
      Finset.prod_insert hl, ih (fun a ha => hp a (Finset.mem_insert_of_mem ha))]
    apply Finset.disjoint_left.mpr
    intro a ha hb
    have hal : a = l := Finset.mem_singleton.mp (hp l (Finset.mem_insert_self _ _) ha)
    subst a
    have hv := MvPolynomial.vars_prod p hb
    simp only [Finset.mem_biUnion] at hv
    obtain ⟨a,ha,hla⟩ := hv
    have hla' : l = a := Finset.mem_singleton.mp (hp a (Finset.mem_insert_of_mem ha) hla)
    exact hl (hla'.symm ▸ ha)

/- The exact linear functional for a fixed subset of the non-good paths.
Translation by -1 retains all correlations between repeated uses of a line. -/

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]

omit [Fintype L] in
theorem vars_X_centered_power (l : L) (r u : ℕ) :
    (((X l : MvPolynomial L ℝ)^r) * (X l - 1)^u).vars ⊆ {l} := by
  apply (MvPolynomial.vars_mul _ _).trans
  apply Finset.union_subset
  · exact (MvPolynomial.vars_pow _ _).trans (by simp)
  · apply (MvPolynomial.vars_pow _ _).trans
    exact (MvPolynomial.vars_sub_subset (p := (X l : MvPolynomial L ℝ)) (q := 1)).trans (by simp)

omit [DecidableEq L] in
theorem tensorMoment_X_centered_power (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (l : L) (r u : ℕ) :
    tensorMoment m ((X l : MvPolynomial L ℝ)^r * (X l-1)^u) =
      lineCenteredMoment m l r u := by
  rw [sub_pow, Finset.mul_sum, map_sum]
  unfold lineCenteredMoment
  apply Finset.sum_congr rfl
  intro a _
  have ht : (X l : MvPolynomial L ℝ)^r *
      ((-1)^(a+u) * X l^a * 1^(u-a) * (u.choose a : MvPolynomial L ℝ)) =
      (((-1 : ℝ)^(a+u) * (u.choose a : ℝ)) • (X l : MvPolynomial L ℝ)^(r+a)) := by
    rw [Algebra.smul_def, map_mul, map_pow, map_neg, map_one, map_natCast, pow_add]
    ring
  rw [ht, map_smul, tensorMoment_X_pow m hm, smul_eq_mul]

/- Repeated uses of one line are collected into a SINGLE mixed centered moment. -/
theorem shiftedMoment_monomial (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (r : L → ℕ) (d : L →₀ ℕ) (a : ℝ) :
    shiftedMoment m r (monomial d a) = a * ∏ l, lineCenteredMoment m l (r l) (d l) := by
  unfold shiftedMoment
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_fintype d _ (by simp)]
  have he : (∏ l, (X l : MvPolynomial L ℝ)^r l) *
      ((algebraMap ℝ (MvPolynomial L ℝ)) a * ∏ l, (X l-1)^d l) =
      a • (∏ l, (X l : MvPolynomial L ℝ)^r l * (X l-1)^d l) := by
    rw [Finset.prod_mul_distrib, Algebra.smul_def]
    ring
  rw [he, map_smul, tensorMoment_prod_separated m hm _ _ (fun l _ => vars_X_centered_power l _ _)]
  simp only [tensorMoment_X_centered_power m hm, smul_eq_mul]

/- Coefficientwise nonnegativity, used only for the positive centered expansion. -/

omit [Fintype L] in
theorem nonnegCoeffs_one : NonnegCoeffs (1 : MvPolynomial L ℝ) := by
  intro d
  simp only [coeff_one]
  split_ifs <;> norm_num

omit [Fintype L] in
theorem NonnegCoeffs.mul {p q : MvPolynomial L ℝ} (hp : NonnegCoeffs p) (hq : NonnegCoeffs q) :
    NonnegCoeffs (p*q) := by
  intro d
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun e _ => mul_nonneg (hp e.1) (hq e.2))

omit [Fintype L] in
theorem nonnegCoeffs_X (l : L) : NonnegCoeffs (X l : MvPolynomial L ℝ) := by
  intro d
  simp only [coeff_X]
  split_ifs <;> norm_num

omit [Fintype L] [DecidableEq L] in
theorem nonnegCoeffs_prod {I : Type*} (S : Finset I) (p : I → MvPolynomial L ℝ)
    (hp : ∀ i ∈ S, NonnegCoeffs (p i)) : NonnegCoeffs (∏ i ∈ S, p i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (nonnegCoeffs_one (L := L))
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul (ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)))

omit [Fintype L] [DecidableEq L] in
theorem nonnegCoeffs_sum {I : Type*} (S : Finset I) (p : I → MvPolynomial L ℝ)
    (hp : ∀ i ∈ S, NonnegCoeffs (p i)) : NonnegCoeffs (∑ i ∈ S, p i) := by
  intro d
  rw [coeff_sum]
  exact Finset.sum_nonneg (fun i hi => hp i hi d)

/- Exact tensor moment estimate. Its potential premise is local in each
line and each used degree, not independence of particle factors. -/
theorem shiftedMoment_abs_le_eval (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (r : L → ℕ) (p : MvPolynomial L ℝ) (hp : NonnegCoeffs p)
    (C t : ℝ)
    (hb : ∀ d ∈ p.support, ∀ l,
      |lineCenteredMoment m l (r l) (d l)| ≤ C^(r l) * t^(d l)) :
    |shiftedMoment m r p| ≤ C^(∑ l, r l) * MvPolynomial.eval (fun _ => t) p := by
  conv_lhs => rw [p.as_sum]
  rw [map_sum]
  calc
    _ ≤ ∑ d ∈ p.support, |shiftedMoment m r (monomial d (p.coeff d))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ p.support, p.coeff d * ∏ l, (C^(r l) * t^(d l)) := by
      apply Finset.sum_le_sum
      intro d hd
      rw [shiftedMoment_monomial m hm, abs_mul, abs_of_nonneg (hp d), Finset.abs_prod]
      exact mul_le_mul_of_nonneg_left
        (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun l _ => hb d hd l)) (hp d)
    _ = C^(∑ l, r l) * MvPolynomial.eval (fun _ => t) p := by
      conv_rhs => rw [p.as_sum]
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype d _ (by simp),
        Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
      ring

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]

/- Positive expansion for a centered particle factor. This is a sum over
NONEMPTY subsets of its stages; no independence of particle factors is used. -/

omit [Fintype L] [DecidableEq L] [Fintype J] in
theorem pathExpansion_eq (S : Finset J) (f : J → L) :
    pathExpansion S f = (∏ j ∈ S, ((X (f j) : MvPolynomial L ℝ)+1))-1 := by
  have he := Finset.sum_erase_add S.powerset (fun T => ∏ j ∈ T, (X (f j) : MvPolynomial L ℝ))
    (Finset.empty_mem_powerset S)
  simp only [Finset.prod_empty] at he
  unfold pathExpansion
  rw [Finset.prod_add_one]
  exact eq_sub_of_add_eq he

omit [Fintype L] [Fintype J] in
theorem pathExpansion_nonneg (S : Finset J) (f : J → L) :
    NonnegCoeffs (pathExpansion S f) := by
  exact nonnegCoeffs_sum _ _ (fun T _ => nonnegCoeffs_prod T _ (fun j _ => nonnegCoeffs_X _))

omit [Fintype L] [Fintype J] in
theorem pathExpansion_degree (S : Finset J) (f : J → L) (l : L) :
    (pathExpansion S f).degreeOf l ≤ ∑ j ∈ S, if f j = l then 1 else 0 := by
  rw [pathExpansion_eq]
  apply (MvPolynomial.degreeOf_sub_le _ _ _).trans
  rw [MvPolynomial.degreeOf_one, max_eq_left (Nat.zero_le _)]
  apply (MvPolynomial.degreeOf_prod_le _ _ _).trans
  apply Finset.sum_le_sum
  intro j _
  have hd := MvPolynomial.degreeOf_add_le l (X (f j) : MvPolynomial L ℝ) 1
  simpa only [MvPolynomial.degreeOf_one, MvPolynomial.degreeOf_X, eq_comm,
    max_eq_left (Nat.zero_le _)] using hd

omit [Fintype L] [DecidableEq L] [Fintype J] in
theorem pathExpansion_eval (S : Finset J) (f : J → L) (t : ℝ) :
    MvPolynomial.eval (fun _ => t) (pathExpansion S f) = (1+t)^S.card-1 := by
  rw [pathExpansion_eq]
  simp [add_comm]

omit [Fintype L] [DecidableEq L] [Fintype J] in
theorem pathExpansion_shift (S : Finset J) (f : J → L) :
    MvPolynomial.aeval (fun l => (X l : MvPolynomial L ℝ)-1) (pathExpansion S f) =
      (∏ j ∈ S, (X (f j) : MvPolynomial L ℝ))-1 := by
  rw [pathExpansion_eq]
  simp

/- Combined centered expansion, with the actual same variable on a shared line. -/

omit [Fintype L] [DecidableEq I] in
theorem goodExpansion_nonneg (G : Finset I) (path : I → J → L) :
    NonnegCoeffs (goodExpansion G path) := by
  exact nonnegCoeffs_prod _ _ (fun i _ => pathExpansion_nonneg _ _)

omit [Fintype L] [DecidableEq I] in
theorem goodExpansion_degree (G : Finset I) (path : I → J → L) (l : L) :
    (goodExpansion G path).degreeOf l ≤ ∑ i ∈ G, ∑ j : J, if path i j = l then 1 else 0 := by
  exact (MvPolynomial.degreeOf_prod_le _ _ _).trans
    (Finset.sum_le_sum (fun _ _ => pathExpansion_degree _ _ _))

omit [Fintype L] [DecidableEq L] [DecidableEq I] in
theorem goodExpansion_eval (G : Finset I) (path : I → J → L) (t : ℝ) :
    MvPolynomial.eval (fun _ => t) (goodExpansion G path) =
      ((1+t)^Fintype.card J-1)^G.card := by
  simp [goodExpansion, pathExpansion_eval]

/- Uniform estimate for (1+C*x)^b-1, retaining one small factor per particle. -/
theorem centered_power_le (C x : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (hx1 : x ≤ 1) (b : ℕ) :
    (1+C*x)^b-1 ≤ ((1+C)^b-1)*x := by
  induction b with
  | zero => simp
  | succ b ih =>
    have hCx : 0 ≤ C*x := mul_nonneg hC hx
    have hb : 1 ≤ (1+C)^b := one_le_pow₀ (by linarith)
    have hsmall : C*x ≤ C := mul_le_of_le_one_right hC hx1
    have hmul := mul_le_mul_of_nonneg_right ih (by linarith : 0 ≤ 1+C*x)
    have her : ((1+C)^b-1)*x*(1+C*x) ≤ ((1+C)^b-1)*x*(1+C) := by
      exact mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg (by linarith) hx)
    rw [pow_succ, pow_succ]
    nlinarith

omit [Fintype L] [DecidableEq L] [DecidableEq I] in
theorem goodExpansion_eval_le (G : Finset I) (path : I → J → L)
    (C x : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    MvPolynomial.eval (fun _ => C*x) (goodExpansion G path) ≤
      (1+C)^(Fintype.card J*G.card) * x^G.card := by
  rw [goodExpansion_eval]
  have h1 : 1 ≤ (1+C*x)^Fintype.card J := one_le_pow₀ (by nlinarith)
  have he := centered_power_le C x hC hx hx1 (Fintype.card J)
  have hu : ((1+C)^Fintype.card J-1)*x ≤ (1+C)^Fintype.card J*x := by nlinarith
  calc
    _ ≤ ((1+C)^Fintype.card J*x)^G.card :=
      pow_le_pow_left₀ (sub_nonneg.mpr h1) (he.trans hu) _
    _ = _ := by rw [mul_pow, ← pow_mul]

/- Core shared-line estimate behind source (10), before inserting the actual
gamma moments. Each line degree is limited by the count of good trajectories
through it, and each good path supplies a factor sqrt(eta). -/
omit [DecidableEq I] in
theorem goodExpansion_moment_le (m : L → ℕ → ℝ) (hm : ∀ l, m l 0 = 1)
    (r : L → ℕ) (G : Finset I) (path : I → J → L)
    (C x : ℝ) (hC : 0 ≤ C) (hx : 0 ≤ x) (hx1 : x ≤ 1)
    (hb : ∀ l u, u ≤ (∑ i ∈ G, ∑ j : J, if path i j = l then 1 else 0) →
      |lineCenteredMoment m l (r l) u| ≤ C^(r l) * (C*x)^u) :
    |shiftedMoment m r (goodExpansion G path)| ≤
      C^(∑ l, r l) * (1+C)^(Fintype.card J*G.card) * x^G.card := by
  have he := shiftedMoment_abs_le_eval m hm r (goodExpansion G path)
    (goodExpansion_nonneg G path) C (C*x) (by
      intro d hd l
      exact hb l (d l) ((MvPolynomial.monomial_le_degreeOf l hd).trans
        (goodExpansion_degree G path l)))
  exact he.trans ((mul_le_mul_of_nonneg_left
    (goodExpansion_eval_le G path C x hC hx hx1) (pow_nonneg hC _)).trans_eq (by ring))

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.MomentExpansion
variable {L : Type*} [Fintype L] [DecidableEq L]
variable {I J : Type*} [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
theorem tensorMoment_path_monomial (m : L → ℕ → ℝ) (r : L → ℕ)
    (A : Finset I) (path : I → J → L) :
    tensorMoment m ((∏ l, (X l : MvPolynomial L ℝ)^r l) *
      ∏ i ∈ A, ∏ j : J, X (path i j)) =
        ∏ l, m l (r l+incidenceCount A path l) := by
  have hr : (∏ l, (X l : MvPolynomial L ℝ)^r l) =
      monomial (∑ l, Finsupp.single l (r l)) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    apply Finset.prod_congr rfl
    intro l _
    exact X_pow_eq_monomial
  have hp : (∏ i ∈ A, ∏ j : J, (X (path i j) : MvPolynomial L ℝ)) =
      monomial (∑ i ∈ A, ∑ j : J, Finsupp.single (path i j) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    apply Finset.prod_congr rfl
    intro i _
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [hr, hp, MvPolynomial.monomial_mul_monomial, one_mul, tensorMoment_monomial, one_mul]
  apply Finset.prod_congr rfl
  intro l _
  congr 1
  simp [incidenceCount, Finsupp.single_apply, eq_comm]

/- Exact alternation identity. The summation set is the omitted subset of good
particles, so its sign is (-1)^|A|. This is source (10)'s inside-expectation
formula, with all shared-line correlations retained by the linear functional. -/
theorem shiftedMoment_goodExpansion_eq (m : L → ℕ → ℝ) (r : L → ℕ)
    (G : Finset I) (path : I → J → L) :
    shiftedMoment m r (goodExpansion G path) =
      ∑ A ∈ G.powerset, (-1 : ℝ)^A.card * ∏ l, m l (r l+incidenceCount (G\A) path l) := by
  unfold shiftedMoment
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.mulLeft_apply,
    goodExpansion, map_prod, pathExpansion_shift]
  rw [Finset.prod_sub, Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro A _
  simp only [Finset.prod_const_one, mul_one]
  have he : (∏ l, (X l : MvPolynomial L ℝ)^r l) *
      ((-1 : MvPolynomial L ℝ)^A.card *
        ∏ i ∈ G\A, ∏ j : J, X (path i j)) =
      (-1 : ℝ)^A.card • ((∏ l, (X l : MvPolynomial L ℝ)^r l) *
        ∏ i ∈ G\A, ∏ j : J, X (path i j)) := by
    rw [Algebra.smul_def, map_pow, map_neg, map_one]
    ring
  rw [he, map_smul, tensorMoment_path_monomial, smul_eq_mul]

end CoordinateSweeps.MomentExpansion

/- Gamma-moment support. -/

/- The analytic light-line obligation 04-sparse.tex (11).  The distribution
is exactly Mathlib's Gamma(shape, unit rate), not an assumed random variable. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators

namespace CoordinateSweeps

theorem integral_gamma_eq {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    (∫ x, f x ∂gammaMeasure a r) =
      ∫ x in Ioi 0, (r^a / Gamma a * x^(a-1) * exp (-(r*x))) * f x := by
  rw [gammaMeasure]
  change (∫ x, f x ∂volume.withDensity (fun x => ENNReal.ofReal (gammaPDFReal a r x))) = _
  rw [integral_withDensity_eq_integral_toReal_smul
    ((measurable_gammaPDFReal a r).ennreal_ofReal) (ae_of_all _ (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (gammaPDFReal_nonneg ha hr _), smul_eq_mul]
  have he : (fun x => gammaPDFReal a r x * f x) =
      (Ici 0).indicator (fun x => (r^a / Gamma a * x^(a-1) * exp (-(r*x))) * f x) := by
    funext x
    by_cases hx : 0 ≤ x <;> simp [gammaPDFReal, hx, indicator_of_mem, indicator_of_notMem]
  rw [he, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]

theorem gamma_mgf {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    (∫ x, exp (t*x) ∂gammaMeasure a 1) = (1/(1-t))^a := by
  rw [integral_gamma_eq ha zero_lt_one]
  simp only [one_rpow, one_mul]
  have he : (fun x : ℝ => (1 / Gamma a * x^(a-1) * exp (-x)) * exp (t*x)) =
      fun x => (1 / Gamma a) * (x^(a-1) * exp (-((1-t)*x))) := by
    funext x
    rw [mul_assoc, mul_assoc, ← exp_add]
    congr 3
    ring
  rw [he, integral_const_mul, integral_rpow_mul_exp_neg_mul_Ioi ha (sub_pos.mpr ht)]
  field_simp [(Gamma_pos_of_pos ha).ne']

theorem gamma_centered_mgf {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    (∫ x, exp (t*(x-a)) ∂gammaMeasure a 1) = exp (a*(-t-log (1-t))) := by
  have he : (fun x => exp (t*(x-a))) = fun x => exp (-t*a) * exp (t*x) := by
    funext x
    rw [← exp_add]
    congr 1
    ring
  rw [he, integral_const_mul, gamma_mgf ha ht,
    rpow_def_of_pos (one_div_pos.mpr (sub_pos.mpr ht)), ← exp_add,
    one_div, log_inv]
  congr 1
  ring

theorem gamma_centered_mgf_integrable {a t : ℝ} (ha : 0 < a) (ht : t < 1) :
    Integrable (fun x => exp (t*(x-a))) (gammaMeasure a 1) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_centered_mgf ha ht]
  exact (exp_pos _).ne'

theorem log_mgf_bound {t : ℝ} (ht : |t| ≤ 1/2) : -t - log (1-t) ≤ 2*t^2 := by
  have ht1 : |t| < 1 := by linarith
  have hh := abs_log_sub_add_sum_range_le ht1 1
  norm_num at hh
  have hb : |t|^2 / (1-|t|) ≤ 2*t^2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1-|t|)).mpr
    rw [sq_abs]
    nlinarith [sq_nonneg t]
  rw [sq_abs] at hb
  have hl := neg_le_abs (t + log (1-t))
  linarith

theorem gamma_centered_mgf_le {a t : ℝ} (ha : 0 < a) (ht : |t| ≤ 1/2) :
    (∫ x, exp (t*(x-a)) ∂gammaMeasure a 1) ≤ exp (2*a*t^2) := by
  rw [gamma_centered_mgf ha (by have := le_abs_self t; linarith)]
  apply exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left (log_mgf_bound ht) ha.le]

/- Pointwise exponential domination, used to obtain the actual centered
moments without a separate probabilistic Chernoff axiom. -/
theorem abs_pow_le_exp_sum (x : ℝ) (u : ℕ) {t : ℝ} (ht : 0 < t) :
    |x|^u ≤ ((u : ℝ)/t)^u * (exp (t*x) + exp (-t*x)) := by
  have hp := rpow_abs_le_mul_max_exp_of_pos x (Nat.cast_nonneg u) ht
  rw [rpow_natCast, rpow_natCast] at hp
  apply hp.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact max_le (le_add_of_nonneg_right (exp_nonneg _))
    (le_add_of_nonneg_left (exp_nonneg _))

theorem abs_pow_integrable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (u : ℕ) {t : ℝ} (ht : 0 < t)
    (hp : Integrable (fun x => exp (t * X x)) μ)
    (hn : Integrable (fun x => exp (-t * X x)) μ) :
    Integrable (fun x => |X x|^u) μ := by
  apply ((hp.add hn).const_mul (((u : ℝ)/t)^u)).mono'
  · exact (hX.abs.pow_const u).aestronglyMeasurable
  · filter_upwards [] with x
    simpa only [Real.norm_eq_abs, abs_pow, abs_abs, Pi.add_apply] using abs_pow_le_exp_sum (X x) u ht

theorem abs_pow_integral_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} (hX : AEMeasurable X μ) (u : ℕ) {t : ℝ} (ht : 0 < t)
    (hp : Integrable (fun x => exp (t * X x)) μ)
    (hn : Integrable (fun x => exp (-t * X x)) μ) :
    (∫ x, |X x|^u ∂μ) ≤ ((u : ℝ)/t)^u *
      ((∫ x, exp (t*X x) ∂μ) + (∫ x, exp (-t*X x) ∂μ)) := by
  calc
    _ ≤ ∫ x, ((u : ℝ)/t)^u * (exp (t*X x) + exp (-t*X x)) ∂μ :=
      integral_mono (abs_pow_integrable hX u ht hp hn)
        ((hp.add hn).const_mul _) (fun x => abs_pow_le_exp_sum (X x) u ht)
    _ = _ := by rw [integral_const_mul, integral_add hp hn]

/- A centered gamma moment in the range needed by every light line. -/
theorem gamma_abs_centered_moment_le {a : ℝ} (ha : 0 < a) {u : ℕ}
    (hu : 1 ≤ u) (hua : 4*(u : ℝ) ≤ a) :
    (∫ x, |x-a|^u ∂gammaMeasure a 1) ≤
      (2 * exp 2 * Real.sqrt (a*u))^u := by
  let t := Real.sqrt ((u : ℝ)/a)
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have ht : 0 < t := Real.sqrt_pos.mpr (div_pos hu0 ha)
  have ht2 : t^2 = (u : ℝ)/a := Real.sq_sqrt (by positivity)
  have ht_half : t ≤ 1/2 := by
    have hh : (u : ℝ)/a ≤ 1/4 := (div_le_iff₀ ha).mpr (by linarith)
    nlinarith
  have htab : |t| ≤ 1/2 := by rw [abs_of_pos ht]; exact ht_half
  have hp := gamma_centered_mgf_integrable ha (show t < 1 by linarith)
  have hn := gamma_centered_mgf_integrable ha (show -t < 1 by linarith)
  have hh := abs_pow_integral_le
    (X := fun x : ℝ => x-a) (by fun_prop) u ht hp hn
  have hplus := gamma_centered_mgf_le ha htab
  have hminus := gamma_centered_mgf_le ha (t := -t) (by simpa only [abs_neg] using htab)
  have hat : a*t^2 = (u : ℝ) := by rw [ht2]; field_simp
  have hratio : (u : ℝ)/t = Real.sqrt (a*u) := by
    have ht0 : t ≠ 0 := ht.ne'
    have he : (u : ℝ)/t * ((u : ℝ)/t) = a*u := by
      field_simp
      nlinarith [hat]
    have hs := Real.sq_sqrt (show 0 ≤ a*(u : ℝ) by positivity)
    have hr : 0 ≤ (u : ℝ)/t := by positivity
    nlinarith [he, Real.sqrt_nonneg (a*u)]
  calc
    _ ≤ ((u : ℝ)/t)^u * (exp (2*a*t^2) + exp (2*a*(-t)^2)) :=
      hh.trans (mul_le_mul_of_nonneg_left (add_le_add hplus hminus) (by positivity))
    _ = 2 * (exp 2 * Real.sqrt (a*u))^u := by
      rw [hratio, neg_sq]
      have he : 2*a*t^2 = 2*(u : ℝ) := by nlinarith [hat]
      rw [he, mul_comm (2 : ℝ) (u : ℝ), exp_nat_mul, mul_pow]
      ring
    _ ≤ (2 * exp 2 * Real.sqrt (a*u))^u := by
      have htwo : (2 : ℝ) ≤ 2^u := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hu)
      calc
        _ ≤ 2^u * (exp 2 * Real.sqrt (a*u))^u :=
          mul_le_mul_of_nonneg_right htwo (by positivity)
        _ = _ := by rw [← mul_pow]; congr 1; ring

/- No restriction at the density's null endpoint is needed. -/
theorem integral_gamma_congr {a r : ℝ} (ha : 0 < a) (hr : 0 < r)
    {f g : ℝ → ℝ} (hfg : ∀ x, 0 < x → f x = g x) :
    (∫ x, f x ∂gammaMeasure a r) = ∫ x, g x ∂gammaMeasure a r := by
  rw [integral_gamma_eq ha hr, integral_gamma_eq ha hr]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [hfg x hx]

/- The exact inverse-power density tilt used, with all gamma laws concrete. -/
theorem gamma_inverse_tilt {a m : ℝ} (k : ℕ) (hak : (k : ℝ) < a)
    (f : ℝ → ℝ) :
    (∫ x, (m/x)^k * f x ∂gammaMeasure a 1) =
      (m^k * Gamma (a-k) / Gamma a) * (∫ x, f x ∂gammaMeasure (a-k) 1) := by
  have ha : 0 < a := lt_of_le_of_lt (Nat.cast_nonneg k) hak
  have ha' : 0 < a-k := sub_pos.mpr hak
  rw [integral_gamma_eq ha zero_lt_one, integral_gamma_eq ha' zero_lt_one,
    ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hp : x^(a-1) = x^((a-k)-1) * x^k := by
    rw [← rpow_natCast x k, ← rpow_add hx]
    congr 1
    ring
  rw [hp]
  simp only [one_rpow, one_mul, div_pow]
  field_simp [(Gamma_pos_of_pos ha').ne', (Gamma_pos_of_pos ha).ne', hx0]

/- The gamma-ratio is the exact falling factorial, not an asymptotic. -/
theorem gamma_ratio_descFactorial {n k : ℕ} (hk : k ≤ n) :
    Gamma ((n : ℝ)+1-k) / Gamma ((n : ℝ)+1) = (n.descFactorial k : ℝ)⁻¹ := by
  have he : (n : ℝ)+1-k = (n-k : ℕ)+1 := by rw [Nat.cast_sub hk]; ring
  rw [he, Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
  have hh : ((n-k).factorial : ℝ) * (n.descFactorial k : ℝ) = n.factorial := by
    exact_mod_cast Nat.factorial_mul_descFactorial hk
  have hnp : (n.factorial : ℝ) ≠ 0 := by positivity
  have hdp : (n.descFactorial k : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_pos.mpr hk).ne'
  field_simp
  exact hh

/- The first equality of manuscript (11). -/
theorem gamma_light_line_identity {m h u v : ℕ} (hm : 0 < m) (huv : h+u+v ≤ m) :
    (∫ x, ((m : ℝ)/x)^v * |(m : ℝ)/x-1|^u
      ∂gammaMeasure ((m-h : ℕ)+1) 1) =
      ((m : ℝ)^(u+v) / ((m-h).descFactorial (u+v) : ℝ)) *
      (∫ x, |1-x/(m : ℝ)|^u ∂gammaMeasure ((m-h : ℕ)+1-(u+v : ℕ)) 1) := by
  have hh : h ≤ m := by omega
  have hk : u+v ≤ m-h := by omega
  have ha : (0 : ℝ) < (m-h : ℕ)+1 := by positivity
  have hak : ((u+v : ℕ) : ℝ) < (m-h : ℕ)+1 := by exact_mod_cast (by omega : u+v < m-h+1)
  have he := integral_gamma_congr ha zero_lt_one
    (f := fun x => ((m : ℝ)/x)^v * |(m : ℝ)/x-1|^u)
    (g := fun x => ((m : ℝ)/x)^(u+v) * |1-x/(m : ℝ)|^u) (by
      intro x hx
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      have hx0 : x ≠ 0 := hx.ne'
      have hz : (m : ℝ)/x-1 = ((m : ℝ)/x)*(1-x/(m : ℝ)) := by
        field_simp
      rw [hz, abs_mul, abs_of_pos (div_pos (by exact_mod_cast hm) hx), mul_pow, pow_add]
      ring)
  rw [he, gamma_inverse_tilt (u+v) hak]
  rw [mul_div_assoc, gamma_ratio_descFactorial hk, ← div_eq_mul_inv]

/- Scale and bias estimate for the tilted gamma law. -/
theorem gamma_normalized_moment_le {a m η : ℝ} (ha : 0 < a) (hm : 0 < m)
    (hη : 0 ≤ η) (hη1 : η ≤ 1) {u : ℕ} (hu : 1 ≤ u)
    (hua : 4*(u : ℝ) ≤ a) (ham : a ≤ m) (huη : (u : ℝ) ≤ m*η)
    (hbias : |1-a/m| ≤ η) :
    (∫ x, |1-x/m|^u ∂gammaMeasure a 1) ≤
      (8 * exp 2 * Real.sqrt η)^u := by
  let : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasure_gammaMeasure ha zero_lt_one
  have hu0 : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hηsqrt : η ≤ Real.sqrt η := by
    have hs := Real.sq_sqrt hη
    nlinarith [Real.sqrt_nonneg η]
  have hcenter : Integrable (fun x : ℝ => |x-a|^u) (gammaMeasure a 1) :=
    abs_pow_integrable (by fun_prop) u (t := 1/4) (by norm_num)
      (gamma_centered_mgf_integrable ha (by norm_num))
      (gamma_centered_mgf_integrable ha (by norm_num))
  have hratio : Real.sqrt (a*u)/m ≤ Real.sqrt η := by
    apply (div_le_iff₀ hm).mpr
    have hs := Real.sq_sqrt (show 0 ≤ a*(u : ℝ) by positivity)
    have hsη := Real.sq_sqrt hη
    have hp : a*(u : ℝ) ≤ m^2*η := by
      nlinarith [mul_le_mul_of_nonneg_right ham hu0,
        mul_le_mul_of_nonneg_left huη hm.le]
    have hsq : (Real.sqrt η*m)^2 = m^2*η := by nlinarith [hsη]
    nlinarith [Real.sqrt_nonneg (a*u), mul_nonneg (Real.sqrt_nonneg η) hm.le]
  let B := 2 * exp 2 * Real.sqrt η
  have he1 : (1 : ℝ) ≤ exp 2 := one_le_exp_iff.mpr (by norm_num)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsB : Real.sqrt η ≤ B := by dsimp [B]; nlinarith [Real.sqrt_nonneg η]
  have hcB : (2*exp 2*Real.sqrt (a*u))/m ≤ B := by
    calc
      _ = (2*exp 2)*(Real.sqrt (a*u)/m) := by ring
      _ ≤ B := mul_le_mul_of_nonneg_left hratio (by positivity)
  have hmoment : (m^u)⁻¹ * (∫ x, |x-a|^u ∂gammaMeasure a 1) ≤ B^u := by
    calc
      _ ≤ (m^u)⁻¹ * (2*exp 2*Real.sqrt (a*u))^u :=
        mul_le_mul_of_nonneg_left (gamma_abs_centered_moment_le ha hu hua) (by positivity)
      _ = ((2*exp 2*Real.sqrt (a*u))/m)^u := by rw [div_pow]; ring
      _ ≤ B^u := pow_le_pow_left₀ (by positivity) hcB u
  have hgint : Integrable (fun x : ℝ => (2 : ℝ)^u *
      ((Real.sqrt η)^u + (m^u)⁻¹ * |x-a|^u)) (gammaMeasure a 1) :=
    ((integrable_const _).add (hcenter.const_mul _)).const_mul _
  have hpt (x : ℝ) : |1-x/m|^u ≤ (2 : ℝ)^u *
      ((Real.sqrt η)^u + (m^u)⁻¹ * |x-a|^u) := by
    have hde : 1-x/m = (1-a/m) + (-(x-a))/m := by ring
    have hh : |1-x/m| ≤ Real.sqrt η + |x-a|/m := by
      rw [hde]
      apply (abs_add_le _ _).trans
      rw [abs_div, abs_neg, abs_of_pos hm]
      exact add_le_add (hbias.trans hηsqrt) le_rfl
    calc
      _ ≤ (Real.sqrt η + |x-a|/m)^u := pow_le_pow_left₀ (abs_nonneg _) hh u
      _ ≤ 2^(u-1) * ((Real.sqrt η)^u + (|x-a|/m)^u) :=
        add_pow_le (Real.sqrt_nonneg _) (by positivity) u
      _ ≤ 2^u * ((Real.sqrt η)^u + (|x-a|/m)^u) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      _ = _ := by rw [div_pow]; ring
  calc
    _ ≤ ∫ x, (2 : ℝ)^u * ((Real.sqrt η)^u + (m^u)⁻¹ * |x-a|^u)
        ∂gammaMeasure a 1 := integral_mono_of_nonneg
      (ae_of_all _ (fun _ => by positivity)) hgint (ae_of_all _ hpt)
    _ = 2^u * ((Real.sqrt η)^u + (m^u)⁻¹ *
        (∫ x, |x-a|^u ∂gammaMeasure a 1)) := by
      rw [integral_const_mul, integral_add (integrable_const _) (hcenter.const_mul _),
        integral_const, integral_const_mul]
      simp
    _ ≤ 2^u * (B^u + B^u) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsB _) hmoment
    _ ≤ (8*exp 2*Real.sqrt η)^u := by
      have htwo : (2 : ℝ) ≤ 2^u := by
        simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hu)
      calc
        _ = 2^u * 2 * B^u := by ring
        _ ≤ 2^u * 2^u * B^u := by gcongr
        _ = (8*exp 2*Real.sqrt η)^u := by
          rw [← mul_pow, ← mul_pow]
          congr 1
          dsimp [B]
          ring

/- Uniform bound for the inverse-gamma prefactor, a light line cannot have
more than half of its sites assigned. -/
theorem light_prefactor_le {m h k : ℕ} (hm : 0 < m) (hk : 2*(h+k) ≤ m) :
    (m : ℝ)^k / ((m-h).descFactorial k : ℝ) ≤ 2^k := by
  have hkm : k ≤ m-h := by omega
  have hpos : (0 : ℝ) < (m-h).descFactorial k := by
    exact_mod_cast Nat.descFactorial_pos.mpr hkm
  apply (div_le_iff₀ hpos).mpr
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  calc
    (m : ℝ)^k = ∏ j ∈ Finset.range k, (m : ℝ) := by simp
    _ ≤ ∏ j ∈ Finset.range k, (2 : ℝ)*(m-h-j : ℕ) := by
      apply Finset.prod_le_prod
      · intro _ _; positivity
      · intro j hj
        have hjk := Finset.mem_range.mp hj
        have hjm : j ≤ m-h := by omega
        rw [Nat.cast_sub hjm, Nat.cast_sub (show h ≤ m by omega)]
        have hn : (2 : ℝ)*(h+k) ≤ m := by exact_mod_cast hk
        have hjr : (j : ℝ) ≤ k := by exact_mod_cast (by omega : j ≤ k)
        nlinarith
    _ = 2^k * ∏ j ∈ Finset.range k, ((m-h-j : ℕ) : ℝ) := by
      rw [Finset.prod_mul_distrib]
      simp

/- The light-line estimate (11), with an explicit absolute constant. -/
theorem gamma_light_line_bound {m h u v : ℕ} (hm : 0 < m) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1/8)
    (hlight : ((h+u+v : ℕ) : ℝ) ≤ (m : ℝ)*η) :
    (∫ x, ((m : ℝ)/x)^v * |(m : ℝ)/x-1|^u
      ∂gammaMeasure ((m-h : ℕ)+1) 1) ≤
      (16 * exp 2)^(u+v) * (Real.sqrt η)^u := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := hm0.ne'
  have htot : ((h+u+v : ℕ) : ℝ) ≤ (m : ℝ)/8 := by
    nlinarith [mul_le_mul_of_nonneg_left hηsmall hm0.le]
  have ht : h+u+v ≤ m := by
    exact_mod_cast (show ((h+u+v : ℕ) : ℝ) ≤ (m : ℝ) by linarith)
  have ht2 : 2*(h+(u+v)) ≤ m := by
    have hh : (2 : ℝ)*(h+u+v) ≤ m := by push_cast at htot; linarith
    simpa only [Nat.add_assoc] using (show 2*(h+u+v) ≤ m by exact_mod_cast hh)
  have hh : h ≤ m := by omega
  let a : ℝ := (m-h : ℕ)+1-(u+v : ℕ)
  have hae : a = (m : ℝ)-(h+u+v : ℕ)+1 := by
    dsimp [a]
    rw [Nat.cast_sub hh]
    push_cast
    ring
  have ha : 0 < a := by rw [hae]; linarith
  have hnorm : (∫ x, |1-x/(m : ℝ)|^u ∂gammaMeasure a 1) ≤
      (8 * exp 2 * Real.sqrt η)^u := by
    by_cases hu : u = 0
    · subst u
      let : IsProbabilityMeasure (gammaMeasure a 1) := isProbabilityMeasure_gammaMeasure ha zero_lt_one
      simp
    · have hu1 : 1 ≤ u := by omega
      have huS : (u : ℝ) ≤ (h+u+v : ℕ) := by exact_mod_cast (by omega : u ≤ h+u+v)
      have hS1 : (1 : ℝ) ≤ (h+u+v : ℕ) := by exact_mod_cast (by omega : 1 ≤ h+u+v)
      have hua : 4*(u : ℝ) ≤ a := by rw [hae]; linarith
      have ham : a ≤ m := by rw [hae]; linarith
      apply gamma_normalized_moment_le ha hm0 hη (by linarith) hu1 hua ham (huS.trans hlight)
      have he : 1-a/(m : ℝ) = ((m : ℝ)-a)/m := by field_simp
      rw [he, abs_of_nonneg (div_nonneg (sub_nonneg.mpr ham) hm0.le)]
      apply (div_le_iff₀ hm0).mpr
      rw [hae]
      linarith
  rw [gamma_light_line_identity hm ht]
  have hpre := light_prefactor_le hm ht2
  change _ * (∫ x, |1-x/(m : ℝ)|^u ∂gammaMeasure a 1) ≤ _
  calc
    _ ≤ (2 : ℝ)^(u+v) * (8 * exp 2 * Real.sqrt η)^u := by
      apply mul_le_mul hpre hnorm
      · exact integral_nonneg (fun _ => by positivity)
      · positivity
    _ = 2^(u+v) * (8*exp 2)^u * (Real.sqrt η)^u := by rw [mul_pow]; ring
    _ ≤ 2^(u+v) * (8*exp 2)^(u+v) * (Real.sqrt η)^u := by
      have hC : (1 : ℝ) ≤ 8*exp 2 := by nlinarith [one_le_exp_iff.mpr (show (0 : ℝ) ≤ 2 by norm_num)]
      have hp := pow_le_pow_right₀ hC (Nat.le_add_right u v)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ = (16 * exp 2)^(u+v) * (Real.sqrt η)^u := by
      rw [← mul_pow]
      congr 2
      ring

/- Exactly the power convention printed in manuscript (11). -/

end CoordinateSweeps

namespace CoordinateSweeps.MomentExpansion
open MeasureTheory ProbabilityTheory Real

/- Source light-line factorial moment, with its exact finite-population shift. -/
theorem fallingMoment_eq_integral {m h n : ℕ} (hn : n ≤ m-h) :
    fallingMoment m h n =
      ∫ x, ((m : ℝ)/x)^n ∂gammaMeasure ((m-h : ℕ)+1) 1 := by
  have hak : (n : ℝ) < (m-h : ℕ)+1 := by exact_mod_cast (by omega : n < m-h+1)
  have ha : (0 : ℝ) < (m-h : ℕ)+1-n := by linarith
  let : IsProbabilityMeasure (gammaMeasure ((m-h : ℕ)+1-n) 1) :=
    isProbabilityMeasure_gammaMeasure ha zero_lt_one
  have he := gamma_inverse_tilt (m := (m : ℝ)) n hak (fun _ => (1 : ℝ))
  simp only [mul_one, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul,
    mul_div_assoc, gamma_ratio_descFactorial hn] at he
  simpa only [fallingMoment, div_eq_mul_inv] using he.symm

theorem fallingMoment_integrable {m h n : ℕ} (hm : 0 < m) (hn : n ≤ m-h) :
    Integrable (fun x => ((m : ℝ)/x)^n) (gammaMeasure ((m-h : ℕ)+1) 1) := by
  apply Integrable.of_integral_ne_zero
  rw [← fallingMoment_eq_integral hn]
  apply ne_of_gt
  unfold fallingMoment
  exact div_pos (pow_pos (by exact_mod_cast hm) _)
    (by exact_mod_cast Nat.descFactorial_pos.mpr hn)

/- Centered finite differences collect all occurrences of the SAME line. -/
theorem fallingCenteredMoment_eq_integral {L : Type*} (m h : L → ℕ) (l : L)
    (hm : 0 < m l) (v u : ℕ) (huv : v+u ≤ m l-h l) :
    lineCenteredMoment (fun l => fallingMoment (m l) (h l)) l v u =
      ∫ x, ((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u
        ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
  have he (a : ℕ) (ha : a ∈ Finset.range (u+1)) :
      v+a ≤ m l-h l := by simp only [Finset.mem_range] at ha; omega
  have hi (a : ℕ) (ha : a ∈ Finset.range (u+1)) :
      Integrable (fun x => (-1 : ℝ)^(a+u) * (u.choose a : ℝ) * ((m l : ℝ)/x)^(v+a))
        (gammaMeasure ((m l-h l : ℕ)+1) 1) :=
    (fallingMoment_integrable hm (he a ha)).const_mul _
  unfold lineCenteredMoment
  have hs : (∑ a ∈ Finset.range (u+1), (-1 : ℝ)^(a+u) * (u.choose a : ℝ) *
      fallingMoment (m l) (h l) (v+a)) =
      ∫ x, ∑ a ∈ Finset.range (u+1), (-1 : ℝ)^(a+u) * (u.choose a : ℝ) *
        ((m l : ℝ)/x)^(v+a) ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
    rw [integral_finsetSum _ hi]
    apply Finset.sum_congr rfl
    intro a ha
    rw [integral_const_mul, ← fallingMoment_eq_integral (he a ha)]
  rw [hs]
  congr 1
  funext x
  rw [sub_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [pow_add]
  ring

/- Source (11) now applies directly to the exact finite-difference moment.
The gamma centered bound already existed; this bridge to Q's required moments is new. -/
theorem fallingCenteredMoment_abs_le {L : Type*} (m h : L → ℕ) (l : L)
    (hm : 0 < m l) (v u : ℕ) {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/8)
    (hlight : ((h l+u+v : ℕ) : ℝ) ≤ (m l : ℝ)*η) :
    |lineCenteredMoment (fun l => fallingMoment (m l) (h l)) l v u| ≤
      (16 * exp 2)^v * ((16 * exp 2)*Real.sqrt η)^u := by
  have huvn : h l+u+v ≤ m l := by
    have hm0 : (0 : ℝ) ≤ m l := Nat.cast_nonneg _
    have ht : (m l : ℝ)*η ≤ m l := mul_le_of_le_one_right hm0 (by linarith)
    exact_mod_cast hlight.trans ht
  rw [fallingCenteredMoment_eq_integral m h l hm v u (by omega)]
  have ha : (0 : ℝ) < (m l-h l : ℕ)+1 := by positivity
  have he : (∫ x, |((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u|
      ∂gammaMeasure ((m l-h l : ℕ)+1) 1) =
      ∫ x, ((m l : ℝ)/x)^v * |(m l : ℝ)/x-1|^u
        ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
    apply integral_gamma_congr ha zero_lt_one
    intro x hx
    rw [abs_mul, abs_pow, abs_pow, abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) hx.le)]
  calc
    _ ≤ ∫ x, |((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u|
        ∂gammaMeasure ((m l-h l : ℕ)+1) 1 := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun x => ((m l : ℝ)/x)^v * ((m l : ℝ)/x-1)^u)
    _ = _ := he
    _ ≤ (16 * exp 2)^(u+v) * (Real.sqrt η)^u := gamma_light_line_bound hm hη hηsmall hlight
    _ = _ := by rw [pow_add, mul_pow]; ring

/- Actual inverse-gamma specialization of the shared-line expansion. -/

end CoordinateSweeps.MomentExpansion

end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_TrajectoryMoment
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

theorem auxCount_sum (x y : Fin k → G.Slot) (A : Finset (Fin k)) (j : Fin G.b) :
    ∑ L : G.Line j, auxCount x y A j L = A.card := by
  unfold auxCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

theorem selected_sum {R : Type*} [AddCommMonoid R]
    (A : Finset (Fin k)) (f : Fin k → R) :
    (∑ i : Fin A.card, f (selected A i)) = ∑ a ∈ A, f a := by
  change (∑ i : Fin A.card, (fun a : A => f a.val)
    ((Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm i)) = _
  calc
    _ = ∑ a : A, f a.val := by
      exact Equiv.sum_comp (Fintype.equivFinOfCardEq (Fintype.card_coe A)).symm (fun a : A => f a.val)
    _ = _ := Finset.sum_coe_sort A f

theorem augment_selected_extraCount (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) (ω : G.Choices) (hω : H.Compatible ω)
    (he : G.endpointEvent x y A ω) (j : Fin G.b) (L : G.Line j) :
    (H.augment (fun i => x (selected A i)) (fun i => y (selected A i))
      (H.validInput_selected x hx A) ω hω ((endpointEvent_iff_selected x y A ω).mp he)).extraCount j L =
      auxCount x y A j L := by
  unfold extraCount auxCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter, OnLine, augment_new]
  change (∑ i : Fin A.card, if G.pathLine (x (selected A i)) (y (selected A i)) j = L then 1 else 0) = _
  exact selected_sum (R := ℕ) A (fun i => if G.pathLine (x i) (y i) j = L then 1 else 0)

theorem size_pow_eq_aux_product (x y : Fin k → G.Slot) (A : Finset (Fin k)) :
    (G.size : ℝ)^A.card =
      ∏ j, ∏ L : G.Line j, ((2^G.bits j : ℕ) : ℝ)^auxCount x y A j L := by
  simp only [Finset.prod_pow_eq_pow_sum, auxCount_sum]
  rw [Finset.prod_pow]
  congr 1
  simp [Grid.size]

/- Very same endpoint feasibility event as the conditioned finite sample space. -/

theorem descFactorial_add_split (n a b : ℕ) :
    n.descFactorial (a+b) = n.descFactorial a * (n-a).descFactorial b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.add_succ, Nat.descFactorial_succ, ih, Nat.descFactorial_succ,
      Nat.sub_sub]
    ring

/- Uniform scaled entries have exactly the falling-factorial moments that enter
the shared-line gamma expansion, zero for impossible simultaneous paths. -/
theorem scaled_extraProbability_uniform (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) :
    (G.size : ℝ)^A.card * H.extraProbability x y A (fun _ => FiniteLaw.uniform _) =
      if H.EndpointPossible x y A then
        ∏ j, ∏ L : G.Line j, fallingMoment (2^G.bits j) (H.lineCount j L) (auxCount x y A j L)
      else 0 := by
  classical
  rw [H.extraProbability_eq_conditionalEndpoint]
  by_cases he : H.EndpointPossible x y A
  · rw [ite_eq_left he]
    obtain ⟨ω,hω,he⟩ := he
    let J := H.augment (fun i => x (selected A i)) (fun i => y (selected A i))
      (H.validInput_selected x hx A) ω hω ((endpointEvent_iff_selected x y A ω).mp he)
    have hext : J.Extends H := H.augment_extends _ _ _ _ _ _
    have hcount (j : Fin G.b) (L : G.Line j) :
        J.lineCount j L = H.lineCount j L + auxCount x y A j L := by
      rw [J.lineCount_add H hext]
      exact congrArg (H.lineCount j L + ·) (H.augment_selected_extraCount x y hx A ω hω he j L)
    have hprob : H.conditionalEndpointProbability x y A (fun _ => FiniteLaw.uniform _) =
        J.probability 0 / H.probability 0 := by
      have hu : (fun j : Fin G.b => lineLaw (G.bits j) 0 (le_refl 0) zero_le_one) =
          (fun _ => FiniteLaw.uniform _) := by
        funext j
        ext σ
        simp [lineLaw, FiniteLaw.mix, FiniteLaw.uniform]
      rw [← hu]
      unfold conditionalEndpointProbability
      rw [H.lineMass_hole_normalizer, ← J.lineMass_hole_normalizer (le_refl 0) zero_le_one]
      congr 1
      apply Finset.sum_congr rfl
      intro ν _
      have hj : J.Compatible ν ↔ H.Compatible ν ∧ G.endpointEvent x y A ν := by
        dsimp [J]
        rw [H.augment_compatible_iff, endpointEvent_iff_selected]
      simp only [hj]
    rw [hprob, J.probability_zero, H.probability_zero, size_pow_eq_aux_product x y A,
      ← Finset.prod_div_distrib]
    simp only [← Finset.prod_div_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro L _
    rw [hcount, descFactorial_add_split]
    have hfa : ((2^G.bits j).descFactorial (H.lineCount j L) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr (H.lineCount_le j L)).ne'
    have hsub : auxCount x y A j L ≤ 2^G.bits j-H.lineCount j L := by
      have hj := J.lineCount_le j L
      rw [hcount] at hj
      omega
    have hfb : ((2^G.bits j-H.lineCount j L).descFactorial (auxCount x y A j L) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.descFactorial_pos.mpr hsub).ne'
    unfold fallingMoment
    push_cast
    field_simp
  · rw [ite_eq_right he]
    have hn : ∀ ω, ¬ (H.Compatible ω ∧ G.endpointEvent x y A ω) := by
      simpa only [EndpointPossible, not_exists] using he
    simp [conditionalEndpointProbability, hn]

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

/- Geometric validity at EVERY boundary, not only at endpoints. -/
theorem feasible_of_disjoint_paths (H : G.Holes h) : H.Feasible := by
  by_contra hn
  have hz : H.probability 0 = 0 := by
    unfold probability
    exact Finset.sum_eq_zero (fun ω _ => (hn ⟨ω.val,ω.property⟩).elim)
  have hp := H.probability_zero_pos
  rw [hz] at hp
  exact lt_irrefl 0 hp

theorem adjoin_compatible_iff (H : G.Holes h) (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (hv : H.JointDisjoint x y A) (ω : G.Choices) :
    (H.adjoin x y A hv).Compatible ω ↔ H.Compatible ω ∧ G.endpointEvent x y A ω := by
  rw [endpointEvent_iff_selected]
  constructor
  · intro hJ
    constructor
    · intro a s
      simpa only [adjoin_old] using hJ (Fin.castAdd A.card a) s
    · intro a
      simpa only [adjoin_new, Grid.pathBetween_zero, Grid.pathBetween_last,
        Grid.sweep, Fin.val_last] using hJ (Fin.natAdd h a) (Fin.last G.b)
  · rintro ⟨hω,he⟩
    intro i s
    cases i using Fin.addCases with
    | left a => simpa only [adjoin_old] using hω a s
    | right a =>
      simp only [adjoin_new, Grid.pathBetween_zero]
      rw [G.boundary_eq_pathBetween, he a]

/- Exact event feasibility equals disjointness of the unique full trajectories. -/
theorem endpointPossible_iff_jointDisjoint (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) :
    H.EndpointPossible x y A ↔ H.JointDisjoint x y A := by
  constructor
  · rintro ⟨ω,hω,he⟩
    have hb (i : Fin k) (hi : i ∈ A) (s : Fin (G.b+1)) :
        G.boundary ω s (x i) = G.pathBetween (x i) (y i) s := by
      rw [G.boundary_eq_pathBetween, he i hi]
    constructor
    · intro i hi a s hf
      exact hx.2 i a ((G.boundary ω s).injective ((hb i hi s).trans (hf.trans (hω a s).symm)))
    · intro i hi j hj hij s hf
      exact hij (hx.1 ((G.boundary ω s).injective ((hb i hi s).trans (hf.trans (hb j hj s).symm))))
  · intro hv
    obtain ⟨ω,hω⟩ := (H.adjoin x y A hv).feasible_of_disjoint_paths
    exact ⟨ω,(H.adjoin_compatible_iff x y A hv ω).mp hω⟩

/- Precisely the vertex-isolation condition in the source's definition of good. -/

theorem jointDisjoint_mono (H : G.Holes h) (x y : Fin k → G.Slot)
    {A B : Finset (Fin k)} (hAB : A ⊆ B) (hB : H.JointDisjoint x y B) :
    H.JointDisjoint x y A :=
  ⟨fun i hi => hB.1 i (hAB hi), fun i hi j hj => hB.2 i (hAB hi) j (hAB hj)⟩

theorem jointDisjoint_union_iff (H : G.Holes h) (x y : Fin k → G.Slot)
    (A S : Finset (Fin k)) (hS : ∀ i ∈ S, H.VertexIsolated x y i) :
    H.JointDisjoint x y (A∪S) ↔ H.JointDisjoint x y A := by
  constructor
  · exact H.jointDisjoint_mono x y Finset.subset_union_left
  · intro hA
    constructor
    · intro i hi a s
      rcases Finset.mem_union.mp hi with hi | hi
      · exact hA.1 i hi a s
      · exact (hS i hi).1 a s
    · intro i hi j hj hij s
      rcases Finset.mem_union.mp hi with hi | hi
      · rcases Finset.mem_union.mp hj with hj | hj
        · exact hA.2 i hi j hj hij s
        · exact Ne.symm ((hS j hj).2 i hij.symm s)
      · exact (hS i hi).2 j hij s

/- Adding any subset of good paths CANNOT change validity, as needed before
alternation is taken inside the shared-line expectation. -/
theorem endpointPossible_union_iff (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A S : Finset (Fin k))
    (hS : ∀ i ∈ S, H.VertexIsolated x y i) :
    H.EndpointPossible x y (A∪S) ↔ H.EndpointPossible x y A := by
  rw [H.endpointPossible_iff_jointDisjoint x y hx, H.endpointPossible_iff_jointDisjoint x y hx]
  exact H.jointDisjoint_union_iff x y A S hS

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
/- A line is named by both its stage and its remaining coordinates. -/

namespace Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

theorem incidenceCount_stagePath (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (j : Fin G.b) (L : G.Line j) :
    incidenceCount A (G.stagePath x y) ⟨j,L⟩ = auxCount x y A j L := by
  unfold incidenceCount auxCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_eq_single j]
  · simp [stagePath]
  · intro a ha haj
    have hn : G.stagePath x y i a ≠ ⟨j,L⟩ := fun he => haj (congrArg Sigma.fst he)
    simp [hn]
  · simp

theorem incidenceCount_stagePath_any (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (l : G.StageLine) :
    incidenceCount A (G.stagePath x y) l = auxCount x y A l.1 l.2 := by
  cases l with
  | mk j L => exact incidenceCount_stagePath x y A j L

theorem incidenceCount_total (x y : Fin k → G.Slot) (A : Finset (Fin k)) :
    ∑ l : G.StageLine, incidenceCount A (G.stagePath x y) l = G.b*A.card := by
  rw [Fintype.sum_sigma]
  simp only [incidenceCount_stagePath, auxCount_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

theorem incidenceCount_good_nonlight (H : G.Holes h) (x y : Fin k → G.Slot) (η : ℝ)
    (l : G.StageLine) (hl : ¬ H.Light x y η l) {A : Finset (Fin k)}
    (hA : A ⊆ H.goodSet x y η) : incidenceCount A (G.stagePath x y) l = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  apply Finset.sum_eq_zero
  intro j _
  have hn : G.stagePath x y i j ≠ l := by
    intro he
    exact hl (he ▸ ((H.mem_goodSet x y η i).mp (hA hi)).2 j)
  simp [hn]

theorem incidenceCount_mono (x y : Fin k → G.Slot) {A B : Finset (Fin k)}
    (hAB : A ⊆ B) (l : G.StageLine) :
    incidenceCount A (G.stagePath x y) l ≤ incidenceCount B (G.stagePath x y) l :=
  Finset.sum_le_sum_of_subset_of_nonneg hAB (fun _ _ _ => Nat.zero_le _)

theorem incidenceCount_union (x y : Fin k → G.Slot) {A B : Finset (Fin k)}
    (hAB : Disjoint A B) (l : G.StageLine) :
    incidenceCount (A∪B) (G.stagePath x y) l =
      incidenceCount A (G.stagePath x y) l + incidenceCount B (G.stagePath x y) l :=
  Finset.sum_union hAB

/- The actual shared-line moment bound: inactive (non-light) line variables
are set to 1, not made independent per particle. -/
theorem goodExpansion_lightMoment_le (H : G.Holes h) (x y : Fin k → G.Slot)
    {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/8) (J : Finset (Fin k))
    (hJ : Disjoint J (H.goodSet x y η)) :
    |shiftedMoment (H.lightMoment x y η) (incidenceCount J (G.stagePath x y))
      (goodExpansion (H.goodSet x y η) (G.stagePath x y))| ≤
      (16 * Real.exp 2)^(G.b*J.card) * (1+16 * Real.exp 2)^(G.b*(H.goodSet x y η).card) *
        η^(((H.goodSet x y η).card : ℝ)/2) := by
  have hC : (1 : ℝ) ≤ 16*Real.exp 2 := by
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have he := goodExpansion_moment_le (H.lightMoment x y η)
    (H.lightMoment_zero x y η) (incidenceCount J (G.stagePath x y))
    (H.goodSet x y η) (G.stagePath x y) (16*Real.exp 2) (Real.sqrt η)
    (by positivity) (Real.sqrt_nonneg η) (by
      apply (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 1)).mpr
      linarith) (by
      intro l u hu
      by_cases hl : H.Light x y η l
      · have hline : ∀ n, H.lightMoment x y η l n =
            fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) n := by
          intro n; simp [lightMoment, hl]
        simp only [lineCenteredMoment, hline]
        apply fallingCenteredMoment_abs_le (fun l : G.StageLine => 2^G.bits l.1)
          (fun l => H.lineCount l.1 l.2) l (by positivity) _ u hη hηsmall
        apply le_trans _ hl
        have htotal := incidenceCount_mono x y (Finset.subset_univ
          (J ∪ H.goodSet x y η)) l
        rw [incidenceCount_union x y hJ l] at htotal
        simp only [incidenceCount_stagePath_any] at htotal
        change u ≤ incidenceCount (H.goodSet x y η) (G.stagePath x y) l at hu
        rw [incidenceCount_stagePath_any] at hu
        exact_mod_cast (show H.lineCount l.1 l.2 + u + incidenceCount J (G.stagePath x y) l ≤
            H.lineCount l.1 l.2 + auxCount x y Finset.univ l.1 l.2 by
          rw [incidenceCount_stagePath_any]
          omega)
      · have hzero := H.incidenceCount_good_nonlight x y η l hl (Finset.Subset.refl _)
        have hu0 : u = 0 := by change u ≤ incidenceCount _ _ l at hu; omega
        subst u
        simpa [lineCenteredMoment, lightMoment, hl] using
          (one_le_pow₀ hC : (1 : ℝ) ≤ (16*Real.exp 2)^incidenceCount J (G.stagePath x y) l))
  have hs : (Real.sqrt η)^(H.goodSet x y η).card = η^(((H.goodSet x y η).card : ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hη]
    congr 1; ring
  simpa only [incidenceCount_total, Fintype.card_fin, hs] using he

end Holes
end CoordinateSweeps.Grid

namespace CoordinateSweeps.MomentExpansion

theorem fallingMoment_one_le {m h n : ℕ} (hn : h+n ≤ m) : 1 ≤ fallingMoment m h n := by
  have hd : (0 : ℝ) < (m-h).descFactorial n := by
    exact_mod_cast Nat.descFactorial_pos.mpr (by omega : n ≤ m-h)
  unfold fallingMoment
  apply (le_div_iff₀ hd).mpr
  rw [one_mul]
  exact_mod_cast (Nat.descFactorial_le_pow (m-h) n).trans
    (Nat.pow_le_pow_left (Nat.sub_le m h) n)

end CoordinateSweeps.MomentExpansion

namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

theorem endpointPossible_lineCount_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (A : Finset (Fin k)) (hA : H.EndpointPossible x y A)
    (l : G.StageLine) : H.lineCount l.1 l.2 + incidenceCount A (G.stagePath x y) l ≤ 2^G.bits l.1 := by
  obtain ⟨ω,hω,he⟩ := hA
  let J := H.augment (fun i => x (selected A i)) (fun i => y (selected A i))
    (H.validInput_selected x hx A) ω hω ((endpointEvent_iff_selected x y A ω).mp he)
  have hext : J.Extends H := H.augment_extends _ _ _ _ _ _
  have hc := J.lineCount_le l.1 l.2
  rw [J.lineCount_add H hext,
    H.augment_selected_extraCount x y hx A ω hω he l.1 l.2] at hc
  simpa only [incidenceCount_stagePath_any] using hc

/- Product outside the light-line expectation; zero validity is handled
separately, never by interpreting a divergent inverse-gamma moment. -/

theorem nonlightFactor_nonneg (H : G.Holes h) (x y : Fin k → G.Slot)
    (η : ℝ) (J : Finset (Fin k)) : 0 ≤ H.nonlightFactor x y η J := by
  apply Finset.prod_nonneg
  intro l _
  split_ifs
  · norm_num
  · unfold fallingMoment; positivity

theorem nonlightFactor_le (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (η : ℝ) (J : Finset (Fin k)) (hJ : H.EndpointPossible x y J) :
    H.nonlightFactor x y η J ≤ Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b) := by
  have hu (j : Fin G.b) : lineLaw (G.bits j) 0 (le_refl 0) zero_le_one = FiniteLaw.uniform _ := by
    ext σ
    simp [lineLaw, FiniteLaw.mix, FiniteLaw.uniform]
  have he := H.scaled_extraProbability_le x y hx J (le_refl 0) zero_le_one
    (by intro j σ; rw [hu]; have := (FiniteLaw.uniform _).nonneg σ; linarith)
    (by intro j σ; rw [hu]; have := (FiniteLaw.uniform _).nonneg σ; linarith)
  simp_rw [hu] at he
  rw [H.scaled_extraProbability_uniform x y hx J, ite_eq_left hJ] at he
  apply le_trans _ he
  rw [← Fintype.prod_sigma (fun l : G.StageLine =>
    fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) (auxCount x y J l.1 l.2))]
  unfold nonlightFactor
  apply Finset.prod_le_prod
  · intro l _
    split_ifs
    · norm_num
    · unfold fallingMoment; positivity
  · intro l _
    split_ifs
    · apply fallingMoment_one_le
      simpa only [incidenceCount_stagePath_any] using H.endpointPossible_lineCount_le x y hx J hJ l
    · rw [incidenceCount_stagePath_any]

/- Exact factorization for adding any collection of good paths. -/
theorem scaled_extraProbability_good_union (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (η : ℝ) (J S : Finset (Fin k))
    (hJ : Disjoint J (H.goodSet x y η)) (hS : S ⊆ H.goodSet x y η) :
    (G.size : ℝ)^(J∪S).card * H.extraProbability x y (J∪S) (fun _ => FiniteLaw.uniform _) =
      (if H.EndpointPossible x y J then H.nonlightFactor x y η J else 0) *
        ∏ l : G.StageLine, H.lightMoment x y η l
          (incidenceCount J (G.stagePath x y) l+incidenceCount S (G.stagePath x y) l) := by
  rw [H.scaled_extraProbability_uniform x y hx (J∪S)]
  have hv := H.endpointPossible_union_iff x y hx J S (fun i hi =>
    ((H.mem_goodSet x y η i).mp (hS hi)).1)
  rw [hv]
  split_ifs with hp
  · rw [← Fintype.prod_sigma (fun l : G.StageLine =>
        fallingMoment (2^G.bits l.1) (H.lineCount l.1 l.2) (auxCount x y (J∪S) l.1 l.2)),
      nonlightFactor, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro l _
    rw [← incidenceCount_stagePath_any, incidenceCount_union x y (hJ.mono_right hS)]
    unfold lightMoment
    split_ifs with hl
    · simp
    · rw [H.incidenceCount_good_nonlight x y η l hl hS]
      simp
  · simp

end CoordinateSweeps.Grid.Holes
/- Finite subset rearrangements needed for the actual good/non-good path
alternation in source04:eq10. -/
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps
variable {I : Type*} [DecidableEq I]

theorem sum_powerset_union {R : Type*} [AddCommMonoid R]
    (A B : Finset I) (hAB : Disjoint A B) (f : Finset I → R) :
    ∑ S ∈ (A∪B).powerset, f S =
      ∑ J ∈ A.powerset, ∑ S ∈ B.powerset, f (J∪S) := by
  rw [← Finset.sum_product A.powerset B.powerset (fun p => f (p.1 ∪ p.2))]
  symm
  apply Finset.sum_bij (fun p _ => p.1 ∪ p.2)
  · intro p hp
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    exact Finset.mem_powerset.mpr (Finset.union_subset_union
      (Finset.mem_powerset.mp hp1) (Finset.mem_powerset.mp hp2))
  · intro p hp q hq he
    obtain ⟨hp1,hp2⟩ := Finset.mem_product.mp hp
    obtain ⟨hq1,hq2⟩ := Finset.mem_product.mp hq
    have hp1 := Finset.mem_powerset.mp hp1
    have hp2 := Finset.mem_powerset.mp hp2
    have hq1 := Finset.mem_powerset.mp hq1
    have hq2 := Finset.mem_powerset.mp hq2
    apply Prod.ext
    · ext i
      constructor
      · intro hi
        have hu : i ∈ q.1 ∪ q.2 := he ▸ Finset.mem_union_left _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · exact False.elim (Finset.disjoint_left.mp hAB (hp1 hi) (hq2 h))
      · intro hi
        have hu : i ∈ p.1 ∪ p.2 := he.symm ▸ Finset.mem_union_left _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · exact False.elim (Finset.disjoint_left.mp hAB (hq1 hi) (hp2 h))
    · ext i
      constructor
      · intro hi
        have hu : i ∈ q.1 ∪ q.2 := he ▸ Finset.mem_union_right _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact False.elim (Finset.disjoint_left.mp hAB (hq1 h) (hp2 hi))
        · exact h
      · intro hi
        have hu : i ∈ p.1 ∪ p.2 := he.symm ▸ Finset.mem_union_right _ hi
        rcases Finset.mem_union.mp hu with h | h
        · exact False.elim (Finset.disjoint_left.mp hAB (hp1 h) (hq2 hi))
        · exact h
  · intro S hS
    refine ⟨(S∩A,S∩B), Finset.mem_product.mpr ⟨?_,?_⟩, ?_⟩
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
    · exact Finset.mem_powerset.mpr Finset.inter_subset_right
    · simp only [Finset.mem_powerset] at hS
      ext i
      simp only [Finset.mem_union, Finset.mem_inter]
      constructor
      · tauto
      · intro hi
        have hu := Finset.mem_union.mp (hS hi)
        tauto
  · intro p hp
    rfl

theorem sum_powerset_sdiff {R : Type*} [AddCommMonoid R]
    (A : Finset I) (f : Finset I → R) :
    ∑ S ∈ A.powerset, f (A\S) = ∑ S ∈ A.powerset, f S := by
  apply Finset.sum_bij (fun S _ => A\S)
  · intro S hS
    exact Finset.mem_powerset.mpr Finset.sdiff_subset
  · intro S hS T hT he
    have hS := Finset.mem_powerset.mp hS
    have hT := Finset.mem_powerset.mp hT
    apply_fun (fun U => A\U) at he
    simpa only [Finset.sdiff_sdiff_self_left, Finset.inter_eq_right.mpr hS,
      Finset.inter_eq_right.mpr hT] using he
  · intro S hS
    have hS := Finset.mem_powerset.mp hS
    exact ⟨A\S, Finset.mem_powerset.mpr Finset.sdiff_subset, by simp [hS]⟩
  · intro S hS
    rfl

theorem alternating_good_split [Fintype I] (G : Finset I) (f : Finset I → ℝ) :
    (∑ A ∈ (Finset.univ : Finset I).powerset,
      (-1 : ℝ)^(Fintype.card I-A.card)*f A) =
    ∑ J ∈ ((Finset.univ : Finset I)\G).powerset,
      (-1 : ℝ)^(Fintype.card I-J.card-G.card) *
        ∑ A ∈ G.powerset, (-1 : ℝ)^A.card * f (J ∪ (G\A)) := by
  have hg : ((Finset.univ : Finset I)\G) ∪ G = Finset.univ := by simp
  conv_lhs => rw [← hg, sum_powerset_union _ _ disjoint_sdiff_self_left]
  apply Finset.sum_congr rfl
  intro J hJ
  have hJ := Finset.mem_powerset.mp hJ
  have hd : Disjoint J G := Finset.disjoint_of_subset_left hJ disjoint_sdiff_self_left
  rw [← sum_powerset_sdiff G (fun S => (-1 : ℝ)^(Fintype.card I-(J∪S).card)*f (J∪S))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  have hA := Finset.mem_powerset.mp hA
  have hdc : Disjoint J (G\A) := hd.mono_right Finset.sdiff_subset
  have hcard : J.card+G.card ≤ Fintype.card I := by
    rw [← Finset.card_union_of_disjoint hd]
    exact Finset.card_le_univ _
  have hAc := Finset.card_le_card hA
  rw [Finset.card_union_of_disjoint hdc, Finset.card_sdiff_of_subset hA]
  have he : Fintype.card I-(J.card+(G.card-A.card)) =
      (Fintype.card I-J.card-G.card)+A.card := by omega
  rw [he, pow_add]
  ring

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
open MomentExpansion
variable {G : Grid} {h k : ℕ}

theorem alternating_good_extensions (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) (η : ℝ) (J : Finset (Fin k))
    (hJ : Disjoint J (H.goodSet x y η)) :
    (∑ A ∈ (H.goodSet x y η).powerset, (-1 : ℝ)^A.card *
      ((G.size : ℝ)^(J∪(H.goodSet x y η\A)).card *
        H.extraProbability x y (J∪(H.goodSet x y η\A)) (fun _ => FiniteLaw.uniform _))) =
      (if H.EndpointPossible x y J then H.nonlightFactor x y η J else 0) *
        shiftedMoment (H.lightMoment x y η) (incidenceCount J (G.stagePath x y))
          (goodExpansion (H.goodSet x y η) (G.stagePath x y)) := by
  rw [shiftedMoment_goodExpansion_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  rw [H.scaled_extraProbability_good_union x y hx η J _ hJ Finset.sdiff_subset]
  ring

/- Source04:eq10, now proved for literal uniform stage-line laws and actual
conditioned path probabilities. Constants are explicit and absolute; all
non-light factors and validity indicators remain outside the moment. -/
theorem scaled_placementKernel_good_bound (H : G.Holes h) (x y : Fin k → G.Slot)
    (hx : H.ValidInput x) {η : ℝ} (hη : 0 ≤ η) (hηsmall : η ≤ 1/8) :
    |(G.size : ℝ)^k * H.placementKernel x y (fun _ => FiniteLaw.uniform _)| ≤
      (2 : ℝ)^k * Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b) *
        (16*Real.exp 2)^(G.b*k) * (1+16*Real.exp 2)^(G.b*k) *
          η^(((H.goodSet x y η).card : ℝ)/2) := by
  have hs : (G.size : ℝ) ≠ 0 := by unfold Grid.size; positivity
  have hC : (1 : ℝ) ≤ 16*Real.exp 2 := by
    have := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hC' : (1 : ℝ) ≤ 1+16*Real.exp 2 := by linarith
  let GG := H.goodSet x y η
  let E := Real.exp ((G.b : ℝ)*(h+k)+Real.log 4*k*G.b)
  let U := (16*Real.exp 2)^(G.b*k) * (1+16*Real.exp 2)^(G.b*k) * η^((GG.card : ℝ)/2)
  have hU : 0 ≤ U := by dsimp [U]; positivity
  rw [placementKernel, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hs, one_pow, one_mul]
  conv_lhs => simp only [mul_assoc]
  have hsplit := alternating_good_split GG (fun A =>
    (G.size : ℝ)^A.card * H.extraProbability x y A (fun _ => FiniteLaw.uniform _))
  simp only [Fintype.card_fin] at hsplit
  rw [hsplit]
  have hterm (J : Finset (Fin k)) (hJ : J ∈ ((Finset.univ : Finset (Fin k))\GG).powerset) :
      |(-1 : ℝ)^(k-J.card-GG.card) *
        ∑ A ∈ GG.powerset, (-1 : ℝ)^A.card *
          ((G.size : ℝ)^(J∪(GG\A)).card *
            H.extraProbability x y (J∪(GG\A)) (fun _ => FiniteLaw.uniform _))| ≤ E*U := by
    have hsub := Finset.mem_powerset.mp hJ
    have hd : Disjoint J GG := Finset.disjoint_of_subset_left hsub disjoint_sdiff_self_left
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      H.alternating_good_extensions x y hx η J hd, abs_mul]
    have hD : |if H.EndpointPossible x y J then H.nonlightFactor x y η J else 0| ≤ E := by
      split_ifs with hp
      · rw [abs_of_nonneg (H.nonlightFactor_nonneg x y η J)]
        exact H.nonlightFactor_le x y hx η J hp
      · simp only [abs_zero]
        exact (Real.exp_pos _).le
    have hM := H.goodExpansion_lightMoment_le x y hη hηsmall J hd
    have hJk : J.card ≤ k := by simpa using Finset.card_le_univ J
    have hGk : GG.card ≤ k := by simpa using Finset.card_le_univ GG
    have hM' : |shiftedMoment (H.lightMoment x y η) (incidenceCount J (G.stagePath x y))
        (goodExpansion GG (G.stagePath x y))| ≤ U := by
      apply hM.trans
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hη _)
      apply mul_le_mul
      · exact pow_le_pow_right₀ hC (Nat.mul_le_mul_left G.b hJk)
      · exact pow_le_pow_right₀ hC' (Nat.mul_le_mul_left G.b hGk)
      · positivity
      · positivity
    exact mul_le_mul hD hM' (abs_nonneg _) (Real.exp_pos _).le
  calc
    _ ≤ ∑ J ∈ ((Finset.univ : Finset (Fin k))\GG).powerset,
        |(-1 : ℝ)^(k-J.card-GG.card) *
          ∑ A ∈ GG.powerset, (-1 : ℝ)^A.card *
            ((G.size : ℝ)^(J∪(GG\A)).card *
              H.extraProbability x y (J∪(GG\A)) (fun _ => FiniteLaw.uniform _))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ J ∈ ((Finset.univ : Finset (Fin k))\GG).powerset, E*U :=
      Finset.sum_le_sum hterm
    _ = (2 : ℝ)^((Finset.univ : Finset (Fin k))\GG).card*(E*U) := by simp
    _ ≤ (2 : ℝ)^k*(E*U) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.exp_pos _).le hU)
      apply pow_le_pow_right₀ (by norm_num)
      exact le_trans (Finset.card_le_card Finset.sdiff_subset) (by simp)
    _ = _ := by dsimp [E,U,GG]; ring

end CoordinateSweeps.Grid.Holes
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.Placement_Occurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Placement
variable {I U X Y : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]

/- Dependence only on the listed coordinate values of a placement. -/
omit [DecidableEq I] [Fintype X] in
theorem alternatingKernel_mulVec_top (coords : Y → I → U)
    (s : ℝ) (hs : s ≠ 0) (p : Finset I → X → Y → ℝ)
    (hp : ∀ A x, DependsOn coords A (fun y => (p A x y : ℂ)))
    {v : Y → ℂ} (hv : v ∈ topSpace coords) :
    (alternatingKernel s p).mulVec v = Matrix.mulVec (fun x y => (p Finset.univ x y : ℂ)) v := by
  funext x
  simp only [Matrix.mulVec, dotProduct, alternatingKernel, Complex.ofReal_mul,
    Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_sum]
  simp only [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_eq_single (Finset.univ : Finset I)]
  · simp only [Finset.card_univ, Nat.sub_self, pow_zero, one_mul]
    rw [← mul_assoc, ← mul_pow, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hs), one_pow, one_mul]
  · intro A hA hne
    have hzero := hv A hne (fun y => (p A x y : ℂ)) (hp A x)
    simp only [hzero, mul_zero]
  · simp

/- Counting HS norm always dominates the L2 operator norm, rectangular and
empty dimensions included. No entrywise max norm is used. -/
theorem matrix_l2_norm_le_hs (A : Matrix X Y ℂ) :
    ‖A‖ ≤ Real.sqrt (∑ x, ∑ y, ‖A x y‖^2) := by
  let L : EuclideanSpace ℂ Y →L[ℂ] EuclideanSpace ℂ X :=
    LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  change ‖L‖ ≤ _
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) ?_
  intro v
  have hrow (x : X) : ‖(A.mulVec v) x‖^2 ≤
      (∑ y, ‖A x y‖^2)*(∑ y, ‖v y‖^2) := by
    have hnorm : ‖(A.mulVec v) x‖ ≤ ∑ y, ‖A x y‖*‖v y‖ := by
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun y _ => le_of_eq (norm_mul _ _))
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun y => ‖A x y‖) (fun y => ‖v y‖)
    exact ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => by positivity))).mpr hnorm).trans hc
  have hall : (∑ x, ‖(A.mulVec v) x‖^2) ≤
      (∑ x, ∑ y, ‖A x y‖^2)*(∑ y, ‖v y‖^2) := by
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum (fun x _ => hrow x)
  change ‖Matrix.toEuclideanLin A v‖ ≤ _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow, Real.sq_sqrt (by positivity), PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  exact hall

/- The actual full marginal has the alternating HS bound on the entire top
placement space. This is used before choosing an irreducible constituent. -/
end CoordinateSweeps.Placement
namespace CoordinateSweeps
namespace UnitaryIrrep
variable {Γ : Type*} [Group Γ] (ρ : UnitaryIrrep Γ)

theorem adjoint_intertwines {X : Type*} [Fintype X] [DecidableEq X]
    (P : Γ →* Matrix X X ℂ) (hP : ∀ g, (P g).conjTranspose * P g = 1)
    (B : Matrix (Fin ρ.dimension) X ℂ)
    (hB : ∀ g, B * P g = ρ.matrix g * B) (g : Γ) :
    P g * B.conjTranspose = B.conjTranspose * ρ.matrix g := by
  have hPinv : P g⁻¹ = (P g).conjTranspose := by
    calc
      P g⁻¹ = 1 * P g⁻¹ := (one_mul _).symm
      _ = ((P g).conjTranspose * P g) * P g⁻¹ := by rw [hP g]
      _ = (P g).conjTranspose := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  have h := congrArg Matrix.conjTranspose (hB g⁻¹)
  have hrinv : ρ.matrix g⁻¹ = (ρ.matrix g).conjTranspose := by
    calc
      ρ.matrix g⁻¹ = 1 * ρ.matrix g⁻¹ := (one_mul _).symm
      _ = ((ρ.matrix g).conjTranspose * ρ.matrix g) * ρ.matrix g⁻¹ := by rw [ρ.unitary g]
      _ = (ρ.matrix g).conjTranspose := by rw [mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
  simpa only [Matrix.conjTranspose_mul, hPinv, hrinv,
    Matrix.conjTranspose_conjTranspose] using h

/- Schur's lemma makes every nonzero intertwiner a scalar coisometry. -/
theorem intertwiner_gram_scalar {X : Type*} [Fintype X] [DecidableEq X]
    (P : Γ →* Matrix X X ℂ) (hP : ∀ g, (P g).conjTranspose * P g = 1)
    (B : Matrix (Fin ρ.dimension) X ℂ)
    (hB : ∀ g, B * P g = ρ.matrix g * B) :
    ∃ c : ℂ, B * B.conjTranspose = c • (1 : Matrix _ _ ℂ) := by
  apply ρ.commuting_scalar
  intro g
  rw [Matrix.mul_assoc, ← ρ.adjoint_intertwines P hP B hB g,
    ← Matrix.mul_assoc, hB g, Matrix.mul_assoc]

/- Exact norm transfer, with no extraneous dimension loss. Q need agree with
an averaged permutation operator only on the adjoint intertwiner range. -/
theorem norm_le_compression {X : Type*} [Fintype X] [DecidableEq X]
    (P : Γ →* Matrix X X ℂ) (hP : ∀ g, (P g).conjTranspose * P g = 1)
    (B : Matrix (Fin ρ.dimension) X ℂ) (hne : B ≠ 0)
    (hB : ∀ g, B * P g = ρ.matrix g * B)
    (K : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ) (Q : Matrix X X ℂ)
    (hQ : Q * B.conjTranspose = B.conjTranspose * K) : ‖K‖ ≤ ‖Q‖ := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  obtain ⟨c, hc⟩ := ρ.intertwiner_gram_scalar P hP B hB
  have hn : ‖B‖ * ‖B‖ = ‖c‖ := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self B.conjTranspose
    simpa only [Matrix.conjTranspose_conjTranspose, Matrix.l2_opNorm_conjTranspose,
      hc, norm_smul, norm_one, mul_one] using h.symm
  have hcpos : 0 < ‖c‖ := by rw [← hn]; exact mul_pos (norm_pos_iff.mpr hne) (norm_pos_iff.mpr hne)
  have he : c • K = B * Q * B.conjTranspose := by
    rw [Matrix.mul_assoc, hQ, ← Matrix.mul_assoc, hc, Matrix.smul_mul, one_mul]
  have hbound : ‖c‖ * ‖K‖ ≤ ‖c‖ * ‖Q‖ := by
    rw [← norm_smul, he]
    calc
      ‖B * Q * B.conjTranspose‖ ≤ ‖B * Q‖ * ‖B.conjTranspose‖ := Matrix.l2_opNorm_mul _ _
      _ ≤ (‖B‖ * ‖Q‖) * ‖B.conjTranspose‖ :=
        mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _)
      _ = (‖B‖ * ‖B‖) * ‖Q‖ := by rw [Matrix.l2_opNorm_conjTranspose]; ring
      _ = ‖c‖ * ‖Q‖ := by rw [hn]
  exact (mul_le_mul_iff_right₀ hcpos).mp hbound
end UnitaryIrrep
end CoordinateSweeps

noncomputable section
universe u v
open scoped ComplexConjugate

namespace CoordinateSweeps
/- The pointwise stabilizer of two sites, used in the sparse dimension bridge. -/

namespace SparseDimension
variable {Ω V : Type*} [Fintype Ω] [DecidableEq Ω]
  [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/- Generic Schur commutant lemma, with no classification assumptions. -/
theorem commuting_scalar {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible]
    (A : Module.End ℂ V) (hA : ∀ g, A * ρ g = ρ g * A) :
    ∃ c : ℂ, A = c • (1 : Module.End ℂ V) := by
  let F : Representation.IntertwiningMap ρ ρ :=
    { toLinearMap := A
      isIntertwining' := hA }
  obtain ⟨c, hc⟩ := Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := ρ) |>.2 F
  refine ⟨c, ?_⟩
  have hh := congrArg Representation.IntertwiningMap.toLinearMap hc
  exact hh.symm

/- If all operators are scalar, irreducibility forces one dimension. -/
omit [FiniteDimensional ℂ V] in
theorem finrank_eq_one_of_scalars {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible]
    (hs : ∀ g, ∃ c : ℂ, ρ g = c • (1 : Module.End ℂ V)) :
    Module.finrank ℂ V = 1 := by
  have : Nontrivial V := by
    by_contra hn
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have he : (⊥ : Subrepresentation ρ) = ⊤ := by
      apply Subrepresentation.toSubmodule_injective
      exact Subsingleton.elim _ _
    exact bot_ne_top he
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let S : Subrepresentation ρ :=
    { toSubmodule := ℂ ∙ v
      apply_mem_toSubmodule := by
        intro g x hx
        obtain ⟨c, hc⟩ := hs g
        rw [hc]
        exact Submodule.smul_mem _ c hx }
  have hne : S ≠ ⊥ := by
    intro he
    have hm : v ∈ S := Submodule.mem_span_singleton_self _
    rw [he] at hm
    exact hv hm
  have he : S = ⊤ := (eq_bot_or_eq_top S).resolve_left hne
  have he' : (ℂ ∙ v : Submodule ℂ V) = ⊤ := congrArg Subrepresentation.toSubmodule he
  rw [← finrank_top ℂ V, ← he']
  exact finrank_span_singleton hv

theorem exists_minimal_constituent {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [Nontrivial V] :
    ∃ S : Subrepresentation ρ, 0 < Module.finrank ℂ S.toSubmodule ∧
      S.toRepresentation.IsIrreducible ∧
      ∀ T : Subrepresentation ρ, T ≠ ⊥ →
        Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
  classical
  have hp : ∃ n, ∃ S : Subrepresentation ρ,
      0 < Module.finrank ℂ S.toSubmodule ∧ Module.finrank ℂ S.toSubmodule = n :=
    ⟨Module.finrank ℂ V, ⊤, by simpa using (Module.finrank_pos (R := ℂ) (M := V)), by simp⟩
  obtain ⟨S, hSpos, hSdim⟩ := Nat.find_spec hp
  have hmin (T : Subrepresentation ρ) (hT : T ≠ ⊥) :
      Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ T.toSubmodule := by
    rw [hSdim]
    apply Nat.find_min' hp
    refine ⟨T, ?_, rfl⟩
    apply Module.finrank_pos_iff.mpr
    apply Submodule.nontrivial_iff_ne_bot.mpr
    exact fun ht => hT (Subrepresentation.toSubmodule_injective ht)
  refine ⟨S, hSpos, ?_, hmin⟩
  have : Nontrivial S.toSubmodule := Module.finrank_pos_iff.mp hSpos
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro he
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
  · intro T
    by_cases hT : T = ⊥
    · exact Or.inl hT
    right
    by_contra htop
    have hTp : 0 < Module.finrank ℂ T.toSubmodule := by
      apply Module.finrank_pos_iff.mpr
      apply Submodule.nontrivial_iff_ne_bot.mpr
      exact fun ht => hT (Subrepresentation.toSubmodule_injective ht)
    have hdim : Module.finrank ℂ (nested S T).toSubmodule = Module.finrank ℂ T.toSubmodule :=
      S.toSubmodule.finrank_map_subtype_eq T.toSubmodule
    have hnb : nested S T ≠ ⊥ := by
      intro he
      have hz : Module.finrank ℂ (nested S T).toSubmodule = 0 := by rw [he]; simp
      omega
    have hlow := hmin (nested S T) hnb
    rw [hdim] at hlow
    have hhigh : Module.finrank ℂ T.toSubmodule < Module.finrank ℂ S.toSubmodule :=
      Submodule.finrank_lt (fun ht => htop (Subrepresentation.toSubmodule_injective ht))
    omega

/- Every reducible finite-group representation has a constituent of at most
half its dimension. This uses Maschke over ℂ, not an assumed decomposition. -/
theorem exists_constituent_le_half {Γ : Type*} [Group Γ] [Fintype Γ]
    (ρ : Representation ℂ Γ V) [Nontrivial V]
    (hn : ¬ρ.IsIrreducible) :
    ∃ S : Subrepresentation ρ, 0 < Module.finrank ℂ S.toSubmodule ∧
      S.toRepresentation.IsIrreducible ∧
      2 * Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ V := by
  classical
  obtain ⟨S, hpos, hirr, hmin⟩ := exists_minimal_constituent ρ
  have hnon : ∃ T : Subrepresentation ρ, T ≠ ⊥ ∧ T ≠ ⊤ := by
    by_contra h
    apply hn
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
    · intro he
      exact bot_ne_top (congrArg Subrepresentation.toSubmodule he)
    · intro T
      simpa only [not_exists, not_and_or, not_not] using (not_exists.mp h T)
  obtain ⟨T, hTbot, hTtop⟩ := hnon
  have hSt : S ≠ ⊤ := by
    intro he
    have hd := hmin T hTbot
    have ht : Module.finrank ℂ T.toSubmodule < Module.finrank ℂ V :=
      Submodule.finrank_lt (fun ht => hTtop (Subrepresentation.toSubmodule_injective ht))
    rw [he] at hd
    simp only [subrep_top_toSubmodule, finrank_top] at hd
    omega
  let : NeZero (Nat.card Γ : ℂ) := ⟨by exact_mod_cast Nat.card_pos.ne'⟩
  obtain ⟨U, hU⟩ := exists_isCompl S
  have hUb : U ≠ ⊥ := by
    intro he
    have h := hU.sup_eq_top
    rw [he, sup_bot_eq] at h
    exact hSt h
  have hle := hmin U hUb
  have hcompl : IsCompl S.toSubmodule U.toSubmodule := by
    apply IsCompl.of_eq
    · exact congrArg Subrepresentation.toSubmodule hU.inf_eq_bot
    · exact congrArg Subrepresentation.toSubmodule hU.sup_eq_top
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  exact ⟨S, hpos, hirr, by omega⟩

/- Restriction to permutations fixing two distinct sites is not irreducible,
unless the full irreducible is one-dimensional. This gives a factor-two
dimension descent every two removed cards, needed for sparse types. -/
theorem finrank_eq_one_of_fixTwo_irreducible
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (a b : Ω) (hab : a ≠ b)
    [hirr : Representation.IsIrreducible (ρ.comp (fixTwo a b).subtype)] :
    Module.finrank ℂ V = 1 := by
  have hc : ∀ g : fixTwo a b,
      ρ (Equiv.swap a b) * ρ g.val = ρ g.val * ρ (Equiv.swap a b) := by
    intro g
    rw [← map_mul, ← map_mul]
    congr 1
    rw [Equiv.mul_swap_eq_swap_mul, g.property.1, g.property.2]
  obtain ⟨c, hc⟩ := commuting_scalar (ρ.comp (fixTwo a b).subtype) (ρ (Equiv.swap a b)) hc
  have hswap (x y : Ω) (hxy : x ≠ y) : ρ (Equiv.swap x y) = c • (1 : Module.End ℂ V) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hxy)
    rw [← hg, map_mul, map_mul, hc]
    simp only [mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one]
  apply finrank_eq_one_of_scalars ρ
  intro g
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, by simp⟩
  | swap_mul g x y hxy ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨c*d, ?_⟩
    rw [map_mul, hswap x y hxy, hd, smul_mul_smul_comm, one_mul]

/- Restriction along a surjective homomorphism preserves irreducibility. -/
omit [FiniteDimensional ℂ V] in
theorem irreducible_comp_surjective {Γ Δ : Type*} [Group Γ] [Group Δ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible]
    (f : Δ →* Γ) (hf : Function.Surjective f) :
    Representation.IsIrreducible (ρ.comp f) := by
  have he (S : Subrepresentation (ρ.comp f)) :
      S.toSubmodule = ⊥ ∨ S.toSubmodule = ⊤ := by
    let T : Subrepresentation ρ :=
      { toSubmodule := S.toSubmodule
        apply_mem_toSubmodule := by
          intro g v hv
          obtain ⟨x, rfl⟩ := hf g
          exact S.apply_mem_toSubmodule x hv }
    exact (eq_bot_or_eq_top T).imp
      (congrArg Subrepresentation.toSubmodule) (congrArg Subrepresentation.toSubmodule)
  have : Nontrivial V := by
    by_contra hn
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    apply bot_ne_top (α := Subrepresentation ρ)
    exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)
  refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := ?_ }
  · intro h
    exact bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  · intro S
    exact (he S).imp (fun h => Subrepresentation.toSubmodule_injective h)
      (fun h => Subrepresentation.toSubmodule_injective h)

/- Permutations of the complementary sites, viewed in the two-point stabilizer. -/

omit [Fintype Ω] in
theorem fixTwoHom_surjective (a b : Ω) : Function.Surjective (fixTwoHom a b) := by
  intro g
  have hi (x : Ω) : ((g.val x ≠ a ∧ g.val x ≠ b) ↔ (x ≠ a ∧ x ≠ b)) := by
    have ha : g.val x = a ↔ x = a :=
      ⟨fun h => g.val.injective (h.trans g.property.1.symm), fun h => h ▸ g.property.1⟩
    have hb : g.val x = b ↔ x = b :=
      ⟨fun h => g.val.injective (h.trans g.property.2.symm), fun h => h ▸ g.property.2⟩
    simp only [ne_eq, ha, hb]
  refine ⟨g.val.subtypePerm hi, Subtype.ext ?_⟩
  apply Equiv.Perm.ofSubtype_subtypePerm hi
  intro x hx
  constructor
  · intro he; subst x; exact hx g.property.1
  · intro he; subst x; exact hx g.property.2

/- One factor-two dimension descent, with the remaining symmetric group
realized literally as permutations of the complement. -/
theorem exists_half_constituent_fixTwo
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] [Nontrivial V]
    (hd : Module.finrank ℂ V ≠ 1) (a b : Ω) (hab : a ≠ b) :
    ∃ S : Subrepresentation (ρ.comp (fixTwo a b).subtype),
      0 < Module.finrank ℂ S.toSubmodule ∧
      Representation.IsIrreducible (S.toRepresentation.comp (fixTwoHom a b)) ∧
      2 * Module.finrank ℂ S.toSubmodule ≤ Module.finrank ℂ V := by
  classical
  have hn : ¬Representation.IsIrreducible (ρ.comp (fixTwo a b).subtype) := by
    intro hirr
    let := hirr
    exact hd (finrank_eq_one_of_fixTwo_irreducible ρ a b hab)
  obtain ⟨S, hpos, hirr, hdim⟩ := exists_constituent_le_half (ρ.comp (fixTwo a b).subtype) hn
  let := hirr
  exact ⟨S, hpos, irreducible_comp_surjective S.toRepresentation
    (fixTwoHom a b) (fixTwoHom_surjective a b), hdim⟩

/- Nonzero state space follows from irreducibility, including degenerate groups. -/
omit [FiniteDimensional ℂ V] in
theorem irreducible_nontrivial {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible] : Nontrivial V := by
  by_contra hn
  have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
  apply bot_ne_top (α := Subrepresentation ρ)
  exact Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _)

/- A one-dimensional constituent is already visible after at most twice the
base-two logarithm of the dimension many fixed cards. The power formulation
avoids rounding conventions and is valid also for dimension one. -/
theorem sparse_line_by_dim (D : ℕ) :
    ∀ (Ω : Type u) [Fintype Ω] [DecidableEq Ω]
      (V : Type v) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible],
      Module.finrank ℂ V = D →
      ∃ (t : ℕ) (A : Finset Ω) (W : Submodule ℂ V),
        Module.finrank ℂ W = 1 ∧ A.card ≤ 2*t ∧ 2^t ≤ D ∧
        ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) →
          ∀ w ∈ W, ρ g w ∈ W := by
  classical
  induction D using Nat.strong_induction_on with
  | h D ih =>
    intro Ω _ _ V _ _ _ ρ hirr hD
    have : Nontrivial V := irreducible_nontrivial ρ
    have hDpos : 0 < D := hD ▸ Module.finrank_pos
    by_cases hD1 : D = 1
    · refine ⟨0, ∅, ⊤, ?_, by simp, by simp [hD1], ?_⟩
      · simpa only [finrank_top] using hD.trans hD1
      · intro g hg w hw; trivial
    have hΩ : Nontrivial Ω := by
      by_contra hn
      have : Subsingleton Ω := not_nontrivial_iff_subsingleton.mp hn
      have hscalar : ∀ g : Equiv.Perm Ω, ∃ c : ℂ, ρ g = c • (1 : Module.End ℂ V) := by
        intro g
        have he : g = 1 := Subsingleton.elim _ _
        exact ⟨1, by rw [he, map_one, one_smul]⟩
      exact hD1 (hD.symm.trans (finrank_eq_one_of_scalars ρ hscalar))
    let := hΩ
    obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
    obtain ⟨S, hSpos, hSirr, hShalf⟩ := exists_half_constituent_fixTwo ρ
      (by simpa only [hD] using hD1) a b hab
    let ρ' : Representation ℂ (Equiv.Perm {x : Ω // x ≠ a ∧ x ≠ b}) S.toSubmodule :=
      S.toRepresentation.comp (fixTwoHom a b)
    let : ρ'.IsIrreducible := hSirr
    have hlt : Module.finrank ℂ S.toSubmodule < D := by rw [hD] at hShalf; omega
    obtain ⟨t, A, W, hWdim, hAcard, ht, hWstable⟩ :=
      ih (Module.finrank ℂ S.toSubmodule) hlt {x : Ω // x ≠ a ∧ x ≠ b}
        S.toSubmodule ρ' rfl
    let B : Finset Ω := insert a (insert b (A.image Subtype.val))
    refine ⟨t+1, B, W.map S.toSubmodule.subtype, ?_, ?_, ?_, ?_⟩
    · rw [Submodule.finrank_map_subtype_eq, hWdim]
    · have hc := Finset.card_image_le (s := A) (f := Subtype.val)
      have h1 := Finset.card_insert_le a (insert b (A.image Subtype.val))
      have h2 := Finset.card_insert_le b (A.image Subtype.val)
      dsimp [B]
      omega
    · rw [pow_succ]
      rw [hD] at hShalf
      omega
    · intro g hg w hw
      obtain ⟨w, hw, rfl⟩ := hw
      have hga : g a = a := hg a (by simp [B])
      have hgb : g b = b := hg b (by simp [B])
      obtain ⟨σ, hσ⟩ := fixTwoHom_surjective a b ⟨g, hga, hgb⟩
      have hsfix : ∀ x ∈ A, σ x = x := by
        intro x hx
        apply Subtype.ext
        calc
          (σ x).val = (fixTwoHom a b σ).val x.val :=
            (Equiv.Perm.ofSubtype_apply_coe σ x).symm
          _ = g x.val := congrArg (fun f : fixTwo a b => f.val x.val) hσ
          _ = x.val := hg x.val (by simp [B, Finset.mem_image_of_mem _ hx])
      refine ⟨ρ' σ w, hWstable σ hsfix w hw, ?_⟩
      change ρ ((fixTwoHom a b σ).val) w.val = ρ g w.val
      rw [hσ]

/- The rounded-free quantitative sparse dimension bridge for the actual
symmetric group, independent of a partition classification. -/
theorem exists_sparse_line
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] :
    ∃ (t : ℕ) (A : Finset Ω) (W : Submodule ℂ V),
      Module.finrank ℂ W = 1 ∧ A.card ≤ 2*t ∧ 2^t ≤ Module.finrank ℂ V ∧
      ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) →
        ∀ w ∈ W, ρ g w ∈ W :=
  sparse_line_by_dim _ Ω V ρ rfl

/- Ordinary permutation sign, embedded into the complex scalars. -/
theorem oneDimensional_trivial_or_sign
    (ρ : Representation ℂ (Equiv.Perm Ω) V) (hd : Module.finrank ℂ V = 1) :
    (∀ g, ρ g = 1) ∨ (∀ g, ρ g = signScalar g • (1 : Module.End ℂ V)) := by
  classical
  by_cases hΩ : Nontrivial Ω
  swap
  · have : Subsingleton Ω := not_nontrivial_iff_subsingleton.mp hΩ
    left
    intro g
    rw [Subsingleton.elim g 1, map_one]
  let := hΩ
  obtain ⟨a, b, hab⟩ := exists_pair_ne Ω
  obtain ⟨c, hc, _⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hd (ρ (Equiv.swap a b))
  change ρ (Equiv.swap a b) = c • (1 : Module.End ℂ V) at hc
  have hsame (x y : Ω) (hxy : x ≠ y) : ρ (Equiv.swap x y) = c • (1 : Module.End ℂ V) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (Equiv.Perm.isConj_swap hab hxy)
    rw [← hg, map_mul, map_mul, hc]
    simp only [mul_smul_comm, mul_one, smul_mul_assoc, ← map_mul, mul_inv_cancel, map_one]
  have hc2 : c*c = 1 := by
    apply (LinearEquiv.smul_id_of_finrank_eq_one hd).injective
    simp only [LinearEquiv.smul_id_of_finrank_eq_one_apply]
    change (c*c) • (1 : Module.End ℂ V) = 1 • (1 : Module.End ℂ V)
    rw [one_smul]
    calc
      (c*c) • (1 : Module.End ℂ V) = (c • (1 : Module.End ℂ V))*(c • 1) := by
        simp only [smul_mul_smul_comm, one_mul]
      _ = 1 := by rw [← hc, ← map_mul, Equiv.swap_mul_self, map_one]
  rcases mul_self_eq_one_iff.mp hc2 with hc1 | hcn
  · left
    intro g
    induction g using Equiv.Perm.swap_induction_on with
    | one => exact map_one _
    | swap_mul g x y hxy ih => rw [map_mul, hsame x y hxy, hc1, one_smul, ih, one_mul]
  · right
    intro g
    induction g using Equiv.Perm.swap_induction_on with
    | one => simp
    | swap_mul g x y hxy ih =>
      rw [map_mul, hsame x y hxy, hcn, ih, map_mul, signScalar_swap x y hxy,
        smul_mul_smul_comm, one_mul]

/- The cyclic span proof underlying the irreducible dimension lemma,
on an arbitrary finite-dimensional realization. -/
omit [FiniteDimensional ℂ V] in
theorem orbit_span_top {Γ : Type*} [Group Γ]
    (ρ : Representation ℂ Γ V) [ρ.IsIrreducible] (v : V) (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range (fun g => ρ g v)) = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range (fun g => ρ g v))
      apply_mem_toSubmodule := by
        intro g w hw
        induction hw using Submodule.span_induction with
        | mem w hw =>
          obtain ⟨k, rfl⟩ := hw
          rw [← Module.End.mul_apply, ← map_mul]
          exact Submodule.subset_span (Set.mem_range_self (g*k))
        | zero => simp
        | add x y hx hy hix hiy => simpa only [map_add] using Submodule.add_mem _ hix hiy
        | smul c x hx hi => simpa only [map_smul] using Submodule.smul_mem _ c hi }
  have hn : S ≠ ⊥ := by
    intro he
    have hm : v ∈ S := by
      change v ∈ Submodule.span ℂ (Set.range (fun g => ρ g v))
      apply Submodule.subset_span
      exact ⟨1, by simp⟩
    rw [he] at hm
    exact hv hm
  exact congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top S).resolve_left hn)

/- The upper sparse dimension bound: a line invariant under the stabilizer
of k named sites gives at most n^k dimensions in its irreducible orbit. -/
theorem dimension_le_pow_of_stable_line
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible]
    (A : Finset Ω) (W : Submodule ℂ V) (hW : Module.finrank ℂ W = 1)
    (hstable : ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ∀ w ∈ W, ρ g w ∈ W) :
    Module.finrank ℂ V ≤ (Fintype.card Ω)^A.card := by
  classical
  have : Nontrivial W := (Module.finrank_pos_iff (R := ℂ) (M := W)).mp (by omega)
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  have hv' : v.val ≠ 0 := by intro he; exact hv (Subtype.ext he)
  let restrict (g : Equiv.Perm Ω) : A → Ω := fun a => g a.val
  let chooseG (x : A → Ω) : Equiv.Perm Ω :=
    if hx : ∃ g, restrict g = x then Classical.choose hx else 1
  have hchoose (g : Equiv.Perm Ω) : restrict (chooseG (restrict g)) = restrict g := by
    dsimp [chooseG]
    rw [dite_eq_left (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)]
    exact Classical.choose_spec (show ∃ h, restrict h = restrict g from ⟨g, rfl⟩)
  let u (x : A → Ω) : V := ρ (chooseG x) v.val
  have hspan : Submodule.span ℂ (Set.range u) = ⊤ := by
    rw [eq_top_iff, ← orbit_span_top ρ v.val hv']
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    let r := chooseG (restrict g)
    have hfix : ∀ a ∈ A, (r⁻¹*g) a = a := by
      intro a ha
      have he := congrFun (hchoose g) ⟨a, ha⟩
      change r a = g a at he
      simp only [Equiv.Perm.mul_apply]
      rw [← he]; simp
    have hw : ρ (r⁻¹*g) v.val ∈ W := hstable _ hfix _ v.property
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hW hv
      (⟨ρ (r⁻¹*g) v.val, hw⟩ : W)
    have he : ρ g v.val = c • u (restrict g) := by
      have hh := congrArg (fun w : W => ρ r w.val) hc
      change ρ r (c • v.val) = ρ r (ρ (r⁻¹*g) v.val) at hh
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left] at hh
      exact hh.symm
    change ρ g v.val ∈ Submodule.span ℂ (Set.range u)
    rw [he]
    exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_range_self _))
  have hd := finrank_le_of_span_eq_top hspan
  simpa only [Fintype.card_fun, Fintype.card_coe] using hd

/- Pointwise stabilizer of a named finite set of sites. -/

omit [Fintype Ω] in
theorem fixSetHom_surjective (A : Finset Ω) : Function.Surjective (fixSetHom A) := by
  intro g
  have hi (x : Ω) : (g.val x ∉ A) ↔ x ∉ A := by
    constructor
    · intro h hx
      apply h
      rwa [g.property x hx]
    · intro h hx
      have he := g.property (g.val x) hx
      have he' : g.val x = x := g.val.injective he
      exact h (he' ▸ hx)
  refine ⟨g.val.subtypePerm hi, Subtype.ext ?_⟩
  apply Equiv.Perm.ofSubtype_subtypePerm hi
  intro x hx
  by_contra hn
  exact hx (g.property x (by simpa using hn))

/- A stable line under a pointwise stabilizer is a literal trivial or sign
line. There is no hypothesis about a partition or a pre-existing embedding. -/
theorem stable_line_trivial_or_sign
    (ρ : Representation ℂ (Equiv.Perm Ω) V)
    (A : Finset Ω) (W : Submodule ℂ V) (hW : Module.finrank ℂ W = 1)
    (hstable : ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ∀ w ∈ W, ρ g w ∈ W) :
    ∃ u : V, u ≠ 0 ∧
      ((∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = u) ∨
       (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = signScalar g • u)) := by
  classical
  let S : Subrepresentation (ρ.comp (fixSet A).subtype) :=
    { toSubmodule := W
      apply_mem_toSubmodule := fun g w hw => hstable g.val g.property w hw }
  let ρ' := S.toRepresentation.comp (fixSetHom A)
  have : Nontrivial W := (Module.finrank_pos_iff (R := ℂ) (M := W)).mp (by omega)
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  refine ⟨u.val, fun he => hu (Subtype.ext he), ?_⟩
  rcases oneDimensional_trivial_or_sign ρ' hW with ht | hs
  · left
    intro g hg
    obtain ⟨σ, hσ⟩ := fixSetHom_surjective A ⟨g, hg⟩
    have he := congrArg (fun T : Module.End ℂ W => (T u).val) (ht σ)
    change ρ ((fixSetHom A σ).val) u.val = u.val at he
    simpa only [hσ] using he
  · right
    intro g hg
    obtain ⟨σ, hσ⟩ := fixSetHom_surjective A ⟨g, hg⟩
    have he := congrArg (fun T : Module.End ℂ W => (T u).val) (hs σ)
    change ρ ((fixSetHom A σ).val) u.val = signScalar σ • u.val at he
    simp only [signScalar_apply] at he ⊢
    rw [← Equiv.Perm.sign_ofSubtype σ] at he
    simpa only [← fixSetHom_val, hσ] using he

/- Minimal signed placement level with both dimension bounds. The last
clause rules out every earlier line, hence in particular every earlier fixed
vector of either the representation or its sign twist. -/
theorem exists_minimal_sparse_line
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] :
    ∃ (k t : ℕ) (A : Finset Ω) (u : V),
      A.card = k ∧ k ≤ 2*t ∧ 2^t ≤ Module.finrank ℂ V ∧
      Module.finrank ℂ V ≤ (Fintype.card Ω)^k ∧ u ≠ 0 ∧
      ((∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = u) ∨
       (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ρ g u = signScalar g • u)) ∧
      ∀ B : Finset Ω, B.card < k → ∀ (v : V),
        (∀ g : Equiv.Perm Ω, (∀ a ∈ B, g a = a) → ∃ c : ℂ, ρ g v = c • v) → v = 0 := by
  classical
  let P (k : ℕ) : Prop := ∃ (A : Finset Ω) (W : Submodule ℂ V), A.card = k ∧
    Module.finrank ℂ W = 1 ∧
    ∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → ∀ w ∈ W, ρ g w ∈ W
  obtain ⟨t, A₀, W₀, hW₀, hA₀, ht, hs₀⟩ := exists_sparse_line ρ
  have hex : ∃ k, P k := ⟨A₀.card, A₀, W₀, rfl, hW₀, hs₀⟩
  obtain ⟨A, W, hA, hW, hs⟩ := Nat.find_spec hex
  have hk : Nat.find hex ≤ A₀.card := Nat.find_min' hex ⟨A₀, W₀, rfl, hW₀, hs₀⟩
  obtain ⟨u, hu, hchar⟩ := stable_line_trivial_or_sign ρ A W hW hs
  refine ⟨Nat.find hex, t, A, u, hA, hk.trans hA₀, ht, ?_, hu, hchar, ?_⟩
  · rw [← hA]
    exact dimension_le_pow_of_stable_line ρ A W hW hs
  · intro B hB v hv
    by_contra hn
    have hp : P B.card := by
      refine ⟨B, ℂ ∙ v, rfl, finrank_span_singleton hn, ?_⟩
      intro g hg w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      obtain ⟨r, hr⟩ := hv g hg
      rw [map_smul, hr, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    exact Nat.find_min hex hB hp
end SparseDimension
end CoordinateSweeps

noncomputable section
open scoped BigOperators

namespace CoordinateSweeps.PlacementOccurrence
variable {Γ X V : Type*} [Group Γ] [Fintype Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]
    [AddCommGroup V] [Module ℂ V]

/- Sum of orbit vectors against placement coordinates. The repeated
stabilizer fibers are left in the sum, so no transversal choice is needed. -/
omit [Fintype X] [DecidableEq X] in
theorem orbitSynthesis_covariant (ρ : Representation ℂ Γ V) (u : V) (x₀ : X)
    (h : Γ) (f : X → ℂ) :
    orbitSynthesis ρ u x₀ (fun x => f (h⁻¹ • x)) = ρ h (orbitSynthesis ρ u x₀ f) := by
  change (∑ g, f (h⁻¹ • (g • x₀)) • ρ g u) = ρ h (∑ g, f (g • x₀) • ρ g u)
  rw [← Equiv.sum_comp (Equiv.mulLeft h) (fun g => f (h⁻¹ • (g • x₀)) • ρ g u)]
  simp only [Equiv.coe_mulLeft, mul_smul, inv_smul_smul, map_sum, map_smul,
    map_mul, Module.End.mul_apply]

/- A vector fixed by the point stabilizer produces a nonzero synthesis map. -/
omit [Fintype X] in
theorem orbitSynthesis_delta_ne_zero (ρ : Representation ℂ Γ V) (u : V) (hu : u ≠ 0)
    (x₀ : X) (hfixed : ∀ g : Γ, g • x₀ = x₀ → ρ g u = u) :
    orbitSynthesis ρ u x₀ (fun x => if x = x₀ then 1 else 0) ≠ 0 := by
  classical
  have he : orbitSynthesis ρ u x₀ (fun x => if x = x₀ then 1 else 0) =
      ((Finset.univ.filter (fun g : Γ => g • x₀ = x₀)).card : ℂ) • u := by
    change (∑ g, (if g • x₀ = x₀ then (1 : ℂ) else 0) • ρ g u) = _
    simp only [ite_smul, one_smul, zero_smul]
    calc
      _ = ∑ g : Γ, if g • x₀ = x₀ then u else 0 := by
        apply Finset.sum_congr rfl
        intro g _
        split_ifs with hg
        · exact hfixed g hg
        · rfl
      _ = _ := by rw [← Finset.sum_filter]; simp [Nat.cast_smul_eq_nsmul]
  rw [he]
  apply smul_ne_zero _ hu
  norm_cast
  apply Nat.ne_of_gt
  apply Finset.card_pos.mpr
  exact ⟨1, by simp⟩

/- Frobenius occurrence at the precise stabilizer level, proved by an
explicit intertwiner rather than postulated decomposition. -/
omit [Fintype Γ] in
theorem subgroup_sum_fixed (ρ : Representation ℂ Γ V) (K : Subgroup Γ) [Fintype K] (u : V)
    (k : K) : ρ k.val (∑ h : K, ρ h.val u) = ∑ h : K, ρ h.val u := by
  simp only [map_sum, ← Module.End.mul_apply, ← map_mul]
  exact Equiv.sum_comp (Equiv.mulLeft k) (fun h : K => ρ h.val u)

/- Averaging a synthesis over a larger stabilizer acts only on the cyclic
vector whenever the coefficient function forgets those coordinates. -/
omit [Fintype X] [DecidableEq X] in
theorem orbitSynthesis_subgroup_average (ρ : Representation ℂ Γ V) (u : V) (x₀ : X)
    (K : Subgroup Γ) [Fintype K] (f : X → ℂ)
    (hf : ∀ (g : Γ) (k : K), f ((g*k.val) • x₀) = f (g • x₀)) :
    orbitSynthesis ρ (∑ k : K, ρ k.val u) x₀ f =
      (Fintype.card K : ℂ) • orbitSynthesis ρ u x₀ f := by
  change (∑ g, f (g • x₀) • ρ g (∑ k : K, ρ k.val u)) = _
  simp only [map_sum, Finset.smul_sum, ← Module.End.mul_apply, ← map_mul]
  rw [Finset.sum_comm]
  have hk (k : K) : (∑ g : Γ, f (g • x₀) • ρ (g*k.val) u) = orbitSynthesis ρ u x₀ f := by
    calc
      _ = ∑ g : Γ, f ((g*k.val) • x₀) • ρ (g*k.val) u := by
        simp only [hf]
      _ = _ := Equiv.sum_comp (Equiv.mulRight k.val) (fun g => f (g • x₀) • ρ g u)
  simp only [hk, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]

/- Exact proper-coordinate annihilation used in source04:eq7: it is the
absence of fixed vectors one level earlier, not a partial cancellation claim. -/
omit [Fintype X] [DecidableEq X] in
theorem orbitSynthesis_eq_zero_of_no_fixed (ρ : Representation ℂ Γ V) (u : V) (x₀ : X)
    (K : Subgroup Γ) [Fintype K]
    (hnof : ∀ v : V, (∀ k : K, ρ k.val v = v) → v = 0)
    (f : X → ℂ) (hf : ∀ (g : Γ) (k : K), f ((g*k.val) • x₀) = f (g • x₀)) :
    orbitSynthesis ρ u x₀ f = 0 := by
  have hzero : (∑ k : K, ρ k.val u) = 0 := hnof _ (subgroup_sum_fixed ρ K u)
  have h := orbitSynthesis_subgroup_average ρ u x₀ K f hf
  rw [hzero] at h
  have hz : orbitSynthesis ρ (0 : V) x₀ f = 0 := by simp [orbitSynthesis]
  rw [hz] at h
  apply (smul_eq_zero.mp h.symm).resolve_left
  exact_mod_cast Fintype.card_ne_zero
end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.SparseDimension
variable {Ω V : Type*} [Fintype Ω] [DecidableEq Ω]
  [AddCommGroup V] [Module ℂ V]

theorem exists_minimal_fixed_vector [FiniteDimensional ℂ V]
    (ρ : Representation ℂ (Equiv.Perm Ω) V) [ρ.IsIrreducible] :
    ∃ (ε : Bool) (k t : ℕ) (A : Finset Ω) (u : V),
      let τ := if ε then signTwist ρ else ρ
      A.card = k ∧ k ≤ 2*t ∧ 2^t ≤ Module.finrank ℂ V ∧
      Module.finrank ℂ V ≤ (Fintype.card Ω)^k ∧ u ≠ 0 ∧
      (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a = a) → τ g u = u) ∧
      ∀ B : Finset Ω, B.card < k → ∀ v : V,
        (∀ g : Equiv.Perm Ω, (∀ a ∈ B, g a = a) → τ g v = v) → v = 0 := by
  obtain ⟨k,t,A,u,hA,hk,ht,hd,hu,hchar,hmin⟩ := exists_minimal_sparse_line ρ
  rcases hchar with htriv | hsign
  · refine ⟨false,k,t,A,u,hA,hk,ht,hd,hu,htriv, ?_⟩
    intro B hB v hv
    exact hmin B hB v (fun g hg => ⟨1, by simpa using hv g hg⟩)
  · refine ⟨true,k,t,A,u,hA,hk,ht,hd,hu, ?_, ?_⟩
    · intro g hg
      simp only [↓reduceIte, signTwist_apply, hsign g hg, smul_smul,
        signScalar_mul_self, one_smul]
    · intro B hB v hv
      apply hmin B hB v
      intro g hg
      refine ⟨signScalar g, ?_⟩
      have h := congrArg (fun w : V => signScalar g • w) (hv g hg)
      simpa only [Bool.true_eq, ↓reduceIte, signTwist_apply, smul_smul,
        signScalar_mul_self, one_smul] using h
end CoordinateSweeps.SparseDimension

namespace CoordinateSweeps.PlacementOccurrence
open SparseDimension
variable {Ω I V : Type*} [Fintype Ω] [DecidableEq Ω]
  [Fintype I] [AddCommGroup V] [Module ℂ V]

/- Stabilizer of the small placement coordinates really is the pointwise
stabilizer of their image, so the exact earlier-level hypothesis applies. -/
theorem synthesis_kills_proper_coordinates
    (ρ : Representation ℂ (Equiv.Perm Ω) V) (u : V) (x₀ : I ↪ Ω)
    (hnof : ∀ B : Finset Ω, B.card < Fintype.card I → ∀ v : V,
      (∀ g : Equiv.Perm Ω, (∀ a ∈ B, g a = a) → ρ g v = v) → v = 0)
    (A : Finset I) (hA : A ≠ Finset.univ) (f : (I ↪ Ω) → ℂ)
    (hf : ∀ x y : I ↪ Ω, (∀ i ∈ A, x i = y i) → f x = f y) :
    orbitSynthesis ρ u x₀ f = 0 := by
  classical
  let B : Finset Ω := A.image x₀
  have hB : B.card < Fintype.card I := by
    dsimp [B]
    rw [Finset.card_image_of_injective _ x₀.injective]
    exact Finset.card_lt_card (Finset.ssubset_univ_iff.mpr hA)
  apply orbitSynthesis_eq_zero_of_no_fixed ρ u x₀ (fixSet B)
  · intro v hv
    exact hnof B hB v (fun g hg => hv ⟨g,hg⟩)
  · intro g k
    apply hf
    intro i hi
    change g (k.val (x₀ i)) = g (x₀ i)
    rw [k.property (x₀ i) (Finset.mem_image_of_mem _ hi)]
end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.Placement
variable {I U X Y : Type*} [Fintype I] [DecidableEq I] [Fintype X] [Fintype Y]
/- The adjoint of a synthesis map annihilating all cylinder functions lands
in the exact alternating-kernel top space. Complex conjugation is essential. -/
omit [DecidableEq I] in
theorem conjTranspose_mulVec_mem_top {D : Type*} [Fintype D]
    (coords : Y → I → U) (B : Matrix D Y ℂ)
    (hB : ∀ A : Finset I, A ≠ Finset.univ → ∀ f : Y → ℂ,
      DependsOn coords A f → B.mulVec f = 0) (w : D → ℂ) :
    B.conjTranspose.mulVec w ∈ topSpace coords := by
  intro A hA f hf
  have hfstar : DependsOn coords A (fun y => star (f y)) :=
    fun y y' h => congrArg star (hf y y' h)
  have hz := hB A hA (fun y => star (f y)) hfstar
  have hsum (d : D) : ∑ y, f y * star (B d y) = 0 := by
    have h := congrArg star (congrFun hz d)
    simpa only [Matrix.mulVec, dotProduct, star_sum, star_mul,
      star_star, Pi.zero_apply, star_zero, mul_comm] using h
  simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul, hsum, zero_mul]
  exact Finset.sum_const_zero

/- Matrix form of top-level compression, ready for Schur norm transfer. -/
omit [DecidableEq I] [Fintype X] in
theorem alternatingKernel_mul_conjTranspose {D : Type*} [Fintype D]
    (coords : Y → I → U) (s : ℝ) (hs : s ≠ 0)
    (p : Finset I → X → Y → ℝ)
    (hp : ∀ A x, DependsOn coords A (fun y => (p A x y : ℂ)))
    (B : Matrix D Y ℂ)
    (hB : ∀ A : Finset I, A ≠ Finset.univ → ∀ f : Y → ℂ,
      DependsOn coords A f → B.mulVec f = 0) :
    alternatingKernel s p * B.conjTranspose =
      (show Matrix X Y ℂ from fun x y => (p Finset.univ x y : ℂ)) * B.conjTranspose := by
  apply Matrix.ext
  intro x d
  have hv : (fun y => B.conjTranspose y d) ∈ topSpace coords := by
    classical
    have h := conjTranspose_mulVec_mem_top coords B hB (Pi.single d 1)
    have he : B.conjTranspose.mulVec (Pi.single d 1) = (fun y => B.conjTranspose y d) := by
      ext y; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rw [he] at h
    exact h
  exact congrFun (alternatingKernel_mulVec_top coords s hs p hp hv) x
end CoordinateSweeps.Placement

namespace CoordinateSweeps.PlacementOccurrence
open scoped Matrix.Norms.L2Operator
variable {Γ X : Type*} [Group Γ] [Fintype Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]

omit [Fintype Γ] in
lemma actionMatrix_mulVec (g : Γ) (f : X → ℂ) :
    (actionMatrix g).mulVec f=fun x => f (g⁻¹ • x) := by
  change (((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ).mulVec f = _
  rw [Matrix.permMatrix_mulVec]
  rfl

omit [Fintype Γ] in
lemma actionMatrix_unitary (g : Γ) : (actionMatrix (X := X) g).conjTranspose*actionMatrix g=1 := by
  change (((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ).conjTranspose*
    ((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ=1
  rw [Matrix.conjTranspose_permMatrix,inv_inv,← Matrix.permMatrix_mul,inv_mul_cancel,Matrix.permMatrix_one]

lemma synthesisMatrix_mulVec (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (x₀ : X) (f : X → ℂ) :
    (synthesisMatrix ρ u x₀).mulVec f=orbitSynthesis ρ.asRepresentation u x₀ f :=
  LinearMap.toMatrix'_mulVec _ _

lemma synthesisMatrix_covariant (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (x₀ : X) (g : Γ) :
    synthesisMatrix ρ u x₀*actionMatrix g=ρ.matrix g*synthesisMatrix ρ u x₀ := by
  change (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (synthesisMatrix ρ u x₀) (actionMatrix g))=
    (Matrix.instHMulOfFintypeOfMulOfAddCommMonoid.hMul (ρ.matrix g) (synthesisMatrix ρ u x₀))
  apply Matrix.mulVec_injective
  funext f
  rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,actionMatrix_mulVec,
    synthesisMatrix_mulVec,synthesisMatrix_mulVec]
  exact orbitSynthesis_covariant ρ.asRepresentation u x₀ g f

lemma synthesisMatrix_ne_zero (ρ : UnitaryIrrep Γ) (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : X)
    (hfixed : ∀ g : Γ, g • x₀=x₀ → ρ.asRepresentation g u=u) : synthesisMatrix ρ u x₀ ≠ 0 := by
  intro h
  have hh := orbitSynthesis_delta_ne_zero ρ.asRepresentation u hu x₀ hfixed
  apply hh
  rw [← synthesisMatrix_mulVec,h,Matrix.zero_mulVec]

end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.PlacementOccurrence
open scoped Matrix.Norms.L2Operator
open Placement
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]

/- Source04:eq7 at its exact first placement level, with a constructed
nonzero synthesis intertwiner and Schur norm transfer. -/
omit [DecidableEq I] in
theorem first_level_norm_le (ρ : UnitaryIrrep (Equiv.Perm Ω))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : I ↪ Ω)
    (hfixed : ∀ g : Equiv.Perm Ω, (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset Ω, A.card < Fintype.card I → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm Ω, (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0)
    {W : Type*} [Fintype W] (w : W → ℂ) (g : W → Equiv.Perm Ω)
    (s : ℝ) (hs : s ≠ 0) (p : Finset I → (I ↪ Ω) → (I ↪ Ω) → ℝ)
    (hp : ∀ A x, DependsOn (fun y : I ↪ Ω => y) A (fun y => (p A x y : ℂ)))
    (hfull : (show Matrix (I ↪ Ω) (I ↪ Ω) ℂ from fun x y => (p Finset.univ x y : ℂ))=
      ∑ a : W, w a • actionMatrix (X := I ↪ Ω) (g a)) :
    ‖∑ a : W, w a • ρ.matrix (g a)‖ ≤
      ‖alternatingKernel s p‖ := by
  let B : Matrix (Fin ρ.dimension) (I ↪ Ω) ℂ := synthesisMatrix ρ u x₀
  have hB : ∀ A : Finset I, A ≠ Finset.univ → ∀ f : (I ↪ Ω) → ℂ,
      DependsOn (fun y : I ↪ Ω => y) A f → B.mulVec f=0 := by
    intro A hA f hf
    rw [synthesisMatrix_mulVec]
    exact synthesis_kills_proper_coordinates ρ.asRepresentation u x₀ hnof A hA f hf
  have hne : B ≠ 0 := synthesisMatrix_ne_zero ρ u hu x₀ (by
    intro σ hσ
    exact hfixed σ (fun i => congrArg (fun x : I ↪ Ω => x i) hσ))
  have hnorm : ‖∑ a : W, w a • ρ.matrix (g a)‖ ≤ ‖alternatingKernel s p‖ := by
    apply ρ.norm_le_compression (actionMatrix (X := I ↪ Ω)) actionMatrix_unitary B hne
      (synthesisMatrix_covariant ρ u x₀)
    rw [alternatingKernel_mul_conjTranspose (fun y : I ↪ Ω => y) s hs p hp B hB,hfull,
      Matrix.sum_mul,Matrix.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [Matrix.smul_mul,Matrix.mul_smul]
    congr 1
    exact ρ.adjoint_intertwines _ actionMatrix_unitary B (synthesisMatrix_covariant ρ u x₀) (g a)
  exact hnorm

end CoordinateSweeps.PlacementOccurrence

open scoped Matrix.Norms.L2Operator

namespace CoordinateSweeps.PlacementOccurrence
variable {Γ X : Type*} [Group Γ] [Fintype X] [DecidableEq X] [MulAction Γ X]
lemma actionMatrix_entry (g : Γ) (x y : X) : actionMatrix (X := X) g x y=if g⁻¹ • x=y then 1 else 0 := by
  change (((MulAction.toPermHom Γ X g)⁻¹).permMatrix ℂ) x y=_
  simp [Equiv.Perm.permMatrix, PEquiv.toMatrix]
end CoordinateSweeps.PlacementOccurrence

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_SparseMoment
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}
open Coverage

theorem probability_holeHeavy_single (H : G.Holes h) {η : ℝ} (hη : 0 < η) (j : Fin G.b) :
    (∑ p : G.Slot × G.Slot, if G.pathLine p.1 p.2 j ∈ H.holeHeavy η j then G.endpointWeight p else 0) ≤
      2*h/((G.size : ℝ)*η) := by
  have hs : 0 < (G.size : ℝ) := by unfold Grid.size; positivity
  have hm : 0 < ((2^G.bits j : ℕ) : ℝ) := by positivity
  have ht : ∑ l, (H.lineCount j l : ℝ) = h := by exact_mod_cast H.sum_lineCount j
  have hc := heavySet_card_mul_le (H.lineCount j) (((2^G.bits j : ℕ) : ℝ)*η/2)
  rw [ht] at hc
  have hline : ∀ l : G.Line j,
      (∑ p : G.Slot × G.Slot, if G.pathLine p.1 p.2 j = l then G.endpointWeight p else 0) ≤
        ((2^G.bits j : ℕ) : ℝ)/G.size := by
    intro l
    exact le_of_eq (by simpa using G.probability_path_line j l)
  apply (probability_lineSet_le G.endpointWeight (fun p : G.Slot × G.Slot => G.pathLine p.1 p.2 j)
    (H.holeHeavy η j) (((2^G.bits j : ℕ) : ℝ)/G.size) hline).trans
  change ((heavySet (H.lineCount j) _).card : ℝ) * _ ≤ _
  apply (le_div_iff₀ (mul_pos hs hη)).mpr
  field_simp at ⊢
  nlinarith

theorem probability_holeHeavyHits_le (H : G.Holes h) {η : ℝ} (hη : 0 < η)
    (hp : 2*h/((G.size : ℝ)*η) ≤ 1) (j : Fin G.b) (u : ℝ) (hu : 0 ≤ u) :
    Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
      u ≤ ((H.holeHeavyHits p η j).card : ℝ)) ≤
      (2 : ℝ)^k * (2*h/((G.size : ℝ)*η))^u := by
  convert (probability_many_hits_le_rpow (I := Fin k) G.endpointWeight G.endpointWeight_nonneg
      G.endpointWeight_total (fun p : G.Slot × G.Slot => G.pathLine p.1 p.2 j ∈ H.holeHeavy η j)
      _ (by positivity) hp (by convert H.probability_holeHeavy_single hη j using 1; congr!) u hu) using 1 <;>
    simp only [holeHeavyHits, Fintype.card_fin]
  congr!

theorem probability_particleHeavyHits_le {η : ℝ} (hη : 0 < η)
    (hp : 2*k/((G.size : ℝ)*η) ≤ 1) (j : Fin G.b) (u : ℝ) (hu : 0 ≤ u) :
    Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
      u ≤ ((particleHeavyHits p η j).card : ℝ)) ≤
      ((Fintype.card (G.Line j)+1 : ℕ) : ℝ)^⌊2*k/(((2^G.bits j : ℕ) : ℝ)*η)⌋₊ *
        (2 : ℝ)^k * (2*k/((G.size : ℝ)*η))^u := by
  have hs : 0 < (G.size : ℝ) := by unfold Grid.size; positivity
  have hm : 0 < ((2^G.bits j : ℕ) : ℝ) := by positivity
  have hv : 0 < ((2^G.bits j : ℕ) : ℝ)*η/2 := by positivity
  have he : (k : ℝ)/(((2^G.bits j : ℕ) : ℝ)*η/2) = 2*k/(((2^G.bits j : ℕ) : ℝ)*η) := by ring
  have hf : (⌊(k : ℝ)/(((2^G.bits j : ℕ) : ℝ)*η/2)⌋₊ : ℝ)*
      (((2^G.bits j : ℕ) : ℝ)/G.size) ≤ 2*k/((G.size : ℝ)*η) := by
    apply le_trans (mul_le_mul_of_nonneg_right (Nat.floor_le (by positivity)) (by positivity))
    apply le_of_eq
    field_simp
  have hb := probability_heavy_occupancy_le (I := Fin k)
    G.endpointWeight G.endpointWeight_nonneg G.endpointWeight_total
    (fun p : G.Slot × G.Slot => G.pathLine p.1 p.2 j) hv
    (2*k/((G.size : ℝ)*η)) (((2^G.bits j : ℕ) : ℝ)/G.size)
    (by positivity) (by positivity) hp
    (fun l => le_of_eq (by simpa using G.probability_path_line j l))
    (by simpa using hf) u hu
  convert hb using 1 <;>
    simp only [particleHeavyHits, particleHeavy, Fintype.card_fin, he]
  congr!

theorem not_vertexIsolated_iff (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (i : Fin k) :
    ¬ H.VertexIsolated (fun i => (p i).1) (fun i => (p i).2) i ↔
      i ∈ sharingCoverage G.vertexShares H.endpointData p := by
  simp only [VertexIsolated, sharingCoverage, mem_covered, Grid.vertexShares]
  constructor
  · intro hi
    by_cases ha : ∀ a s, G.pathBetween (p i).1 (p i).2 s ≠ H.path a s
    · have hj : ¬ ∀ j, i ≠ j → ∀ s, G.pathBetween (p i).1 (p i).2 s ≠ G.pathBetween (p j).1 (p j).2 s := fun h => hi ⟨ha,h⟩
      push Not at hj
      obtain ⟨j,hij,t,hjt⟩ := hj
      exact Or.inl ⟨j,hij,t,hjt⟩
    · push Not at ha
      obtain ⟨a,t,hat⟩ := ha
      exact Or.inr ⟨a,t,hat.trans (H.path_eq_pathBetween hH a t)⟩
  · rintro (⟨j,hij,t,he⟩ | ⟨a,t,he⟩) hv
    · exact hv.2 j hij t he
    · exact hv.1 a t (he.trans (H.path_eq_pathBetween hH a t).symm)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}
open Coverage

theorem not_good_cover (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (η : ℝ) (i : Fin k)
    (hi : i ∉ H.goodSet (fun i => (p i).1) (fun i => (p i).2) η) :
    i ∈ sharingCoverage G.vertexShares H.endpointData p ∨
      ∃ j, i ∈ H.holeHeavyHits p η j ∨ i ∈ particleHeavyHits p η j := by
  have hn : ¬ H.Good (fun i => (p i).1) (fun i => (p i).2) η i := by simpa using hi
  by_cases hv : H.VertexIsolated (fun i => (p i).1) (fun i => (p i).2) i
  · right
    have hj : ¬ ∀ j, H.Light (fun i => (p i).1) (fun i => (p i).2) η
        (G.stagePath (fun i => (p i).1) (fun i => (p i).2) i j) := fun ht => hn ⟨hv,ht⟩
    push Not at hj
    obtain ⟨j,hj⟩ := hj
    refine ⟨j,?_⟩
    simp only [Light, Grid.stagePath, Nat.cast_add, not_le] at hj
    simp only [holeHeavyHits, particleHeavyHits, holeHeavy, particleHeavy,
      heavySet, Finset.mem_filter, Finset.mem_univ, true_and]
    change ((2^G.bits j : ℕ) : ℝ)*η/2 < (H.lineCount j (G.pathLine (p i).1 (p i).2 j) : ℝ) ∨
      ((2^G.bits j : ℕ) : ℝ)*η/2 < (auxCount (fun i => (p i).1) (fun i => (p i).2)
        Finset.univ j (G.pathLine (p i).1 (p i).2 j) : ℝ)
    by_contra hc
    push Not at hc
    linarith
  · exact Or.inl ((H.not_vertexIsolated_iff hH p i).mp hv)

theorem card_covered_by_good_and_bad (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (η : ℝ) :
    k ≤ (H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card +
      (sharingCoverage G.vertexShares H.endpointData p).card +
      ∑ j, ((H.holeHeavyHits p η j).card + (particleHeavyHits p η j).card) := by
  let A := H.goodSet (fun i => (p i).1) (fun i => (p i).2) η
  let V := sharingCoverage G.vertexShares H.endpointData p
  let B := (Finset.univ : Finset (Fin G.b)).biUnion
    (fun j => H.holeHeavyHits p η j ∪ particleHeavyHits p η j)
  have hc : (Finset.univ : Finset (Fin k)) ⊆ (A ∪ V) ∪ B := by
    intro i _
    by_cases hi : i ∈ A
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hi)
    · rcases H.not_good_cover hH p η i hi with hv | ⟨j,hj⟩
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hv)
      · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
          ⟨j,Finset.mem_univ _, Finset.mem_union.mpr hj⟩)
  calc
    k = (Finset.univ : Finset (Fin k)).card := by simp
    _ ≤ ((A ∪ V) ∪ B).card := Finset.card_le_card hc
    _ ≤ (A ∪ V).card + B.card := Finset.card_union_le _ _
    _ ≤ (A.card+V.card) + B.card := Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (A.card+V.card) + ∑ j, ((H.holeHeavyHits p η j).card + (particleHeavyHits p η j).card) := by
      apply Nat.add_le_add_left
      apply (Finset.card_biUnion_le).trans
      exact Finset.sum_le_sum (fun j _ => Finset.card_union_le _ _)

theorem fewGood_cover (H : G.Holes h) (hH : H.Feasible)
    (p : Fin k → G.Slot × G.Slot) (η : ℝ)
    (he : ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2) :
    (k : ℝ)/4 ≤ ((sharingCoverage G.vertexShares H.endpointData p).card : ℝ) ∨
      ∃ j, (k : ℝ)/(8*G.b) ≤ ((H.holeHeavyHits p η j).card : ℝ) ∨
        (k : ℝ)/(8*G.b) ≤ ((particleHeavyHits p η j).card : ℝ) := by
  have hb : 0 < (G.b : ℝ) := by exact_mod_cast G.positive
  by_contra hf
  push Not at hf
  have hc : (k : ℝ) ≤ (H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card +
      (sharingCoverage G.vertexShares H.endpointData p).card +
      ∑ j, (((H.holeHeavyHits p η j).card : ℝ) + (particleHeavyHits p η j).card) := by
    exact_mod_cast H.card_covered_by_good_and_bad hH p η
  have hsum : (∑ j, (((H.holeHeavyHits p η j).card : ℝ) + (particleHeavyHits p η j).card)) ≤
      (G.b : ℝ)*((k : ℝ)/(4*G.b)) := by
    calc
      _ ≤ ∑ _j : Fin G.b, (k : ℝ)/(4*G.b) := by
        apply Finset.sum_le_sum
        intro j _
        have h1 := (hf.2 j).1
        have h2 := (hf.2 j).2
        have hid : (k : ℝ)/(4*G.b) = 2*((k : ℝ)/(8*G.b)) := by ring
        rw [hid]
        linarith
      _ = _ := by simp
  have hid : (G.b : ℝ)*((k : ℝ)/(4*G.b)) = k/4 := by field_simp
  rw [hid] at hsum
  linarith [hf.1]

/- Source04:eq12 prior to choosing absolute parameters and absorbing
subpolynomial factors. There is no conditioning on a particle-selected line set. -/
theorem probability_fewGood_le (H : G.Holes h) (hH : H.Feasible) {η : ℝ} (hη : 0 < η)
    (hh : 2*h/((G.size : ℝ)*η) ≤ 1) (hk : 2*k/((G.size : ℝ)*η) ≤ 1)
    (hv : ((k+h : ℕ) : ℝ)*G.vertexSharingRate ≤ 1) :
    Coverage.probability G.endpointWeight (fun p : Fin k → G.Slot × G.Slot =>
      ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2) ≤
      (2 : ℝ)^k * (((k+h : ℕ) : ℝ)*G.vertexSharingRate)^((k : ℝ)/8) +
      ∑ j : Fin G.b, ((2 : ℝ)^k * (2*h/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b)) +
        ((Fintype.card (G.Line j)+1 : ℕ) : ℝ)^⌊2*k/(((2^G.bits j : ℕ) : ℝ)*η)⌋₊ *
          (2 : ℝ)^k * (2*k/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b))) := by
  let V := fun p : Fin k → G.Slot × G.Slot =>
    (k : ℝ)/4 ≤ ((sharingCoverage G.vertexShares H.endpointData p).card : ℝ)
  let B := fun (j : Fin G.b) (p : Fin k → G.Slot × G.Slot) =>
    (k : ℝ)/(8*G.b) ≤ ((H.holeHeavyHits p η j).card : ℝ) ∨
      (k : ℝ)/(8*G.b) ≤ ((particleHeavyHits p η j).card : ℝ)
  have hu := probability_coverage_le_real (I := Fin k) G.vertexShares G.vertexShares_symm
    H.endpointData G.endpointWeight G.endpointWeight_nonneg G.endpointWeight_total
    G.vertexSharingRate G.vertexSharingRate_nonneg G.probability_vertexShares_le
    (by simpa using hv) ((k : ℝ)/4) (by positivity)
  have hV : Coverage.probability G.endpointWeight V ≤
      (2 : ℝ)^k * (((k+h : ℕ) : ℝ)*G.vertexSharingRate)^((k : ℝ)/8) := by
    simpa only [V, Fintype.card_fin, div_div, show (4:ℝ)*2=8 by norm_num] using hu
  have hB (j : Fin G.b) : Coverage.probability G.endpointWeight (B j) ≤
      (2 : ℝ)^k * (2*h/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b)) +
        ((Fintype.card (G.Line j)+1 : ℕ) : ℝ)^⌊2*k/(((2^G.bits j : ℕ) : ℝ)*η)⌋₊ *
          (2 : ℝ)^k * (2*k/((G.size : ℝ)*η))^((k : ℝ)/(8*G.b)) := by
    apply (probability_or_le G.endpointWeight G.endpointWeight_nonneg _ _).trans
    exact add_le_add (H.probability_holeHeavyHits_le hη hh j _ (by positivity))
      (probability_particleHeavyHits_le hη hk j _ (by positivity))
  calc
    _ ≤ Coverage.probability G.endpointWeight (fun p => V p ∨ ∃ j, B j p) :=
      probability_mono G.endpointWeight G.endpointWeight_nonneg (fun p hp => H.fewGood_cover hH p η hp)
    _ ≤ Coverage.probability G.endpointWeight V +
        Coverage.probability G.endpointWeight (fun p => ∃ j, B j p) :=
      probability_or_le G.endpointWeight G.endpointWeight_nonneg _ _
    _ ≤ Coverage.probability G.endpointWeight V +
        ∑ j, Coverage.probability G.endpointWeight (B j) :=
      add_le_add le_rfl (probability_exists_le G.endpointWeight G.endpointWeight_nonneg B)
    _ ≤ _ := add_le_add hV (Finset.sum_le_sum (fun j _ => hB j))
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

/- An explicit absolute prefactor used before asymptotic absorption. -/
theorem placementHSsq_uniform_le_fewGood (H : G.Holes h) {η : ℝ}
    (hη : 0 ≤ η) (hηsmall : η ≤ 1/8) :
    H.placementHSsq (k := k) (fun _ => FiniteLaw.uniform _) ≤
      (uniformSparsePrefactor G h k)^2 *
        (η^((k : ℝ)/2) + Coverage.probability G.endpointWeight
          (fun p : Fin k → G.Slot × G.Slot =>
            ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2)) := by
  let M := uniformSparsePrefactor G h k
  let Bad := fun p : Fin k → G.Slot × G.Slot =>
    ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ) < k/2
  have hM : 0 ≤ M := by dsimp [M, uniformSparsePrefactor]; positivity
  have hη1 : η ≤ 1 := by linarith
  have hsum : ∑ p : Fin k → G.Slot × G.Slot, Coverage.productMass G.endpointWeight p = 1 := by
    unfold Coverage.productMass
    rw [← Fintype.prod_sum]
    simp only [G.endpointWeight_total, Finset.prod_const_one]
  rw [H.placementHSsq_eq_full]
  calc
    _ ≤ ∑ p : Fin k → G.Slot × G.Slot,
        Coverage.productMass G.endpointWeight p * (M^2 *
          (η^((k : ℝ)/2) + if Bad p then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _
        (Coverage.productMass_nonneg G.endpointWeight G.endpointWeight_nonneg p)
      by_cases hp : H.ValidInput (fun i => (p i).1) ∧ H.ValidOutput (fun i => (p i).2)
      · rw [ite_eq_left hp]
        have he := H.scaled_placementKernel_good_bound (fun i => (p i).1) (fun i => (p i).2)
          hp.1 hη hηsmall
        change |(G.size : ℝ)^k * H.placementKernel _ _ _| ≤ M *
          η^(((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ)/2) at he
        have hpow : η^(((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ)/2) ≤ 1 :=
          Real.rpow_le_one hη hη1 (by positivity)
        by_cases hb : Bad p
        · rw [ite_eq_left hb]
          have hf : |(G.size : ℝ)^k * H.placementKernel _ _ _| ≤ M :=
            he.trans (mul_le_of_le_one_right hM hpow)
          have hsq := (sq_le_sq₀ (abs_nonneg _) hM).mpr hf
          rw [sq_abs] at hsq
          have he0 := Real.rpow_nonneg hη ((k : ℝ)/2)
          nlinarith [sq_nonneg M]
        · rw [ite_eq_right hb, add_zero]
          have hc : (k : ℝ)/4 ≤ ((H.goodSet (fun i => (p i).1) (fun i => (p i).2) η).card : ℝ)/2 := by
            dsimp [Bad] at hb
            linarith
          have hmono := Real.rpow_le_rpow_of_exponent_ge' hη hη1 (by positivity) hc
          have hf := he.trans (mul_le_mul_of_nonneg_left hmono hM)
          have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg hM (Real.rpow_nonneg hη _))).mpr hf
          simp only [sq_abs, mul_pow] at hsq
          have hid : (η^((k : ℝ)/4))^2 = η^((k : ℝ)/2) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
            congr 1
            ring
          simpa only [mul_pow, hid] using hsq
      · rw [ite_eq_right hp]
        positivity
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib]
      rw [← Finset.sum_mul, hsum, one_mul]
      rw [Coverage.probability, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      split_ifs <;> ring
end CoordinateSweeps.Grid.Holes

/- Required top-placement compression for the conditional main. The top space
is the annihilator of all functions depending on a proper set of coordinates.
This is the exact top level used in source04 around eq7. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ}

theorem extraProbability_dependsOn (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (A : Finset (Fin k))
    (x : H.InputPlacements k) :
    Placement.DependsOn (fun y : H.OutputPlacements k => y.val) A
      (fun y => (H.extraProbability x.val y.val A μ : ℂ)) := by
  intro y y' hy
  apply congrArg Complex.ofReal
  rw [H.extraProbability_eq_conditionalEndpoint, H.extraProbability_eq_conditionalEndpoint]
  have he (ω : G.Choices) : G.endpointEvent x.val y.val A ω ↔ G.endpointEvent x.val y'.val A ω := by
    constructor <;> intro hw i hi
    · exact (hw i hi).trans (hy i hi)
    · exact (hw i hi).trans (hy i hi).symm
  simp only [conditionalEndpointProbability, he]

theorem placementHSsq_eq_subtype (H : G.Holes h)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    H.placementHSsq (k := k) μ =
      ∑ x : H.InputPlacements k, ∑ y : H.OutputPlacements k,
        ‖(H.placementKernel x.val y.val μ : ℂ)‖^2 := by
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold placementHSsq
  symm
  rw [sum_subtype_eq_sum_ite_of_iff (p := H.ValidInput) (q := H.ValidInput)
    (fun x : Fin k → G.Slot => Iff.rfl)
    (fun x => ∑ y : H.OutputPlacements k, H.placementKernel x y.val μ ^ 2)]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx
  · rw [sum_subtype_eq_sum_ite_of_iff (p := H.ValidOutput) (q := H.ValidOutput)
      (fun y : Fin k → G.Slot => Iff.rfl) (fun y => H.placementKernel x y μ ^ 2)]
    apply Finset.sum_congr rfl
    intro y _
    simp only [hx, true_and]
  · apply Eq.symm
    simp only [hx, false_and, ite_false, Finset.sum_const_zero]

/- Exact top-placement restriction of the ACTUAL conditioned sweep, bounded
by the already proved path-weight Q counting norm. No representation-theoretic
conclusion is inserted as a hypothesis. -/
end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_SparseDimension
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.Grid.Holes
open PlacementOccurrence Placement
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma outputPlacementEquiv_apply (hf : H.Feasible) (y : Fin k ↪ H.FreeAt 0) (i : Fin k) :
    (H.outputPlacementEquiv hf y).val i=G.sweep (H.reference hf) (y i).val := rfl

lemma residualFree_apply (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) (x : H.FreeAt 0) :
    (H.residualFree hf ω x).val=(G.sweep (H.reference hf))⁻¹ (G.sweep ω.val x.val) := rfl

lemma endpointEvent_residualFree (hf : H.Feasible) (x y : Fin k ↪ H.FreeAt 0)
    (ω : {ω : G.Choices // H.Compatible ω}) :
    G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω.val ↔
      H.residualFree hf ω • x=y := by
  constructor
  · intro he
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    change (H.residualFree hf ω (x i)).val=(y i).val
    rw [H.residualFree_apply]
    apply (Equiv.symm_apply_eq (G.sweep (H.reference hf))).mpr
    exact he i (Finset.mem_univ _)
  · intro he i hi
    have hh := congrArg (fun x : Fin k ↪ H.FreeAt 0 => (x i).val) he
    change (H.residualFree hf ω (x i)).val=(y i).val at hh
    rw [H.residualFree_apply] at hh
    exact (Equiv.symm_apply_eq (G.sweep (H.reference hf))).mp hh

lemma extraProbability_eq_residual_sum (hf : H.Feasible) (x y : Fin k ↪ H.FreeAt 0)
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    H.extraProbability (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ
      (fun j => lineLaw (G.bits j) z hz hz') =
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        if H.residualFree hf ω • x=y then G.choiceWeight z ω.val/H.probability z else 0 := by
  rw [H.extraProbability_eq_conditionalEndpoint,conditionalEndpointProbability,H.lineMass_hole_normalizer hz hz']
  have hn : (∑ ω : G.Choices, if H.Compatible ω ∧
      G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω then
        G.productLineMass (fun j => lineLaw (G.bits j) z hz hz') ω else 0)=
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        if H.residualFree hf ω • x=y then G.choiceWeight z ω.val else 0 := by
    symm
    calc
      _ = ∑ ω : {ω : G.Choices // H.Compatible ω},
          if G.endpointEvent (H.inputPlacementEquiv x).val
            (H.outputPlacementEquiv hf y).val Finset.univ ω.val then G.choiceWeight z ω.val else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [H.endpointEvent_residualFree hf]
        split_ifs <;> rfl
      _ = _ := by
        rw [sum_subtype_eq_sum_ite_of_iff (fun _ => Iff.rfl)
      (fun ω : G.Choices => if G.endpointEvent (H.inputPlacementEquiv x).val
        (H.outputPlacementEquiv hf y).val Finset.univ ω then G.choiceWeight z ω else 0)]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> try rfl
        all_goals simp_all
  rw [hn,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

/- Partial endpoint matrix written on a single placement set using the
reference sweep; every variable is a literal conditional path probability. -/

lemma referencePartial_depends (hf : H.Feasible)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (A : Finset (Fin k)) (x : Fin k ↪ H.FreeAt 0) :
    Placement.DependsOn (fun y : Fin k ↪ H.FreeAt 0 => y) A
      (fun y => (H.referencePartial hf μ A x y : ℂ)) := by
  intro y y' hy
  apply H.extraProbability_dependsOn μ A (H.inputPlacementEquiv x)
  intro i hi
  simp only [outputPlacementEquiv_apply,hy i hi]

lemma referencePartial_full (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    (show Matrix (Fin k ↪ H.FreeAt 0) (Fin k ↪ H.FreeAt 0) ℂ from fun x y =>
      (H.referencePartial hf (fun j => lineLaw (G.bits j) z hz hz') Finset.univ x y : ℂ))=
        ∑ ω : {ω : G.Choices // H.Compatible ω},
          ((G.choiceWeight z ω.val/H.probability z : ℝ) : ℂ) •
            actionMatrix (X := Fin k ↪ H.FreeAt 0) (H.residualFree hf ω)⁻¹ := by
  ext x y
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,actionMatrix_entry,inv_inv]
  rw [referencePartial,H.extraProbability_eq_residual_sum hf x y hz hz',Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> simp

lemma referenceAlternating_entry (hf : H.Feasible)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) (x y : Fin k ↪ H.FreeAt 0) :
    alternatingKernel (G.size : ℝ) (H.referencePartial hf μ) x y=
      (H.placementKernel (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val μ : ℂ) := by
  simp only [alternatingKernel,referencePartial,placementKernel,Fintype.card_fin]

lemma referenceAlternating_hs (hf : H.Feasible)
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    (∑ x : Fin k ↪ H.FreeAt 0, ∑ y : Fin k ↪ H.FreeAt 0,
      ‖alternatingKernel (G.size : ℝ) (H.referencePartial hf μ) x y‖^2)=H.placementHSsq (k := k) μ := by
  rw [H.placementHSsq_eq_subtype]
  simp only [referenceAlternating_entry]
  apply Fintype.sum_equiv H.inputPlacementEquiv
  intro x
  exact (H.outputPlacementEquiv hf).sum_comp
    (fun y => ‖(H.placementKernel (H.inputPlacementEquiv x).val y.val μ : ℂ)‖^2)

/- The missing attachment of source04:eq7 to the faithful conditional
irreducible average, not merely an abstract stochastic matrix. -/
theorem conditional_norm_le_placementHS (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset (H.FreeAt 0), A.card < k → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm (H.FreeAt 0), (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤
      Real.sqrt (H.placementHSsq (k := k) (fun j => lineLaw (G.bits j) z hz hz')) := by
  have hm := first_level_norm_le ρ u hu x₀ hfixed (by simpa only [Fintype.card_fin] using hnof)
    (fun ω : {ω : G.Choices // H.Compatible ω} => ((G.choiceWeight z ω.val/H.probability z : ℝ) : ℂ))
    (fun ω => (H.residualFree hf ω)⁻¹) (G.size : ℝ) (by unfold Grid.size; positivity)
    (H.referencePartial hf (fun j => lineLaw (G.bits j) z hz hz'))
    (H.referencePartial_depends hf _) (H.referencePartial_full hf hz hz')
  have he : (∑ ω : {ω : G.Choices // H.Compatible ω},
      ((G.choiceWeight z ω.val/H.probability z : ℝ):ℂ) • ρ.matrix (H.residualFree hf ω)⁻¹)=
      (H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)).conjTranspose := by
    rw [H.conditionalAverage_eq_sum,Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro ω _
    rw [Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal]
    exact congrArg (fun M => ((G.choiceWeight z ω.val/H.probability z : ℝ):ℂ) • M)
      (ρ.matrix_inv (H.residualFree hf ω))
  rw [he] at hm
  change ‖(H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)).conjTranspose‖ ≤ _ at hm
  rw [Matrix.l2_opNorm_conjTranspose] at hm
  apply hm.trans
  have hh := Placement.matrix_l2_norm_le_hs (alternatingKernel (G.size : ℝ)
      (H.referencePartial (k := k) hf (fun j => lineLaw (G.bits j) z hz hz')))
  rw [H.referenceAlternating_hs] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  rfl
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
-- Archived complete binary-sign support, reused without a new-result claim.
/- The real-valued sign character, not a replacement for the permutation. -/

theorem boolSwitch_apply (b x : Bool) : boolSwitch b x = Bool.xor x b := by
  cases b <;> cases x <;> simp [boolSwitch]

theorem sign_boolSwitch (b : Bool) : realSign (boolSwitch b) = if b then -1 else 1 := by
  cases b <;> simp [boolSwitch, realSign]

theorem pairSwitch_eq_prod {L : Type*} (bits : L → Bool) :
    pairSwitch bits = Equiv.prodCongrLeft (fun l => boolSwitch (bits l)) := by
  apply Equiv.ext
  rintro ⟨b,l⟩
  change (Bool.xor b (bits l), l) = (boolSwitch (bits l) b, l)
  rw [boolSwitch_apply]

theorem sign_pairSwitch {L : Type*} [Fintype L] (bits : L → Bool) :
    realSign (pairSwitch bits) = ∏ l, (if bits l then (-1 : ℝ) else 1) := by
  rw [pairSwitch_eq_prod]
  change (((Equiv.Perm.sign (Equiv.prodCongrLeft (fun l => boolSwitch (bits l)))) : ℤ) : ℝ) = _
  rw [Equiv.Perm.sign_prodCongrLeft]
  change (((Units.coeHom ℤ) (∏ l, Equiv.Perm.sign (boolSwitch (bits l)))) : ℝ) = _
  rw [map_prod, Int.cast_prod]
  apply Finset.prod_congr rfl
  intro l _
  exact sign_boolSwitch (bits l)

theorem sign_binaryLayer {d : ℕ} (j : Fin d)
    (bits : ({k : Fin d // k ≠ j} → Bool) → Bool) :
    realSign (binaryLayer j bits) = realSign (pairSwitch bits) := by
  change (((Equiv.Perm.sign (_)) : ℤ) : ℝ) = _
  rw [binaryLayer, Equiv.Perm.sign_trans_trans]
  simp [realSign]

theorem sign_binarySweep (d : ℕ) (bits : BinaryChoices d) :
    realSign (binarySweep d bits) = ∏ j, realSign (binaryLayer j (bits j)) := by
  unfold binarySweep orderedProduct
  rw [map_list_prod]
  simp [List.map_reverse, List.map_ofFn, List.prod_reverse, List.prod_ofFn]

theorem sum_sign_binarySweep {d : ℕ} (hd : 0 < d) :
    (∑ bits : BinaryChoices d, realSign (binarySweep d bits)) = 0 := by
  simp_rw [sign_binarySweep, sign_binaryLayer]
  change (∑ bits : BinaryChoices d, ∏ j : Fin d,
    realSign (pairSwitch (bits j))) = 0
  have hs : ∀ (j : Fin d) (b : ({k : Fin d // k ≠ j} → Bool) → Bool),
      realSign (pairSwitch b) = ∏ l, if b l then (-1 : ℝ) else 1 := by
    intro j b
    convert sign_pairSwitch b using 1
    all_goals try with_reducible_and_instances rfl
    congr 2
    exact Subsingleton.elim _ _
  simp_rw [hs]
  rw [← Fintype.prod_sum (fun j : Fin d =>
    fun b : ({k : Fin d // k ≠ j} → Bool) → Bool =>
      ∏ l, if b l then (-1 : ℝ) else 1)]
  apply Finset.prod_eq_zero (i := (⟨0,hd⟩ : Fin d)) (Finset.mem_univ _)
  rw [← Fintype.prod_sum (fun (_ : ({k : Fin d // k ≠ (⟨0,hd⟩ : Fin d)} → Bool))
    (b : Bool) => if b then (-1 : ℝ) else 1)]
  simp

end CoordinateSweeps

namespace CoordinateSweeps
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

lemma signed_sum_zero_of_swap (w : Equiv.Perm Ω → ℝ) (P : Equiv.Perm Ω → Prop)
    (a b : Ω) (hab : a ≠ b)
    (hw : ∀ σ, w (Equiv.swap a b*σ)=w σ)
    (hP : ∀ σ, P (Equiv.swap a b*σ) ↔ P σ) :
    (∑ σ : Equiv.Perm Ω, if P σ then w σ*realSign σ else 0)=0 := by
  classical
  have hs : realSign (Equiv.swap a b)=(-1:ℝ) := by
    simp [realSign,Equiv.Perm.sign_swap hab]
  have he := Equiv.sum_comp (Equiv.mulLeft (Equiv.swap a b))
    (fun σ : Equiv.Perm Ω => if P σ then w σ*realSign σ else 0)
  have hn : (∑ σ : Equiv.Perm Ω, if P (Equiv.swap a b*σ) then
      w (Equiv.swap a b*σ)*realSign (Equiv.swap a b*σ) else 0)=
      -(∑ σ : Equiv.Perm Ω, if P σ then w σ*realSign σ else 0) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hP,hw,map_mul,hs]
    split_ifs <;> ring
  change (∑ σ : Equiv.Perm Ω, if P (Equiv.swap a b*σ) then
    w (Equiv.swap a b*σ)*realSign (Equiv.swap a b*σ) else 0)=_ at he
  linarith [hn,he]

lemma sum_uniform_realSign [Nontrivial Ω] :
    (∑ σ : Equiv.Perm Ω, FiniteLaw.uniform _ σ*realSign σ)=0 := by
  obtain ⟨a,b,hab⟩ := exists_pair_ne Ω
  simpa only [↓reduceIte] using signed_sum_zero_of_swap (FiniteLaw.uniform _) (fun _ => True)
    a b hab (fun _ => rfl) (fun _ => Iff.rfl)

omit [DecidableEq Ω] in
lemma sum_map_mul (μ : FiniteLaw Ω) {X : Type*} [Fintype X] (f : Ω → X) (v : X → ℝ) :
    (∑ y : X, (μ.map f) y*v y)=∑ x : Ω, μ x*v (f x) := by
  simp only [FiniteLaw.map_apply,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  simp [ite_mul]

lemma sum_binary_realSign {d : ℕ} (hd : 0 < d) :
    (∑ σ : Equiv.Perm (Cube d), binaryLaw d σ*realSign σ)=0 := by
  rw [binaryLaw,sum_map_mul]
  simp only [FiniteLaw.uniform_apply,← Finset.mul_sum,sum_sign_binarySweep hd,mul_zero]

lemma sum_lineLaw_realSign {d : ℕ} (hd : 0 < d) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) :
    (∑ σ : Equiv.Perm (Cube d), lineLaw d z hz hz' σ*realSign σ)=0 := by
  let : NeZero d := ⟨hd.ne'⟩
  change (∑ σ : Equiv.Perm (Cube d), ((1-z)*FiniteLaw.uniform _ σ+z*binaryLaw d σ)*realSign σ)=0
  simp only [add_mul,mul_assoc,Finset.sum_add_distrib,← Finset.mul_sum,
    sum_uniform_realSign,sum_binary_realSign hd,mul_zero,add_zero]

namespace Grid
lemma realSign_fiberPerm {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (g : B → Equiv.Perm A) : realSign (fiberPerm g)=∏ b, realSign (g b) := by
  have he : fiberPerm g=Equiv.prodCongrLeft g := rfl
  rw [he]
  change (((Equiv.Perm.sign (Equiv.prodCongrLeft g) : ℤ):ℝ))=_
  rw [Equiv.Perm.sign_prodCongrLeft]
  change (((Units.coeHom ℤ) (∏ b, Equiv.Perm.sign (g b))):ℝ)=_
  rw [map_prod,Int.cast_prod]
  rfl

lemma realSign_stage (G : Grid) (ω : G.Choices) (j : Fin G.b) :
    realSign (G.stage ω j)=∏ L, realSign (ω j L) := by
  have he : realSign (G.stage ω j)=realSign (fiberPerm (ω j)) := by
    change (((Equiv.Perm.sign (_)) : ℤ) : ℝ) = _
    rw [stage,Equiv.Perm.sign_trans_trans]
    simp [realSign]
  exact he.trans (realSign_fiberPerm (ω j))

lemma realSign_sweep (G : Grid) (ω : G.Choices) :
    realSign (G.sweep ω)=∏ j, ∏ L, realSign (ω j L) := by
  unfold sweep boundary
  have ht := List.take_length (l := List.ofFn (G.stage ω))
  simp only [List.length_ofFn] at ht
  rw [ht]
  rw [map_list_prod]
  simp only [List.map_reverse,List.map_ofFn,List.prod_reverse,List.prod_ofFn,Function.comp_apply,realSign_stage]

lemma signed_line_factorization (G : Grid)
    (μ : ∀ j : Fin G.b, FiniteLaw (Equiv.Perm (Cube (G.bits j))))
    (P : ∀ j : Fin G.b, G.Line j → Equiv.Perm (Cube (G.bits j)) → Prop) :
    (∑ ω : G.Choices, if ∀ j L, P j L (ω j L) then G.productLineMass μ ω*realSign (G.sweep ω) else 0)=
      ∏ j, ∏ L, ∑ σ, if P j L σ then μ j σ*realSign σ else 0 := by
  simp only [realSign_sweep,productLineMass,← Finset.prod_mul_distrib]
  calc
    _ = ∏ j, ∑ ω : G.Line j → Equiv.Perm (Cube (G.bits j)),
        if ∀ L, P j L (ω L) then ∏ L, μ j (ω L)*realSign (ω L) else 0 := by
      convert sum_prod_ite_all
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∏ L, μ j (ω L)*realSign (ω L))
        (fun j (ω : G.Line j → Equiv.Perm (Cube (G.bits j))) => ∀ L, P j L (ω L)) using 1 <;>
          congr!
    _ = _ := by
      apply Finset.prod_congr rfl
      intro j _
      exact sum_prod_ite_all (fun _ σ => μ j σ*realSign σ) (P j)
end Grid
end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ} (H : G.Holes h)

lemma signed_endpoint_factorization (x y : Fin k → G.Slot) (A : Finset (Fin k))
    (μ : ∀ j, FiniteLaw (Equiv.Perm (Cube (G.bits j)))) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y A ω then
      G.productLineMass μ ω*realSign (G.sweep ω) else 0)=
      ∏ j, ∏ L, ∑ σ, if H.jointLineEvent x y A j L σ then μ j σ*realSign σ else 0 := by
  have he (ω : G.Choices) : H.Compatible ω ∧ G.endpointEvent x y A ω ↔
      ∀ j L, H.jointLineEvent x y A j L (ω j L) := by
    rw [H.compatible_iff_lines,G.endpointEvent_iff_lines]
    exact ⟨fun hh j L => ⟨hh.1 j L,hh.2 j L⟩,
      fun hh => ⟨fun j L => (hh j L).1,fun j L => (hh j L).2⟩⟩
  simp_rw [he]
  exact G.signed_line_factorization μ (H.jointLineEvent x y A)

lemma signed_endpoint_zero_of_unused (x y : Fin k → G.Slot) (A : Finset (Fin k))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1) (j : Fin G.b) (hj : 0 < G.bits j)
    (L : G.Line j) (hholes : ∀ i : Fin h, ¬ H.OnLine j L i)
    (hpaths : ∀ i ∈ A, G.pathLine (x i) (y i) j ≠ L) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y A ω then
      G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0 := by
  change (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y A ω then
    G.productLineMass (fun j => lineLaw (G.bits j) z hz hz') ω*realSign (G.sweep ω) else 0)=0
  rw [H.signed_endpoint_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ L)
  have he (σ : Equiv.Perm (Cube (G.bits j))) : H.jointLineEvent x y A j L σ := by
    constructor
    · intro i
      exact False.elim (hholes i.val i.property)
    · intro i hi hL
      exact False.elim (hpaths i hi hL)
  simp only [ite_eq_left (he _)]
  exact sum_lineLaw_realSign hj hz hz'

lemma exists_unused_line (x y : Fin k → G.Slot) (j : Fin G.b)
    (hj : h+k < Fintype.card (G.Line j)) :
    ∃ L : G.Line j, (∀ i : Fin h, ¬ H.OnLine j L i) ∧
      ∀ i : Fin k, G.pathLine (x i) (y i) j ≠ L := by
  let f : Fin h ⊕ Fin k → G.Line j := Sum.elim
    (fun i => fun t => H.path i j.castSucc t) (fun i => G.pathLine (x i) (y i) j)
  have hn : ¬ Function.Surjective f := by
    intro hs
    have hc := Fintype.card_le_of_surjective f hs
    simp only [Fintype.card_sum,Fintype.card_fin] at hc
    omega
  obtain ⟨L,hL⟩ := not_forall.mp hn
  refine ⟨L,?_,?_⟩
  · intro i hi
    exact hL ⟨Sum.inl i,hi⟩
  · intro i hi
    exact hL ⟨Sum.inr i,hi⟩

/- Literal many-coordinate column cancellation; no complex conditioning. -/
theorem signed_endpoint_zero_many (x y : Fin k → G.Slot) {z : ℝ}
    (hz : 0 ≤ z) (hz' : z ≤ 1) (j : Fin G.b) (hj : 0 < G.bits j)
    (hsize : h+k < Fintype.card (G.Line j)) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
      G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0 := by
  obtain ⟨L,hH,hP⟩ := H.exists_unused_line x y j hsize
  exact H.signed_endpoint_zero_of_unused x y Finset.univ hz hz' j hj L hH (fun i _ => hP i)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
/- More than one unassigned slot per line on average forces two free slots
on a common line. Assignments need not be injective for this counting step. -/
lemma exists_two_unassigned {I U V : Type*} [Fintype I] [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (f : I → U × V)
    (hh : Fintype.card I+Fintype.card V < Fintype.card (U × V)) :
    ∃ a b : U, ∃ v : V, a ≠ b ∧ (∀ i, f i ≠ (a,v)) ∧ ∀ i, f i ≠ (b,v) := by
  classical
  let S := (Finset.univ : Finset (U × V)) \ Finset.univ.image f
  have hc : Fintype.card V < S.card := by
    dsimp [S]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ]
    have hi : (Finset.univ.image f).card ≤ Fintype.card I := by
      simpa using Finset.card_image_le (s := Finset.univ) (f := f)
    omega
  have hn : ¬ Function.Injective (fun u : S => u.val.2) := by
    intro hi
    have ht := Fintype.card_le_of_injective _ hi
    exact (not_le.mpr hc) (by simpa only [Fintype.card_coe] using ht)
  simp only [Function.Injective] at hn
  push Not at hn
  obtain ⟨a,b,hv,hab⟩ := hn
  refine ⟨a.val.1,b.val.1,a.val.2,?_,?_,?_⟩
  · intro he
    apply hab
    exact Subtype.ext (Prod.ext he hv)
  · intro i hi
    have ha := (Finset.mem_sdiff.mp a.property).2
    exact ha (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi⟩)
  · intro i hi
    have hb := (Finset.mem_sdiff.mp b.property).2
    apply hb
    refine Finset.mem_image.mpr ⟨i,Finset.mem_univ _,?_⟩
    exact hi.trans (Prod.ext rfl hv)
end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
lemma uniform_signed_joint_zero (x y : Fin k → G.Slot) (j : Fin G.b)
    (L : G.Line j) (a b : Cube (G.bits j)) (hab : a ≠ b)
    (haH : ∀ i : Fin h, H.OnLine j L i → H.path i j.succ j ≠ a)
    (hbH : ∀ i : Fin h, H.OnLine j L i → H.path i j.succ j ≠ b)
    (haP : ∀ i, G.pathLine (x i) (y i) j=L → y i j ≠ a)
    (hbP : ∀ i, G.pathLine (x i) (y i) j=L → y i j ≠ b) :
    (∑ σ, if H.jointLineEvent x y Finset.univ j L σ then
      FiniteLaw.uniform _ σ*realSign σ else 0)=0 := by
  apply signed_sum_zero_of_swap (FiniteLaw.uniform _) _ a b hab (fun _ => rfl)
  have he (u v : Cube (G.bits j)) (hv : v ≠ a) (hv' : v ≠ b) (σ : Equiv.Perm (Cube (G.bits j))) :
      (Equiv.swap a b*σ) u=v ↔ σ u=v := by
    have hs := Equiv.swap_apply_of_ne_of_ne hv hv'
    constructor
    · intro hh
      apply (Equiv.swap a b).injective
      exact hh.trans hs.symm
    · intro hh
      change Equiv.swap a b (σ u)=v
      rw [hh,hs]
  intro σ
  unfold jointLineEvent LineCompatible extraLineEvent
  constructor
  · intro hh
    constructor
    · intro i
      exact (he _ _ (haH i i.property) (hbH i i.property) σ).mp (hh.1 i)
    · intro i hi hL
      exact (he _ _ (haP i hL) (hbP i hL) σ).mp (hh.2 i hi hL)
  · intro hh
    constructor
    · intro i
      exact (he _ _ (haH i i.property) (hbH i i.property) σ).mpr (hh.1 i)
    · intro i hi hL
      exact (he _ _ (haP i hL) (hbP i hL) σ).mpr (hh.2 i hi hL)

/- Exact zero at the real uniform law, including bounded coordinate counts. -/
theorem signed_endpoint_zero_uniform (x y : Fin k → G.Slot) (j : Fin G.b)
    (hsize : h+k+Fintype.card (G.Line j) < G.size) :
    (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
      G.choiceWeight 0 ω*realSign (G.sweep ω) else 0)=0 := by
  let f : Fin h ⊕ Fin k → Cube (G.bits j) × G.Line j := Sum.elim
    (fun i => (H.path i j.succ j,fun t => H.path i j.castSucc t))
    (fun i => (y i j,G.pathLine (x i) (y i) j))
  have hf : Fintype.card (Fin h ⊕ Fin k)+Fintype.card (G.Line j) <
      Fintype.card (Cube (G.bits j) × G.Line j) := by
    rw [← Fintype.card_congr (Equiv.piSplitAt j (fun t => Cube (G.bits t))),G.card_slot]
    simpa using hsize
  obtain ⟨a,b,L,hab,ha,hb⟩ := exists_two_unassigned f hf
  have hmass : ∀ ω : G.Choices, G.choiceWeight 0 ω=
      G.productLineMass (fun j => FiniteLaw.uniform _) ω := by
    intro ω
    simp [choiceWeight,productLineMass]
  simp_rw [hmass]
  rw [H.signed_endpoint_factorization]
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  apply Finset.prod_eq_zero (Finset.mem_univ L)
  apply H.uniform_signed_joint_zero x y j L a b hab
  · intro i hL he
    exact ha (Sum.inl i) (Prod.ext he hL)
  · intro i hL he
    exact hb (Sum.inl i) (Prod.ext he hL)
  · intro i hL he
    exact ha (Sum.inr i) (Prod.ext he hL)
  · intro i hL he
    exact hb (Sum.inr i) (Prod.ext he hL)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.PlacementOccurrence
open scoped Matrix.Norms.L2Operator
variable {I Ω : Type*} [Fintype I] [DecidableEq I] [Fintype Ω] [DecidableEq Ω]
/- Vanishing on placements transfers to any actually occurring constituent.
No minimum-level condition is needed in the sign-zero branch. -/
omit [DecidableEq I] in
theorem average_zero_of_placement_zero (ρ : UnitaryIrrep (Equiv.Perm Ω))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : I ↪ Ω)
    (hfixed : ∀ g : Equiv.Perm Ω, (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    {W : Type*} [Fintype W] (w : W → ℂ) (g : W → Equiv.Perm Ω)
    (hz : (∑ a : W, w a • actionMatrix (X := I ↪ Ω) (g a))=0) :
    (∑ a : W, w a • ρ.matrix (g a))=0 := by
  let B : Matrix (Fin ρ.dimension) (I ↪ Ω) ℂ := synthesisMatrix ρ u x₀
  have hne : B ≠ 0 := synthesisMatrix_ne_zero ρ u hu x₀ (by
    intro σ hσ
    exact hfixed σ (fun i => congrArg (fun x : I ↪ Ω => x i) hσ))
  have hn := ρ.norm_le_compression (actionMatrix (X := I ↪ Ω)) actionMatrix_unitary B hne
    (synthesisMatrix_covariant ρ u x₀) (∑ a : W, w a • ρ.matrix (g a))
    (∑ a : W, w a • actionMatrix (X := I ↪ Ω) (g a)) (by
      rw [Matrix.sum_mul,Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Matrix.smul_mul,Matrix.mul_smul]
      congr 1
      exact ρ.adjoint_intertwines _ actionMatrix_unitary B (synthesisMatrix_covariant ρ u x₀) (g a))
  rw [hz,norm_zero] at hn
  exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
end CoordinateSweeps.PlacementOccurrence

namespace CoordinateSweeps.Grid.Holes
open SparseDimension UnitaryIrrep PlacementOccurrence
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
lemma realSign_freePerm (g : H.stabilizer) :
    realSign (H.stabilizerFreeEquiv g)=realSign g.val := by
  have he : Equiv.Perm.ofSubtype (H.stabilizerFreeEquiv g)=g.val := by
    apply Equiv.ext
    intro x
    by_cases hx : ∀ i, x ≠ H.path i 0
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
      rfl
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hx]
      push Not at hx
      obtain ⟨i,rfl⟩ := hx
      exact (g.property i).symm
  rw [← he]
  simp [realSign,Equiv.Perm.sign_ofSubtype]

lemma realSign_residualFree (hf : H.Feasible) (ω : {ω : G.Choices // H.Compatible ω}) :
    realSign (H.residualFree hf ω)=realSign (G.sweep (H.reference hf))⁻¹*realSign (G.sweep ω.val) := by
  rw [residualFree,H.realSign_freePerm]
  change realSign ((G.sweep (H.reference hf))⁻¹*G.sweep ω.val)=_
  rw [map_mul]

lemma signed_reference_entry_zero (hf : H.Feasible) (z : ℝ)
    (hzero : ∀ x y : Fin k → G.Slot,
      (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
        G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0)
    (x y : Fin k ↪ H.FreeAt 0) :
    (∑ ω : {ω : G.Choices // H.Compatible ω},
      if H.residualFree hf ω • x=y then
        (G.choiceWeight z ω.val/H.probability z)*realSign (H.residualFree hf ω) else 0)=0 := by
  have hz := hzero (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val
  have hs : (∑ ω : {ω : G.Choices // H.Compatible ω},
      if H.residualFree hf ω • x=y then G.choiceWeight z ω.val*realSign (G.sweep ω.val) else 0)=0 := by
    calc
      _ = ∑ ω : {ω : G.Choices // H.Compatible ω},
          if G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω.val then
            G.choiceWeight z ω.val*realSign (G.sweep ω.val) else 0 := by
        apply Finset.sum_congr rfl
        intro ω _
        rw [H.endpointEvent_residualFree]
        split_ifs <;> rfl
      _ = ∑ ω : G.Choices, if H.Compatible ω ∧
          G.endpointEvent (H.inputPlacementEquiv x).val (H.outputPlacementEquiv hf y).val Finset.univ ω then
            G.choiceWeight z ω*realSign (G.sweep ω) else 0 := by
        rw [sum_subtype_eq_sum_ite_of_iff (fun _ => Iff.rfl)
          (fun ω : G.Choices => if G.endpointEvent (H.inputPlacementEquiv x).val
            (H.outputPlacementEquiv hf y).val Finset.univ ω then
              G.choiceWeight z ω*realSign (G.sweep ω) else 0)]
        apply Finset.sum_congr rfl
        intro ω _
        split_ifs <;> simp_all
      _ = 0 := hz
  calc
    _ = (realSign (G.sweep (H.reference hf))⁻¹/H.probability z)*
        (∑ ω : {ω : G.Choices // H.Compatible ω}, if H.residualFree hf ω • x=y then
          G.choiceWeight z ω.val*realSign (G.sweep ω.val) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ω _
      rw [H.realSign_residualFree]
      split_ifs <;> ring
    _ = 0 := by rw [hs,mul_zero]

/- Column cancellation is now on the faithful conditional average, not just
on raw signed endpoint numerators. -/
theorem conditional_zero_of_signed_endpoints (hf : H.Feasible) (z : ℝ)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) →
      (SparseDimension.signTwist ρ.asRepresentation) g u=u)
    (hzero : ∀ x y : Fin k → G.Slot,
      (∑ ω : G.Choices, if H.Compatible ω ∧ G.endpointEvent x y Finset.univ ω then
        G.choiceWeight z ω*realSign (G.sweep ω) else 0)=0) :
    H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)=0 := by
  let w := fun ω : {ω : G.Choices // H.Compatible ω} =>
    (((G.choiceWeight z ω.val/H.probability z)*realSign (H.residualFree hf ω) : ℝ) : ℂ)
  have he : (∑ ω : {ω : G.Choices // H.Compatible ω},
      w ω • actionMatrix (X := Fin k ↪ H.FreeAt 0) ((H.residualFree hf ω)⁻¹))=0 := by
    ext x y
    simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,actionMatrix_entry,inv_inv,Matrix.zero_apply]
    have hs := H.signed_reference_entry_zero hf z hzero x y
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hs
    simpa only [Complex.ofReal_sum,Complex.ofReal_zero,apply_ite,mul_ite,mul_one,mul_zero] using hc
  have hh := average_zero_of_placement_zero ρ.signTwist u hu x₀
    (by intro g hg; rw [signTwist_rep]; exact hfixed g hg) w
    (fun ω => (H.residualFree hf ω)⁻¹) he
  have hid : (∑ ω : {ω : G.Choices // H.Compatible ω},
      w ω • ρ.signTwist.matrix ((H.residualFree hf ω)⁻¹))=
        (H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)).conjTranspose := by
    rw [H.conditionalAverage_eq_sum,Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro ω _
    change w ω • (signScalar ((H.residualFree hf ω)⁻¹) • ρ.matrix ((H.residualFree hf ω)⁻¹))=_
    rw [smul_smul,Matrix.conjTranspose_smul,Complex.star_def,Complex.conj_ofReal,ρ.matrix_inv]
    congr 1
    dsimp [w]
    rw [Complex.ofReal_mul]
    have hs : ((realSign (H.residualFree hf ω) : ℝ):ℂ)=signScalar (H.residualFree hf ω) := by
      simp [realSign,signScalar_apply]
    rw [hs,mul_assoc]
    change ((G.choiceWeight z ω.val/H.probability z : ℝ):ℂ)*
      (signScalar (H.residualFree hf ω)*signScalar ((H.residualFree hf ω)⁻¹))=_
    rw [← map_mul,mul_inv_cancel,map_one,mul_one]
  rw [hid] at hh
  have heq := congrArg Matrix.conjTranspose hh
  simp only [Matrix.conjTranspose_conjTranspose] at heq
  exact heq.trans (show (0 : Matrix (Fin ρ.dimension) (Fin ρ.dimension) ℂ).conjTranspose=0 from Matrix.conjTranspose_zero)
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
theorem conditional_column_zero_many (hf : H.Feasible) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0)
    (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) →
      (SparseDimension.signTwist ρ.asRepresentation) g u=u)
    (j : Fin G.b) (hj : 0 < G.bits j) (hsize : h+k < Fintype.card (G.Line j)) :
    H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)=0 :=
  H.conditional_zero_of_signed_endpoints hf z ρ u hu x₀ hfixed
    (fun x y => H.signed_endpoint_zero_many x y hz hz' j hj hsize)
theorem conditional_column_zero_uniform (hf : H.Feasible)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0)
    (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) →
      (SparseDimension.signTwist ρ.asRepresentation) g u=u)
    (j : Fin G.b) (hsize : h+k+Fintype.card (G.Line j) < G.size) :
    H.conditionalAverage hf 0 (ρ.pullback H.stabilizerFreeEquiv)=0 :=
  H.conditional_zero_of_signed_endpoints hf 0 ρ u hu x₀ hfixed
    (fun x y => H.signed_endpoint_zero_uniform x y j hsize)
end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_SparseBound
attribute [-instance] _root_.OAI.CoordinateSweeps.Grid.single_line_unique
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators
open MvPolynomial
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators
noncomputable section
open scoped BigOperators
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
universe u v
open scoped ComplexConjugate
noncomputable section
open scoped BigOperators
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators
open Filter Asymptotics
namespace CoordinateSweeps.SparseScalar
lemma pow_two_exp (k : ℕ) : (2:ℝ)^k=Real.exp ((k:ℝ)*Real.log 2) := by
  rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0:ℝ)<2)]
lemma exp_rpow (x y : ℝ) : (Real.exp x)^y=Real.exp (x*y) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
lemma rpow_exp (s x : ℝ) (hs : 0 < s) : s^x=Real.exp (x*Real.log s) := by
  rw [Real.rpow_def_of_pos hs,mul_comm]
lemma many_HS_bound (s t b h : ℝ) (k : ℕ) (hs : 1 < s) (ht : 0 ≤ t)
    (hts : t ≤ s^(-theta/2)) (hh : h ≤ K0*k)
    (hb : 0 ≤ b)
    (habsorb : 3*Real.log 2+2*b*(K0+1+Real.log 4) ≤ theta*Real.log s/8) :
    ((2:ℝ)^k*Real.exp (b*(h+k)+Real.log 4*k*b))^2 *
      ((2:ℝ)^k*t^((k:ℝ)/2)) ≤ s^(-theta*k/8) := by
  have hk : 0 ≤ (k:ℝ) := Nat.cast_nonneg _
  have hp := Real.rpow_le_rpow ht hts (by positivity : 0 ≤ (k:ℝ)/2)
  rw [rpow_exp s _ (by linarith),exp_rpow] at hp
  have he : b*(h+k)+Real.log 4*k*b ≤ b*(K0+1+Real.log 4)*k := by
    have hh' := mul_le_mul_of_nonneg_left hh hb
    nlinarith
  have he' := Real.exp_le_exp.mpr he
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ (2:ℝ)^k*Real.exp (b*(h+k)+Real.log 4*k*b))
    (mul_le_mul_of_nonneg_left he' (by positivity)) 2
  apply (mul_le_mul hpow (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity) (by positivity)).trans
  rw [pow_two_exp,← Real.exp_add,← Real.exp_nat_mul,← Real.exp_add,← Real.exp_add,rpow_exp s _ (by linarith)]
  apply Real.exp_le_exp.mpr
  have ha := mul_le_mul_of_nonneg_right habsorb hk
  push_cast
  nlinarith
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.SparseScalar
lemma prob_power_bound {s t E : ℝ} {k : ℕ} (hs : 1 < s) (ht : 0 ≤ t)
    (hts : t ≤ s^(-theta/2)) (hE : (k:ℝ)/(8*B0) ≤ E) :
    t^E ≤ Real.exp (-theta*k*Real.log s/(16*B0)) := by
  have hEp : 0 ≤ E := (by positivity : 0 ≤ (k:ℝ)/(8*B0)).trans hE
  have hh := Real.rpow_le_rpow ht hts hEp
  rw [rpow_exp s (-theta/2) (by linarith),exp_rpow] at hh
  apply hh.trans (Real.exp_le_exp.mpr ?_)
  have hp : 0 ≤ theta*Real.log s/2 := by
    have hl := Real.log_pos hs
    norm_num [theta]
    positivity
  have ha := mul_le_mul_of_nonneg_left hE hp
  norm_num [B0] at ha ⊢
  nlinarith

/- Scalar absorption of the literal coverage/occupancy union estimate. -/
lemma fewGood_bound {b k : ℕ} (hb : 1 ≤ b) (hB : b ≤ B0) (hk : 1 ≤ k)
    {s v u t : ℝ} (hs : 1 < s) (hv : 0 ≤ v) (hu : 0 ≤ u) (ht : 0 ≤ t)
    (hvs : v ≤ s^(-theta/2)) (hus : u ≤ s^(-theta/2)) (hts : t ≤ s^(-theta/2))
    (C : Fin b → ℝ) (hC0 : ∀ j, 0 ≤ C j)
    (hC : ∀ j, C j ≤ Real.exp (theta*k*Real.log s/(32*B0)))
    (habs : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log s) :
    (2:ℝ)^k*v^((k:ℝ)/8)+∑ j : Fin b,
      ((2:ℝ)^k*u^((k:ℝ)/(8*b))+C j*2^k*t^((k:ℝ)/(8*b))) ≤ s^(-xi*k) := by
  have hbpos : (0:ℝ)<b := by exact_mod_cast hb
  have hB' : (b:ℝ)≤B0 := by exact_mod_cast hB
  have hkpos : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)≤k := by positivity
  have hL := Real.log_pos hs
  have hE : (k:ℝ)/(8*B0) ≤ (k:ℝ)/(8*b) :=
    div_le_div_of_nonneg_left hk0 (by positivity) (by nlinarith)
  have hE' : (k:ℝ)/(8*B0) ≤ (k:ℝ)/8 :=
    div_le_div_of_nonneg_left hk0 (by norm_num) (by norm_num [B0])
  let D := Real.exp (-theta*k*Real.log s/(32*B0))
  have hD : 0 ≤ D := (Real.exp_pos _).le
  have hpow : Real.exp (-theta*k*Real.log s/(16*B0)) ≤ D := by
    apply Real.exp_le_exp.mpr
    dsimp [theta,B0]
    nlinarith [mul_nonneg hk0 hL.le]
  have hv' : v^((k:ℝ)/8) ≤ D := (prob_power_bound hs hv hvs hE').trans hpow
  have hu' : u^((k:ℝ)/(8*b)) ≤ D := (prob_power_bound hs hu hus hE).trans hpow
  have ht' := prob_power_bound hs ht hts hE
  have hc' (j : Fin b) : C j*t^((k:ℝ)/(8*b)) ≤ D := by
    apply (mul_le_mul (hC j) ht' (Real.rpow_nonneg ht _) ((hC0 j).trans (hC j))).trans
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    ring_nf
    exact le_rfl
  calc
    _ ≤ (2:ℝ)^k*D+∑ _j : Fin b, (2*(2:ℝ)^k*D) := by
      apply add_le_add (mul_le_mul_of_nonneg_left hv' (by positivity))
      apply Finset.sum_le_sum
      intro j _
      have h1 := mul_le_mul_of_nonneg_left hu' (by positivity : 0 ≤ (2:ℝ)^k)
      have h2 := mul_le_mul_of_nonneg_left (hc' j) (by positivity : 0 ≤ (2:ℝ)^k)
      nlinarith
    _ = (1+2*(b:ℝ))*(2:ℝ)^k*D := by simp; ring
    _ ≤ (1+2*(B0:ℝ))*(2:ℝ)^k*D := by gcongr
    _ = Real.exp (Real.log (1+2*(B0:ℝ))+(k:ℝ)*Real.log 2-theta*k*Real.log s/(32*B0)) := by
      rw [pow_two_exp,show 1+2*(B0:ℝ)=Real.exp (Real.log (1+2*(B0:ℝ))) by
        rw [Real.exp_log (by norm_num [B0])],← Real.exp_add,← Real.exp_add]
      simp only [Real.log_exp]
      congr 1
      ring
    _ ≤ s^(-xi*k) := by
      rw [rpow_exp _ _ (by linarith)]
      apply Real.exp_le_exp.mpr
      have ha := mul_le_mul_of_nonneg_right habs hk0
      have hlog : 0 ≤ Real.log (1+2*(B0:ℝ)) := Real.log_nonneg (by norm_num [B0])
      have hx := mul_le_mul_of_nonneg_right hkpos hlog
      norm_num [theta,xi,B0] at ha hx hlog ⊢
      nlinarith [mul_nonneg hk0 hL.le]
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.Grid
lemma size_pos (G : Grid) : 0 < G.size := by unfold size; positivity
lemma log_size (G : Grid) : Real.log G.size = ∑ j, (G.bits j : ℝ)*Real.log 2 := by
  simp only [size,Nat.cast_prod,Nat.cast_pow,Nat.cast_ofNat]
  rw [Real.log_prod (fun j _ => by positivity)]
  simp only [Real.log_pow]
lemma log_size_lower (G : Grid) {r : ℕ} (hG : G.Allowed r) :
    (G.b : ℝ)*((r : ℝ)*Real.log 2) ≤ Real.log G.size := by
  rw [G.log_size]
  calc
    _ = ∑ _ : Fin G.b, (r : ℝ)*Real.log 2 := by simp
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
      (by exact_mod_cast (hG j).1) (Real.log_nonneg (by norm_num)))
lemma log_size_upper (G : Grid) {r : ℕ} (hG : G.Allowed r) :
    Real.log G.size ≤ 2*(G.b : ℝ)*((r : ℝ)*Real.log 2) := by
  rw [G.log_size]
  calc
    _ ≤ ∑ _ : Fin G.b, (2*r : ℝ)*Real.log 2 := Finset.sum_le_sum (fun j _ =>
      mul_le_mul_of_nonneg_right (by exact_mod_cast (hG j).2) (Real.log_nonneg (by norm_num)))
    _ = _ := by simp; ring

end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid
open SparseScalar
lemma log_coordinate (G : Grid) (j : Fin G.b) :
    Real.log (2^G.bits j : ℝ)=(G.bits j:ℝ)*Real.log 2 := by rw [Real.log_pow]
lemma log_size_pos_of_allowed (G : Grid) {r : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r) :
    0 < Real.log G.size := by
  have hb : 0 < (G.b:ℝ) := by exact_mod_cast G.positive
  have hr' : 0 < (r:ℝ) := by exact_mod_cast hr
  exact lt_of_lt_of_le (by positivity : 0 < (G.b:ℝ)*((r:ℝ)*Real.log 2)) (G.log_size_lower hG)
lemma coordinate_log_many (G : Grid) {r : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r)
    (hb : B0 ≤ G.b) (j : Fin G.b) :
    Real.log (2^G.bits j : ℝ) ≤ (theta/4)*Real.log G.size := by
  rw [G.log_coordinate]
  have hbits : (G.bits j:ℝ) ≤ 2*r := by exact_mod_cast (hG j).2
  have hb' : (B0:ℝ)≤G.b := by exact_mod_cast hb
  have hr' : 0 ≤ (r:ℝ)*Real.log 2 := by positivity
  have h1 := mul_le_mul_of_nonneg_right hbits (by positivity : 0 ≤ Real.log 2)
  have h2 := mul_le_mul_of_nonneg_right hb' hr'
  have h3 := G.log_size_lower hG
  have hth : 0 ≤ theta/4 := by norm_num [theta]
  have h4 := mul_le_mul_of_nonneg_left h3 hth
  norm_num [theta,B0] at h2 h4 ⊢
  nlinarith
lemma coordinate_log_bounded (G : Grid) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (j : Fin G.b) :
    Real.log G.size/(2*(B0:ℝ)) ≤ Real.log (2^G.bits j : ℝ) := by
  rw [G.log_coordinate]
  have hb' : (G.b:ℝ)≤B0 := by exact_mod_cast hb
  have hr' : 0 ≤ (r:ℝ)*Real.log 2 := by positivity
  have hbits : (r:ℝ) ≤ G.bits j := by exact_mod_cast (hG j).1
  have h1 := mul_le_mul_of_nonneg_right hbits (by positivity : 0 ≤ Real.log 2)
  have h2 := mul_le_mul_of_nonneg_right hb' hr'
  have h3 := G.log_size_upper hG
  apply (div_le_iff₀ (by norm_num [B0] : 0 < 2*(B0:ℝ))).mpr
  norm_num [B0] at h2 ⊢
  nlinarith
lemma coordinate_size_many (G : Grid) {r : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r)
    (hb : B0 ≤ G.b) (j : Fin G.b) :
    (2^G.bits j:ℝ) ≤ (G.size:ℝ)^(theta/4) := by
  rw [rpow_exp _ _ (by exact_mod_cast G.size_pos)]
  rw [← Real.exp_log (by positivity : 0 < (2^G.bits j:ℝ))]
  exact Real.exp_le_exp.mpr (G.coordinate_log_many hr hG hb j)
lemma coordinate_size_bounded (G : Grid) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (j : Fin G.b) :
    (G.size:ℝ)^(1/(2*(B0:ℝ))) ≤ (2^G.bits j:ℝ) := by
  rw [rpow_exp _ _ (by exact_mod_cast G.size_pos)]
  rw [← Real.exp_log (by positivity : 0 < (2^G.bits j:ℝ))]
  apply Real.exp_le_exp.mpr
  simpa only [one_div,mul_comm,div_eq_mul_inv,one_mul] using G.coordinate_log_bounded hG hb j
lemma card_line_mul (G : Grid) (j : Fin G.b) :
    2^G.bits j*Fintype.card (G.Line j)=G.size := by
  have he := Fintype.card_congr (Equiv.piSplitAt j (fun t => Cube (G.bits t)))
  simpa only [Fintype.card_prod,G.card_slot,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] using he.symm
lemma card_line_le (G : Grid) (j : Fin G.b) : Fintype.card (G.Line j) ≤ G.size := by
  rw [← G.card_line_mul j]
  exact Nat.le_mul_of_pos_left _ (by positivity)
end CoordinateSweeps.Grid

namespace CoordinateSweeps.SparseScalar
lemma sparse_fraction {s u : ℝ} (hs : 1 < s) (hu : 0 ≤ u)
    (huS : u ≤ s^(1-theta)) (h2 : 2 ≤ s^(theta/4)) :
    2*u/(s*s^(-xi)) ≤ s^(-theta/2) := by
  have hs0 : 0 < s := by linarith
  apply (div_le_iff₀ (mul_pos hs0 (Real.rpow_pos_of_pos hs0 _))).mpr
  calc
    2*u ≤ s^(theta/4)*s^(1-theta) := mul_le_mul h2 huS hu (Real.rpow_nonneg hs0.le _)
    _ ≤ s^(-theta/2)*(s*s^(-xi)) := by
      rw [rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0]
      conv_rhs => arg 2; arg 1; rw [← Real.exp_log hs0]
      rw [← Real.exp_add,← Real.exp_add,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hl := Real.log_pos hs
      norm_num [theta,xi]
      linarith
lemma sparse_line_mass {s m : ℝ} (hs : 1 < s)
    (hm : s^(1/(2*(B0:ℝ))) ≤ m) : s^(1/(4*(B0:ℝ))) ≤ m*s^(-xi) := by
  have hs0 : 0 < s := by linarith
  calc
    _ ≤ s^(1/(2*(B0:ℝ)))*s^(-xi) := by
      rw [rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0,← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hl := Real.log_pos hs
      norm_num [B0,xi]
      linarith
    _ ≤ _ := mul_le_mul_of_nonneg_right hm (Real.rpow_nonneg hs0.le _)

lemma logarithm_count {s : ℝ} (hs : 2 ≤ s) {n : ℕ} (hn : (n : ℝ) ≤ s) :
    Real.log (n+1 : ℕ) ≤ 2*Real.log s := by
  have hs0 : 0 < s := by linarith
  have h1 : (n+1 : ℝ) ≤ 2*s := by linarith
  have hh := Real.log_le_log (by positivity : 0 < (n+1 : ℝ)) h1
  rw [Real.log_mul (by norm_num) hs0.ne'] at hh
  have h2 := Real.log_le_log (by norm_num : (0:ℝ)<2) hs
  push_cast
  linarith
lemma occupancy_count {s m : ℝ} {n k : ℕ} (hs : 2 ≤ s) (hn : (n : ℝ) ≤ s)
    (hm : s^(1/(2*(B0:ℝ))) ≤ m)
    (habs : 4/s^(1/(4*(B0:ℝ))) ≤ theta/(64*B0)) :
    ((n+1:ℕ):ℝ)^⌊2*k/(m*s^(-xi))⌋₊ ≤ Real.exp (theta*k*Real.log s/(32*B0)) := by
  have hs1 : 1 < s := by linarith
  have hs0 : 0 < s := by linarith
  have hmη := sparse_line_mass hs1 hm
  have hp : 0 < s^(1/(4*(B0:ℝ))) := Real.rpow_pos_of_pos hs0 _
  have hmpos := hp.trans_le hmη
  have hfloor := Nat.floor_le (by positivity : 0 ≤ 2*(k:ℝ)/(m*s^(-xi)))
  have hlog := logarithm_count hs hn
  have hlog0 : 0 ≤ Real.log (n+1:ℕ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  have hL := Real.log_pos hs1
  have hh := mul_le_mul hfloor hlog hlog0 (by positivity : 0 ≤ 2*(k:ℝ)/(m*s^(-xi)))
  have hdiv := (div_le_div_of_nonneg_left (by norm_num : (0:ℝ)≤4) hp hmη).trans habs
  have hh' := mul_le_mul_of_nonneg_right hdiv (mul_nonneg (Nat.cast_nonneg k) hL.le)
  have heq : (2*(k:ℝ)/(m*s^(-xi)))*(2*Real.log s)=(4/(m*s^(-xi)))*((k:ℝ)*Real.log s) := by ring
  rw [heq] at hh
  rw [show ((n+1:ℕ):ℝ)^⌊2*k/(m*s^(-xi))⌋₊=
      Real.exp ((⌊2*k/(m*s^(-xi))⌋₊:ℝ)*Real.log (n+1:ℕ)) by
    rw [Real.exp_nat_mul,Real.exp_log (by positivity)]]
  apply Real.exp_le_exp.mpr
  have ht : 0 ≤ theta := by norm_num [theta]
  have hkL := mul_nonneg (Nat.cast_nonneg k) hL.le
  push_cast at hh
  norm_num [B0,theta] at hh' ⊢
  nlinarith
end CoordinateSweeps.SparseScalar

namespace CoordinateSweeps.SparseScalar
lemma sparse_vertex_fraction {s t B : ℝ} (hs : 1 < s) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (htS : t ≤ s^(1-theta)) (hBS : B ≤ s^(theta/2)) :
    t*B/s ≤ s^(-theta/2) := by
  have hs0 : 0 < s := by linarith
  apply (div_le_iff₀ hs0).mpr
  calc
    _ ≤ s^(1-theta)*s^(theta/2) := mul_le_mul htS hBS hB (ht.trans htS)
    _ = s^(-theta/2)*s := by
      rw [rpow_exp s _ hs0,rpow_exp s _ hs0,rpow_exp s _ hs0]
      conv_rhs => arg 2; rw [← Real.exp_log hs0]
      rw [← Real.exp_add,← Real.exp_add]
      congr 1
      ring
end CoordinateSweeps.SparseScalar
namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k : ℕ} (H : G.Holes h)
/- Uniform bounded-axis source04:eq12, with all sparse geometry now discharged. -/
theorem sparse_fewGood_bound (hf : H.Feasible) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hs : (2:ℝ) ≤ G.size)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (h2 : 2 ≤ (G.size:ℝ)^(theta/4)) (hB : (B0+1:ℝ) ≤ (G.size:ℝ)^(theta/2))
    (hcount : 4/(G.size:ℝ)^(1/(4*(B0:ℝ))) ≤ theta/(64*B0))
    (habs : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log G.size) :
    Coverage.probability G.endpointWeight (fun v : Fin k → G.Slot × G.Slot =>
      ((H.goodSet (fun i => (v i).1) (fun i => (v i).2) ((G.size:ℝ)^(-xi))).card:ℝ)<k/2) ≤
      (G.size:ℝ)^(-xi*k) := by
  have hs1 : (1:ℝ)<G.size := by linarith
  have hs0 : (0:ℝ)<G.size := by linarith
  have hη : 0 < (G.size:ℝ)^(-xi) := Real.rpow_pos_of_pos hs0 _
  have hn : (G.size:ℝ)^(-theta/2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hs1.le (by norm_num [theta])
  have hhS : (h:ℝ) ≤ (G.size:ℝ)^(1-theta) := by push_cast at hsp; linarith
  have hkS : (k:ℝ) ≤ (G.size:ℝ)^(1-theta) := by push_cast at hsp; linarith
  have hhr := sparse_fraction hs1 (Nat.cast_nonneg h) hhS h2
  have hkr := sparse_fraction hs1 (Nat.cast_nonneg k) hkS h2
  have hvr : ((k+h:ℕ):ℝ)*G.vertexSharingRate ≤ (G.size:ℝ)^(-theta/2) := by
    have hbs : ((G.b+1:ℕ):ℝ)≤(B0+1:ℝ) := by exact_mod_cast Nat.add_le_add_right hb 1
    have hvS : ((k+h:ℕ):ℝ)≤(G.size:ℝ)^(1-theta) := by simpa only [Nat.add_comm k h] using hsp
    have hh := sparse_vertex_fraction hs1 (Nat.cast_nonneg (k+h)) (Nat.cast_nonneg (G.b+1)) hvS (hbs.trans hB)
    simpa only [Grid.vertexSharingRate,mul_div_assoc] using hh
  have hle := H.probability_fewGood_le hf hη (hhr.trans hn) (hkr.trans hn) (hvr.trans hn)
  apply hle.trans
  apply fewGood_bound G.positive hb hk hs1
    (mul_nonneg (Nat.cast_nonneg _) G.vertexSharingRate_nonneg) (by positivity) (by positivity)
    hvr hhr hkr _ (fun _ => by positivity) _ habs
  intro j
  apply occupancy_count hs (by exact_mod_cast G.card_line_le j)
    (by simpa only [Nat.cast_pow,Nat.cast_ofNat] using G.coordinate_size_bounded hG hb j) hcount
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k : ℕ}
lemma uniformSparsePrefactor_le (hb : G.b ≤ B0) (hh : (h:ℝ) ≤ K0*k) :
    uniformSparsePrefactor G h k ≤ Real.exp (uniformRate*k) := by
  have hK : 0 ≤ K0 := by norm_num [K0]
  have he : 1 ≤ Real.exp (2:ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
  have h1 : 0 ≤ Real.log (16*Real.exp 2) := Real.log_nonneg (by linarith)
  have h2 : 0 ≤ Real.log (1+16*Real.exp 2) := Real.log_nonneg (by linarith)
  have h3 : 0 ≤ Real.log (4:ℝ) := Real.log_nonneg (by norm_num)
  have hb' : (G.b:ℝ)≤B0 := by exact_mod_cast hb
  have hh' := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg G.b)
  have hB := mul_le_mul_of_nonneg_right hb'
    (show 0 ≤ K0+1+Real.log 4+Real.log (16*Real.exp 2)+Real.log (1+16*Real.exp 2) by positivity)
  have hBk := mul_le_mul_of_nonneg_right hB (Nat.cast_nonneg k)
  unfold uniformSparsePrefactor
  rw [pow_two_exp,show (16*Real.exp 2)^(G.b*k)=Real.exp ((G.b*k:ℕ)*Real.log (16*Real.exp 2)) by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)],
    show (1+16*Real.exp 2)^(G.b*k)=Real.exp ((G.b*k:ℕ)*Real.log (1+16*Real.exp 2)) by
      rw [Real.exp_nat_mul,Real.exp_log (by positivity)],
    ← Real.exp_add,← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  unfold uniformRate
  push_cast
  nlinarith

/- Quantitative uniform-law HS-square contraction with fixed slack for the
later finite real perturbation step. -/
theorem sparse_uniform_HS_bound (H : G.Holes h) (hf : H.Feasible) {r : ℕ} (hG : G.Allowed r)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hh : (h:ℝ) ≤ K0*k) (hs : (2:ℝ) ≤ G.size)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (h2 : 2 ≤ (G.size:ℝ)^(theta/4)) (hB : (B0+1:ℝ) ≤ (G.size:ℝ)^(theta/2))
    (hcount : 4/(G.size:ℝ)^(1/(4*(B0:ℝ))) ≤ theta/(64*B0))
    (habs : Real.log (1+2*(B0:ℝ))+Real.log 2 ≤ xi*Real.log G.size)
    (hη : (G.size:ℝ)^(-xi) ≤ 1/8)
    (hpref : uniformRate ≤ xi*Real.log G.size/16) (hlog2 : Real.log 2 ≤ xi*Real.log G.size/8) :
    H.placementHSsq (k := k) (fun _ => FiniteLaw.uniform _) ≤ (G.size:ℝ)^(-xi*k/4) := by
  have hs0 : (0:ℝ)<G.size := by linarith
  have hs1 : (1:ℝ)<G.size := by linarith
  have hL := Real.log_pos hs1
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  have hk0 : (0:ℝ)≤k := by positivity
  have hxi : 0 < xi := by norm_num [xi]
  have hhS := H.placementHSsq_uniform_le_fewGood (k := k) (Real.rpow_nonneg hs0.le _) hη
  have hfew := H.sparse_fewGood_bound hf hG hb hk hs hsp h2 hB hcount habs
  have hpref' := uniformSparsePrefactor_le (G := G) (k := k) hb hh
  have hprob : 0 ≤ Coverage.probability G.endpointWeight (fun v : Fin k → G.Slot × G.Slot =>
      ((H.goodSet (fun i => (v i).1) (fun i => (v i).2) ((G.size:ℝ)^(-xi))).card:ℝ)<k/2) :=
    by
      unfold Coverage.probability
      apply Finset.sum_nonneg
      intro v hv
      split_ifs
      · exact Coverage.productMass_nonneg _ G.endpointWeight_nonneg v
      · exact le_rfl
  have hp0 : 0 ≤ uniformSparsePrefactor G h k := by unfold uniformSparsePrefactor; positivity
  have hpp := pow_le_pow_left₀ hp0 hpref' 2
  apply hhS.trans ((mul_le_mul hpp (add_le_add (le_refl (((G.size:ℝ)^(-xi))^((k:ℝ)/2))) hfew)
    (add_nonneg (Real.rpow_nonneg (Real.rpow_nonneg hs0.le _) _) hprob)
    (sq_nonneg _)).trans ?_)
  rw [rpow_exp (G.size:ℝ) (-xi) hs0,exp_rpow,rpow_exp (G.size:ℝ) (-xi*k) hs0,
    ← Real.exp_nat_mul,rpow_exp (G.size:ℝ) (-xi*k/4) hs0]
  have heq : (-xi*Real.log G.size)*((k:ℝ)/2)=-xi*k*Real.log G.size/2 := by ring
  rw [heq]
  have hsmall : Real.exp (-xi*k*Real.log G.size) ≤ Real.exp (-xi*k*Real.log G.size/2) := by
    apply Real.exp_le_exp.mpr
    have hpos := mul_nonneg (mul_nonneg hxi.le hk0) hL.le
    linarith
  have hsumm : Real.exp (-xi*k*Real.log G.size/2)+Real.exp (-xi*k*Real.log G.size) ≤
      2*Real.exp (-xi*k*Real.log G.size/2) := by linarith
  apply (mul_le_mul_of_nonneg_left hsumm (Real.exp_pos _).le).trans
  rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)],
    ← Real.exp_add,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.exp_log (by norm_num : (0:ℝ)<2)]
  have h1 := mul_le_mul_of_nonneg_right hpref hk0
  have h2 := mul_le_mul_of_nonneg_right hlog2 hk0
  have h3 := mul_le_mul_of_nonneg_right hk' (Real.log_nonneg (by norm_num : (1:ℝ)≤2))
  push_cast
  nlinarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid
open SparseScalar
lemma b_le_log_size {G : Grid} {r : ℕ} (hG : G.Allowed r)
    (hrL : 1 ≤ (r:ℝ)*Real.log 2) : (G.b:ℝ) ≤ Real.log G.size := by
  exact (le_mul_of_one_le_right (Nat.cast_nonneg _) hrL).trans (G.log_size_lower hG)
lemma sparse_lineSharing (G : Grid) {r h k : ℕ} (hr : 1 ≤ r) (hG : G.Allowed r)
    (hb : B0 ≤ G.b) (hrL : 1 ≤ (r:ℝ)*Real.log 2)
    (hlog : Real.log G.size ≤ (G.size:ℝ)^(theta/4))
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta)) :
    ((k+h:ℕ):ℝ)*G.lineSharingRate ≤ (G.size:ℝ)^(-theta/2) := by
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hb' := (b_le_log_size hG hrL).trans hlog
  have hrate : G.lineSharingRate ≤ (G.b:ℝ)*(G.size:ℝ)^(theta/4)/(G.size:ℝ) := by
    unfold lineSharingRate
    rw [← Finset.sum_div]
    apply div_le_div_of_nonneg_right _ hs0.le
    calc
      _ ≤ ∑ _j : Fin G.b, (G.size:ℝ)^(theta/4) :=
        Finset.sum_le_sum (fun j _ => G.coordinate_size_many hr hG hb j)
      _ = _ := by simp
  have hp := mul_le_mul hsp hrate G.lineSharingRate_nonneg (Real.rpow_nonneg hs0.le _)
  have hb'' := mul_le_mul_of_nonneg_right hb' (Real.rpow_nonneg hs0.le (theta/4))
  have hb''' := div_le_div_of_nonneg_right hb'' hs0.le
  calc
    ((k+h:ℕ):ℝ)*G.lineSharingRate = ((h+k:ℕ):ℝ)*G.lineSharingRate := by rw [Nat.add_comm]
    _ ≤ (G.size:ℝ)^(1-theta)*((G.b:ℝ)*(G.size:ℝ)^(theta/4)/(G.size:ℝ)) := hp
    _ ≤ (G.size:ℝ)^(1-theta)*((G.size:ℝ)^(theta/4)*(G.size:ℝ)^(theta/4)/(G.size:ℝ)) :=
      mul_le_mul_of_nonneg_left hb''' (Real.rpow_nonneg hs0.le _)
    _ = (G.size:ℝ)^(-theta/2) := by
      rw [← Real.rpow_add hs0,div_eq_mul_inv,← Real.rpow_neg_one,← Real.rpow_add hs0,← Real.rpow_add hs0]
      congr 1
      ring
lemma sparse_many_absorb (G : Grid) {r : ℕ} (hG : G.Allowed r)
    (hrL : 3*Real.log 2+2*(K0+1+Real.log 4) ≤ theta*((r:ℝ)*Real.log 2)/8) :
    3*Real.log 2+2*(G.b:ℝ)*(K0+1+Real.log 4) ≤ theta*Real.log G.size/8 := by
  have hb : (1:ℝ)≤G.b := by exact_mod_cast G.positive
  have hb0 : (0:ℝ)≤G.b := by positivity
  have h1 := mul_le_mul_of_nonneg_left hrL hb0
  have h2 := mul_le_mul_of_nonneg_right hb (by positivity : 0 ≤ 3*Real.log 2)
  have h3 := mul_le_mul_of_nonneg_left (G.log_size_lower hG) (by norm_num [theta] : 0 ≤ theta/8)
  nlinarith
end CoordinateSweeps.Grid
namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k : ℕ}
/- Literal many-coordinate real-law HS-square bound, with all grid and
forest-counting conditions derived from source sparse size assumptions. -/
theorem sparse_many_HS_bound (H : G.Holes h) (hf : H.Feasible) {r : ℕ}
    (hr : 1 ≤ r) (hG : G.Allowed r) (hb : B0 ≤ G.b)
    (hrL : 1 ≤ (r:ℝ)*Real.log 2)
    (hrA : 3*Real.log 2+2*(K0+1+Real.log 4) ≤ theta*((r:ℝ)*Real.log 2)/8)
    (hh : (h:ℝ) ≤ K0*k)
    (hlog : Real.log G.size ≤ (G.size:ℝ)^(theta/4))
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g) :
    H.placementHSsq (k := k) (fun j => lineLaw (G.bits j) z hz hz') ≤
      (G.size:ℝ)^(-theta*k/8) := by
  have hL := G.log_size_pos_of_allowed hr hG
  have hs : (1:ℝ)<G.size := (Real.log_pos_iff (by exact_mod_cast G.size_pos.le)).mp hL
  have ht := G.sparse_lineSharing hr hG hb hrL hlog hsp
  have ht0 : 0 ≤ ((k+h:ℕ):ℝ)*G.lineSharingRate := mul_nonneg (Nat.cast_nonneg _) G.lineSharingRate_nonneg
  have hsmall : ((k+h:ℕ):ℝ)*G.lineSharingRate ≤ 1 := ht.trans
    (Real.rpow_le_one_of_one_le_of_nonpos hs.le (by norm_num [theta]))
  exact (H.placementHSsq_le hf hz hz' hlo hhi hsmall).trans
    (many_HS_bound _ _ _ _ k hs ht0 ht hh (Nat.cast_nonneg _) (G.sparse_many_absorb hG hrA))
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
variable {G : Grid} {h : ℕ}
lemma event_nonempty (H : G.Holes h) (hf : H.Feasible) : H.event.Nonempty := by
  obtain ⟨ω,hω⟩ := hf
  exact ⟨ω,by simpa [event] using hω⟩
lemma probability_eq_eventMass (H : G.Holes h) (z : ℝ) :
    H.probability z=∑ ω ∈ H.event, G.choiceWeight z ω := by
  exact (Finset.sum_subtype H.event (by simp [event]) (fun ω => G.choiceWeight z ω)).symm
lemma eventDistance_eq (H : G.Holes h) (z : ℝ) :
    G.eventDistance H.event z=
      ∑ ω : {ω : G.Choices // H.Compatible ω},
        |G.choiceWeight z ω.val/H.probability z-G.choiceWeight 0 ω.val/H.probability 0| := by
  simp only [Grid.eventDistance,← H.probability_eq_eventMass]
  exact Finset.sum_subtype H.event (by simp [event]) _
/- Uniform in every irreducible: real event-distance controls the conditional
operator difference. This avoids choosing a topology on equivalence classes
of irreducible models. -/
theorem conditionalAverage_difference_le (H : G.Holes h) (hf : H.Feasible)
    (z : ℝ) (ρ : UnitaryIrrep H.stabilizer) :
    ‖H.conditionalAverage hf z ρ-H.conditionalAverage hf 0 ρ‖ ≤ G.eventDistance H.event z := by
  let : NeZero ρ.dimension := ⟨ρ.positive.ne'⟩
  rw [H.conditionalAverage_eq_sum,H.conditionalAverage_eq_sum,← Finset.sum_sub_distrib,H.eventDistance_eq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro ω hω
  rw [← sub_smul,← Complex.ofReal_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _) (matrix_unitary_norm_le _ (ρ.unitary _))
theorem conditionalAverage_perturb_bound (H : G.Holes h) (hf : H.Feasible)
    (z : ℝ) (ρ : UnitaryIrrep H.stabilizer) :
    ‖H.conditionalAverage hf z ρ‖ ≤ ‖H.conditionalAverage hf 0 ρ‖+G.eventDistance H.event z := by
  have hh := H.conditionalAverage_difference_le hf z ρ
  have ht := norm_le_insert (H.conditionalAverage hf 0 ρ) (H.conditionalAverage hf z ρ)
  rw [norm_sub_rev] at ht
  linarith
end CoordinateSweeps.Grid.Holes

end
end
end
end
end
end
end
end
end
open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_BaseCase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
Work on the genuinely missing main statements of the pinned manuscript.
All definitions are finite and use the source's ordinary probability and trace
normalizations. No result of the manuscript is assumed.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

namespace CoordinateSweeps

lemma e0_pos : 0 < e0 := by norm_num [e0,a]
lemma c0_eq_e0 : c0=e0 := rfl

namespace Grid

lemma log_size_lower_one (G : Grid) {r : ℕ} (hG : G.Allowed r) :
    (r : ℝ)*Real.log 2 ≤ Real.log G.size := by
  apply le_trans _ (G.log_size_lower hG)
  have hb : (1 : ℝ) ≤ G.b := by exact_mod_cast G.positive
  exact le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))) hb

end Grid

/- Exactly the two largeness requirements stated at the start of06, converted
from log R to bit exponent r. Both constants remain the source constants. -/

lemma scale_coefficients {r : ℕ} (hr : ScaleLarge r) (G : Grid) (hG : G.Allowed r) :
    0 < Real.log G.size ∧ c G.size ≤ 2*c0 ∧ e0/2 ≤ e G.size ∧
    (G.b : ℝ) ≤ (e0/4)*Real.log G.size := by
  have he := e0_pos
  have hroot : (2/e0)^2 ≤ Real.log G.size := hr.2.1.trans (G.log_size_lower_one hG)
  have hlog : 0 < Real.log G.size := lt_of_lt_of_le (by positivity) hroot
  have hs : 2/e0 ≤ Real.sqrt (Real.log G.size) :=
    (Real.le_sqrt (by positivity) hlog.le).mpr hroot
  have hspos : 0 < Real.sqrt (Real.log G.size) := Real.sqrt_pos.mpr hlog
  have hi : 1/Real.sqrt (Real.log G.size) ≤ e0/2 := by
    apply (div_le_iff₀ hspos).mpr
    have hh := mul_le_mul_of_nonneg_left hs (show 0 ≤ e0/2 by positivity)
    field_simp at hh ⊢
    nlinarith
  have hb : (G.b : ℝ)*(4/e0) ≤ Real.log G.size :=
    (mul_le_mul_of_nonneg_left hr.2.2 (Nat.cast_nonneg _)).trans (G.log_size_lower hG)
  refine ⟨hlog,?_,?_,?_⟩
  · unfold c
    rw [c0_eq_e0]
    linarith
  · unfold e
    linarith
  · have hh := mul_le_mul_of_nonneg_left hb (show 0 ≤ e0/4 by positivity)
    field_simp at hh
    nlinarith

namespace Grid.Holes
variable {G : Grid} {h : ℕ} (H : G.Holes h)

/- Exact source nonnegative allowance, including h=0 and the empty type. -/
theorem allowance_lower {r : ℕ} (hr : ScaleLarge r) (hG : G.Allowed r) :
    (e0/4) * h * Real.log G.size ≤ e G.size * h * Real.log G.size - H.cost := by
  obtain ⟨hlog,hc,he,hb⟩ := scale_coefficients hr G hG
  have h1 := mul_le_mul_of_nonneg_right he (show 0 ≤ (h : ℝ)*Real.log G.size by positivity)
  have h2 := H.cost_le.trans (mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg h))
  nlinarith

lemma allowance_nonneg {r : ℕ} (hr : ScaleLarge r) (hG : G.Allowed r) :
    0 ≤ e G.size * h * Real.log G.size - H.cost :=
  (mul_nonneg (mul_nonneg (div_nonneg e0_pos.le (by norm_num)) (Nat.cast_nonneg _))
    (scale_coefficients hr G hG).1.le).trans (H.allowance_lower hr hG)

end Grid.Holes

end CoordinateSweeps

namespace CoordinateSweeps

lemma single_card_le_baseWidth {r d : ℕ} (hd : d ≤ 2*r) :
    (Fintype.card (Equiv.Perm (Cube d)) : ℝ) ≤ baseWidth r := by
  simp only [Fintype.card_perm,Cube,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  unfold baseWidth
  exact_mod_cast Nat.factorial_le (Nat.pow_le_pow_right (by norm_num : 0 < 2) hd)

end CoordinateSweeps

end

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Perturbation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
All definitions are finite and use the source's ordinary probability and trace
normalizations.
-/

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable

/-! The alternating placement kernel from 04-sparse:eq7.
Endpoints below need not be injections; invalid specifications have probability
zero automatically. On valid endpoint placements this is exactly the source Q. -/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/- Necessary shared-line polynomial expansion for the sparse conditional main.
A variable names a LINE, not a particle. The tensor moment functional is merely
linear, never multiplicative when two factors use the same line. -/
noncomputable section
open scoped BigOperators
open MvPolynomial

/- The analytic light-line obligation 04-sparse.tex (11).  The distribution
is exactly Mathlib's Gamma(shape, unit rate). -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal NNReal BigOperators

/- Finite subset rearrangements needed for the actual good/non-good path
alternation in source04:eq10. -/
noncomputable section
open scoped BigOperators

/- Required top-placement compression for the conditional main. The top space
is the annihilator of all functions depending on a proper set of coordinates.
This is the exact top level used in source04 around eq7. -/
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable

noncomputable section
universe u v
open scoped ComplexConjugate

noncomputable section
open scoped BigOperators

open scoped Matrix.Norms.L2Operator

noncomputable section
open scoped BigOperators
open Filter Asymptotics

namespace CoordinateSweeps.SparseScalar
lemma slack_le_gap {s : ℝ} (hs : 1 < s) {k : ℕ} (hk : 1 ≤ k) (hks : (k : ℝ) ≤ s) :
    slack s ≤ s^(-rho*k)-s^(-2*rho*k) := by
  have hs0 : 0 < s := by linarith
  have hr : 0 < rho := by norm_num [rho]
  have hk' : (1:ℝ)≤k := by exact_mod_cast hk
  rw [slack,ite_eq_left hs]
  have h1 : s^(-2*rho*s) ≤ s^(-2*rho*k) := Real.rpow_le_rpow_of_exponent_le hs.le (by nlinarith)
  have h2 : s^rho ≤ s^(rho*k) := Real.rpow_le_rpow_of_exponent_le hs.le (by nlinarith)
  have h3 : 0 ≤ s^rho-1 := sub_nonneg.mpr (Real.one_le_rpow hs.le hr.le)
  apply (mul_le_mul h1 (sub_le_sub_right h2 1) h3 (Real.rpow_nonneg hs0.le _)).trans_eq
  rw [mul_sub,mul_one,← Real.rpow_add hs0]
  congr 2
  ring
end CoordinateSweeps.SparseScalar
namespace CoordinateSweeps.Grid
open SparseScalar
lemma pow_r_le_size (G : Grid) {r : ℕ} (hG : G.Allowed r) : (2:ℝ)^r ≤ G.size := by
  have hb : (1:ℝ)≤G.b := by exact_mod_cast G.positive
  have hl := (le_mul_of_one_le_left (by positivity : 0≤(r:ℝ)*Real.log 2) hb).trans (G.log_size_lower hG)
  rw [pow_two_exp]
  exact (Real.exp_le_exp.mpr hl).trans_eq (Real.exp_log (by exact_mod_cast G.size_pos))
lemma sizeReady (G : Grid) {r : ℕ} (hr : ScaleReady r) (hG : G.Allowed r) : SizeReady G.size :=
  hr.size _ (G.pow_r_le_size hG)
lemma sparse_uniform_room (G : Grid) {r h k : ℕ} (hr : ScaleReady r) (hG : G.Allowed r)
    (hsp : ((h+k:ℕ):ℝ)≤(G.size:ℝ)^(1-theta)) (j : Fin G.b) :
    h+k+Fintype.card (G.Line j)<G.size := by
  have hs := G.sizeReady hr hG
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hhalf : 2*((h+k:ℕ):ℝ)≤G.size := by
    calc
      _ ≤ (G.size:ℝ)^(theta/4)*(G.size:ℝ)^(1-theta) :=
        mul_le_mul hs.powtwo hsp (Nat.cast_nonneg _) (Real.rpow_nonneg hs0.le _)
      _ = (G.size:ℝ)^(theta/4+(1-theta)) := (Real.rpow_add hs0 _ _).symm
      _ ≤ (G.size:ℝ)^1 := Real.rpow_le_rpow_of_exponent_le (by linarith [hs.two]) (by norm_num [theta])
      _ = _ := Real.rpow_one _
  have hm : 4≤2^G.bits j := (by norm_num : 4≤2^2).trans (Nat.pow_le_pow_right (by norm_num) (hr.two.trans (hG j).1))
  have hline := G.card_line_mul j
  have hquart : 4*Fintype.card (G.Line j)≤G.size := by nlinarith
  have hq : 4*(Fintype.card (G.Line j):ℝ)≤G.size := by exact_mod_cast hquart
  have hout : (((h+k+Fintype.card (G.Line j)):ℕ):ℝ)<G.size := by push_cast at hhalf ⊢; nlinarith
  exact_mod_cast hout
lemma sparse_many_room (G : Grid) {r h k : ℕ} (hr : ScaleReady r) (hG : G.Allowed r)
    (hb : B0≤G.b) (hsp : ((h+k:ℕ):ℝ)≤(G.size:ℝ)^(1-theta)) (j : Fin G.b) :
    h+k<Fintype.card (G.Line j) := by
  have hs := G.sizeReady hr hG
  have hs0 : (0:ℝ)<G.size := by exact_mod_cast G.size_pos
  have hp : ((h+k:ℕ):ℝ)*(2^G.bits j:ℝ)<G.size := by
    calc
      _ ≤ (G.size:ℝ)^(1-theta)*(G.size:ℝ)^(theta/4) :=
        mul_le_mul hsp (G.coordinate_size_many (by have hh := hr.two; omega) hG hb j) (by positivity) (Real.rpow_nonneg hs0.le _)
      _ = (G.size:ℝ)^(1-theta+theta/4) := (Real.rpow_add hs0 _ _).symm
      _ < (G.size:ℝ)^1 := Real.rpow_lt_rpow_of_exponent_lt (by linarith [hs.two]) (by norm_num [theta])
      _ = _ := Real.rpow_one _
  have hpN : (h+k)*(2^G.bits j)<G.size := by exact_mod_cast hp
  rw [← G.card_line_mul j,mul_comm (2^G.bits j)] at hpN
  exact (Nat.mul_lt_mul_right (by positivity)).mp hpN
end CoordinateSweeps.Grid

namespace CoordinateSweeps.Grid.Holes
open SparseScalar
variable {G : Grid} {h k r : ℕ} (H : G.Holes h)
lemma lineLaw_zero (d : ℕ) : lineLaw d 0 (by norm_num) (by norm_num) = FiniteLaw.uniform _ := by
  ext g
  simp [lineLaw, FiniteLaw.mix]
lemma sparse_uniform_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset (H.FreeAt 0), A.card < k → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm (H.FreeAt 0), (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0) :
    ‖H.conditionalAverage hf 0 (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-2*rho*k) := by
  have hs := G.sizeReady hr hG
  have hhS := H.sparse_uniform_HS_bound hf hG hb hk hh hs.two hsp hs.powtwo hs.powB hs.count
    hs.absorb hs.eta hs.prefactor hs.logtwo
  have hn := H.conditional_norm_le_placementHS hf (by norm_num : (0:ℝ)≤0) (by norm_num : (0:ℝ)≤1)
    ρ u hu x₀ hfixed hnof
  simp only [lineLaw_zero] at hn
  apply hn.trans ((Real.sqrt_le_sqrt hhS).trans_eq ?_)
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity : (0:ℝ)≤G.size)]
  congr 1
  norm_num [xi,rho]
  ring
lemma sparse_many_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : B0 ≤ G.b) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0)))
    (u : Fin ρ.dimension → ℂ) (hu : u ≠ 0) (x₀ : Fin k ↪ H.FreeAt 0)
    (hfixed : ∀ g : Equiv.Perm (H.FreeAt 0), (∀ i, g (x₀ i)=x₀ i) → ρ.asRepresentation g u=u)
    (hnof : ∀ A : Finset (H.FreeAt 0), A.card < k → ∀ v : Fin ρ.dimension → ℂ,
      (∀ g : Equiv.Perm (H.FreeAt 0), (∀ a ∈ A, g a=a) → ρ.asRepresentation g v=v) → v=0) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-rho*k) := by
  have hs := G.sizeReady hr hG
  have hhS := H.sparse_many_HS_bound hf (by have hh:=hr.two; omega) hG hb hr.logone hr.absorb hh hs.logpow hsp hz hz' hlo hhi
  apply (H.conditional_norm_le_placementHS hf hz hz' ρ u hu x₀ hfixed hnof).trans
    ((Real.sqrt_le_sqrt hhS).trans ?_)
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul (by positivity : (0:ℝ)≤G.size)]
  apply Real.rpow_le_rpow_of_exponent_le (by linarith [hs.two])
  have hk0 := (Nat.cast_nonneg k : (0:ℝ)≤k)
  norm_num [theta,rho]
  nlinarith
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.SparseDimension
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
lemma exists_level (ρ : UnitaryIrrep (Equiv.Perm Ω)) :
    ∃ k t : ℕ, k ≤ 2*t ∧ 2^t ≤ ρ.dimension ∧ ρ.dimension ≤ (Fintype.card Ω)^k ∧
      k ≤ Fintype.card Ω ∧ Nonempty (Level ρ k) := by
  obtain ⟨ε,k,t,A,u,hA,hk,ht,hd,hu,hf,hn⟩ := exists_minimal_fixed_vector ρ.asRepresentation
  have hcard : Fintype.card A=k := by simpa using hA
  let eA : A ≃ Fin k := Fintype.equivFinOfCardEq hcard
  let x : Fin k ↪ Ω := eA.symm.toEmbedding.trans (Function.Embedding.subtype (· ∈ A))
  refine ⟨k,t,hk,by simpa using ht,by simpa using hd,?_,⟨⟨ε,u,hu,x,?_,hn⟩⟩⟩
  · rw [← hA]
    exact Finset.card_le_univ A
  · intro g hg
    apply hf g
    intro a ha
    have hh := hg (eA ⟨a,ha⟩)
    simpa [x] using hh
omit [DecidableEq Ω] in
lemma level_log_bounds (ρ : UnitaryIrrep (Equiv.Perm Ω)) {s k t : ℕ}
    (hs : 0 < s) (hΩ : Fintype.card Ω ≤ s) (hk : k ≤ 2*t)
    (ht : 2^t ≤ ρ.dimension) (hd : ρ.dimension ≤ (Fintype.card Ω)^k) :
    Real.log ρ.dimension ≤ k*Real.log s ∧ (k:ℝ) ≤ 4*Real.log ρ.dimension := by
  have hD : (0:ℝ)<ρ.dimension := by exact_mod_cast ρ.positive
  have hs0 : (0:ℝ) < s := by exact_mod_cast hs
  constructor
  · have hh : (ρ.dimension:ℝ) ≤ (s:ℝ)^k := by exact_mod_cast hd.trans (Nat.pow_le_pow_left hΩ k)
    simpa only [Real.log_pow] using Real.log_le_log hD hh
  · have htt : (2:ℝ)^t ≤ ρ.dimension := by exact_mod_cast ht
    have hh := Real.log_le_log (by positivity : (0:ℝ)<(2:ℝ)^t) htt
    rw [Real.log_pow] at hh
    have hlog : (1/2:ℝ) ≤ Real.log 2 := by
      have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ)<2)
      norm_num at hh
      linarith
    have hk' : (k:ℝ) ≤ 2*t := by exact_mod_cast hk
    nlinarith [mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg t : (0:ℝ)≤t)]
end CoordinateSweeps.SparseDimension

namespace CoordinateSweeps.Grid.Holes
open SparseScalar SparseDimension
variable {G : Grid} {h k r : ℕ} (H : G.Holes h)
lemma level_uniform_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : G.b ≤ B0) (hk : 1 ≤ k) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (L : Level ρ k) :
    ‖H.conditionalAverage hf 0 (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-2*rho*k) := by
  cases he : L.flipped
  · apply H.sparse_uniform_norm hr hG hf hb hk hh hsp ρ L.vector L.nonzero L.placement
    · simpa [he] using L.fixed
    · simpa [he] using L.minimal
  · have hz := H.conditional_column_zero_uniform hf ρ L.vector L.nonzero L.placement
      (by simpa [he] using L.fixed) ⟨0,G.positive⟩
      (G.sparse_uniform_room hr hG hsp _)
    rw [hz,norm_zero]
    positivity
lemma level_many_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    (hb : B0 ≤ G.b) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ 1)
    (hlo : ∀ j g, (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw (G.bits j) z hz hz' g)
    (hhi : ∀ j g, lineLaw (G.bits j) z hz hz' g ≤ 2*FiniteLaw.uniform _ g)
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (L : Level ρ k) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-rho*k) := by
  cases he : L.flipped
  · apply H.sparse_many_norm hr hG hf hb hh hsp hz hz' hlo hhi ρ L.vector L.nonzero L.placement
    · simpa [he] using L.fixed
    · simpa [he] using L.minimal
  · have hz := H.conditional_column_zero_many hf hz hz' ρ L.vector L.nonzero L.placement
      (by simpa [he] using L.fixed) ⟨0,G.positive⟩
      (by have hh:=hr.two; have hg:=(hG ⟨0,G.positive⟩).1; omega)
      (G.sparse_many_room hr hG hb hsp _)
    rw [hz,norm_zero]
    positivity
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps
lemma baseZeta_le_inv_card {r d : ℕ} (hd : d ≤ 2*r) :
    baseZeta r ≤ (Fintype.card (Equiv.Perm (Cube d)) : ℝ)⁻¹ := by
  have hB := baseWidth_one_le r
  have hC := single_card_le_baseWidth hd
  have hC0 : (0:ℝ)<Fintype.card (Equiv.Perm (Cube d)) := by exact_mod_cast Fintype.card_pos
  unfold baseZeta
  rw [one_div]
  exact (inv_le_inv₀ (by positivity) hC0).mpr (by nlinarith)
lemma lineLaw_base_bounds {r d : ℕ} (hd : d ≤ 2*r) {z : ℝ} (hz : 0 ≤ z) (hz' : z ≤ baseZeta r)
    (g : Equiv.Perm (Cube d)) :
    (1/2:ℝ)*FiniteLaw.uniform _ g ≤ lineLaw d z hz (hz'.trans (baseZeta_le_half r) |>.trans (by norm_num)) g ∧
      lineLaw d z hz (hz'.trans (baseZeta_le_half r) |>.trans (by norm_num)) g ≤ 2*FiniteLaw.uniform _ g :=
  FiniteLaw.mix_uniform_between (binaryLaw d) hz (hz'.trans (baseZeta_le_half r))
    (hz'.trans (baseZeta_le_inv_card hd)) g

end CoordinateSweeps

namespace CoordinateSweeps.Grid.Holes
open SparseScalar SparseDimension
variable {G : Grid} {h k r : ℕ} (H : G.Holes h)
lemma level_sparse_norm (hr : ScaleReady r) (hG : G.Allowed r) (hf : H.Feasible)
    {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z ∈ Set.Icc 0 zStar)
    (hk : 1 ≤ k) (hks : k ≤ G.size) (hh : (h:ℝ) ≤ K0*k)
    (hsp : ((h+k:ℕ):ℝ) ≤ (G.size:ℝ)^(1-theta))
    (ρ : UnitaryIrrep (Equiv.Perm (H.FreeAt 0))) (L : Level ρ k) :
    ‖H.conditionalAverage hf z (ρ.pullback H.stabilizerFreeEquiv)‖ ≤ (G.size:ℝ)^(-rho*k) := by
  have hzB := hz.2.trans hζ.2.1
  have hz1 : z ≤ 1 := (hzB.trans (baseZeta_le_half r)).trans (by norm_num)
  by_cases hb : B0 ≤ G.b
  · apply H.level_many_norm hr hG hf hb hh hsp hz.1 hz1
    · exact fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).1
    · exact fun j g => (lineLaw_base_bounds (hG j).2 hz.1 hzB g).2
    · exact L
  · have hb' : G.b ≤ B0 := by omega
    have hU := H.level_uniform_norm hr hG hf hb' hk hh hsp ρ L
    have hP := H.conditionalAverage_perturb_bound hf z (ρ.pullback H.stabilizerFreeEquiv)
    have hdist := hζ.2.2 G hb' hG z hz H.event (H.event_nonempty hf)
    have hS := G.sizeReady hr hG
    have hgap := slack_le_gap (by linarith [hS.two] : (1:ℝ)<G.size) hk (by exact_mod_cast hks)
    linarith
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end
end
end
end

open scoped Matrix.Norms.L2Operator

end OAI
end

section
-- module Solutions.OAIQ56_CS.CoordinateSweeps_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Matrix.Norms.L2Operator
namespace CoordinateSweeps.Grid.Holes
open SparseScalar SparseDimension ScalarInduction
variable {G : Grid} {h r : ℕ} (H : G.Holes h)
lemma conditionalAverage_free_cancel (hf : H.Feasible) (z : ℝ) (σ : UnitaryIrrep H.stabilizer) :
    H.conditionalAverage hf z ((σ.pullback H.stabilizerFreeEquiv.symm).pullback H.stabilizerFreeEquiv)=
      H.conditionalAverage hf z σ := by
  rw [H.conditionalAverage_eq_sum,H.conditionalAverage_eq_sum]
  apply Finset.sum_congr rfl
  intro ω hω
  change (_:ℂ) • σ.matrix (H.stabilizerFreeEquiv.symm (H.stabilizerFreeEquiv (H.residual hf ω)))=_
  rw [MulEquiv.symm_apply_apply]
/-- Entire nonautomatic sparse-dimension branch of the conditional main,
with the actual stabilizer irrep, actual feasible paths and a common real z interval. -/
theorem conditional_sparse_main_oai (hr : ScaleLarge r) (hrS : ScaleReady r)
    (hG : G.Allowed r) (hS : MainSizeReady SparseScalar.q G.size)
    (hf : H.Feasible) {zStar : ℝ} (hζ : SparsePerturb r zStar) {z : ℝ} (hz : z∈Set.Icc 0 zStar)
    (σ : UnitaryIrrep H.stabilizer) (hσ : σ.dimension≠1)
    (ha : ¬ (1+c G.size)*Real.log σ.dimension ≤ e G.size*h*Real.log G.size-H.cost)
    (hF : Real.log σ.dimension < (G.size:ℝ)^(1-a/4)) :
    schattenMoment SparseScalar.q (H.conditionalAverage hf z σ) ≤
      Real.exp (-c G.size*Real.log σ.dimension+e G.size*h*Real.log G.size-H.cost) := by
  let ρ := σ.pullback H.stabilizerFreeEquiv.symm
  obtain ⟨k,t,hkt,ht,hD,hkM,⟨L⟩⟩ := exists_level ρ
  have hΩ : Fintype.card (H.FreeAt 0)≤G.size := by rw [H.card_freeAt]; exact Nat.sub_le _ _
  have hks := hkM.trans hΩ
  have hlogs := level_log_bounds ρ G.size_pos hΩ hkt ht hD
  change Real.log σ.dimension≤k*Real.log G.size ∧ (k:ℝ)≤4*Real.log σ.dimension at hlogs
  have hk : 1≤k := by
    by_contra hh
    have he : k=0 := by omega
    rw [he,pow_zero] at hD
    have hdim : σ.dimension=1 := by have hh0:=σ.positive; change σ.dimension≤1 at hD; omega
    exact hσ hdim
  have hL := (scale_coefficients hr G hG).1
  have hc := (scale_coefficients hr G hG).2.1
  have hc1 : c G.size≤1 := hc.trans (by norm_num [c0,a])
  have hF0 : 0≤Real.log σ.dimension := Real.log_nonneg (by exact_mod_cast σ.positive)
  have hallow := H.allowance_lower hr hG
  have hn := lt_of_not_ge ha
  have hhh : (h:ℝ)*Real.log G.size ≤ K0*Real.log σ.dimension := by
    have hm := mul_le_mul_of_nonneg_right hc1 hF0
    norm_num [e0,a,K0] at hallow ⊢
    nlinarith
  have hh : (h:ℝ)≤K0*k := by
    have hm := mul_le_mul_of_nonneg_left hlogs.1 (by norm_num [K0] : 0≤K0)
    exact (mul_le_mul_iff_right₀ hL).mp (by nlinarith)
  have hsp : ((h+k:ℕ):ℝ)≤(G.size:ℝ)^(1-theta) := by
    have hh0 := (Nat.cast_nonneg h : (0:ℝ)≤h)
    have hhle : (h:ℝ)≤K0*Real.log σ.dimension := by nlinarith [hS.one]
    have hsum : ((h+k:ℕ):ℝ)≤(100004:ℝ)*Real.log σ.dimension := by
      push_cast
      norm_num [K0] at hhle
      linarith [hlogs.2]
    apply hsum.trans
    apply (mul_le_mul_of_nonneg_left hF.le (by norm_num : (0:ℝ)≤100004)).trans
    simpa only [theta] using hS.sparse
  have hnorm := H.level_sparse_norm hrS hG hf hζ hz hk hks hh hsp ρ L
  rw [show ρ=σ.pullback H.stabilizerFreeEquiv.symm from rfl,H.conditionalAverage_free_cancel] at hnorm
  let : NeZero σ.dimension := ⟨σ.positive.ne'⟩
  have hp := pow_le_pow_left₀ (norm_nonneg (H.conditionalAverage hf z σ)) hnorm (2*SparseScalar.q)
  calc
    _ ≤ (σ.dimension:ℝ)*‖H.conditionalAverage hf z σ‖^(2*SparseScalar.q) := trace_moment_le _ _
    _ ≤ (σ.dimension:ℝ)*((G.size:ℝ)^(-rho*k))^(2*SparseScalar.q) :=
      mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = Real.exp (Real.log σ.dimension-4*k*Real.log G.size) := by
      rw [rpow_exp _ _ (by exact_mod_cast G.size_pos),←Real.exp_nat_mul]
      nth_rw 1 [←Real.exp_log (by exact_mod_cast σ.positive : (0:ℝ)<σ.dimension)]
      rw [←Real.exp_add]
      congr 1
      norm_num [SparseScalar.q,rho]
      ring
    _ ≤ Real.exp (-3*Real.log σ.dimension) := Real.exp_le_exp.mpr (by nlinarith [hlogs.1])
    _ ≤ _ := Real.exp_le_exp.mpr (by
      have hm := mul_le_mul_of_nonneg_right hc1 hF0
      have ha0 := H.allowance_nonneg hr hG
      linarith)
end CoordinateSweeps.Grid.Holes

end OAI
end

theorem solution : type_of% @OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main_oai := @OAI.CoordinateSweeps.Grid.Holes.conditional_sparse_main_oai
